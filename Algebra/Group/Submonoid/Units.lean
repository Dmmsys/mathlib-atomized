/-
Copyright (c) 2023 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Group.Submonoid.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!

# Submonoid of units

Given a submonoid `S` of a monoid `M`, we define the subgroup `S.units` as the units of `S` as a
subgroup of `Mˣ`. That is to say, `S.units` contains all members of `S` which have a
two-sided inverse within `S`, as terms of type `Mˣ`.

We also define, for subgroups `S` of `Mˣ`, `S.ofUnits`, which is `S` considered as a submonoid
of `M`. `Submonoid.units` and `Subgroup.ofUnits` form a Galois coinsertion.

We also make the equivalent additive definitions.

## Implementation details
There are a number of other constructions which are multiplicatively equivalent to `S.units` but
which have a different type.

| Definition | Type |
|----------------------|---------------|
| `S.units` | `Subgroup Mˣ` |
| `Sˣ` | `Type u` |
| `IsUnit.submonoid S` | `Submonoid S` |
| `S.units.ofUnits` | `Submonoid M` |

All of these are distinct from `S.leftInv`, which is the submonoid of `M` which contains
every member of `M` with a right inverse in `S`.
-/

@[expose] public section

variable {M : Type*} [Monoid M]

open Units

open scoped Pointwise in
/-- The units of `S`, packaged as a subgroup of `Mˣ`. -/
@[to_additive /-- The additive units of `S`, packaged as an additive subgroup of `AddUnits M`. -/]
/--
Definition of `Submonoid.units` / `Submonoid.units` 的定义

English:
definition Submonoid.units
  signature: (S : Submonoid M)
  body: S.comap (coeHom M) ⊓ (S.comap (coeHom M))⁻¹
  inv_mem' ha := ⟨ha.2, ha.1⟩

中文:
定义 子幺半群.units
  签名: (S : 子幺半群 M)
  定义体: S.comap (coeHom M) ⊓ (S.comap (coeHom M))⁻¹
  inv_mem' ha := ⟨ha.2, ha.1⟩

Depends on / 依赖: S.comap, coeHom
-/
def Submonoid.units (S : Submonoid M) : Subgroup Mˣ where
  toSubmonoid := S.comap (coeHom M) ⊓ (S.comap (coeHom M))⁻¹
  inv_mem' ha := ⟨ha.2, ha.1⟩

/-- A subgroup of units represented as a submonoid of `M`. -/
@[to_additive
/-- An additive subgroup of additive units represented as an additive submonoid of `M`. -/]
/--
Definition of `Subgroup.ofUnits` / `Subgroup.ofUnits` 的定义

English:
definition Subgroup.ofUnits
  signature: (S : Subgroup Mˣ)
  body: S.toSubmonoid.map (coeHom M)

@[to_additive]

中文:
定义 子群.ofUnits
  签名: (S : 子群 Mˣ)
  定义体: S.toSubmonoid.map (coeHom M)

@[to_additive]

Depends on / 依赖: S.toSubmonoid.map, coeHom, toSubmonoid
-/
def Subgroup.ofUnits (S : Subgroup Mˣ) : Submonoid M := S.toSubmonoid.map (coeHom M)

@[to_additive]
/--
lemma `Submonoid.units_mono` / 引理 `Submonoid.units_mono`

English:
lemma Submonoid.units_mono
  statement: Monotone (Submonoid.units (M := M))
  proof: fun _ _ hST _ ⟨h₁, h₂⟩ => ⟨hST h₁, hST h₂⟩

@[to_additive (attr := simp)]

中文:
引理 子幺半群.units_mono
  结论: 递增 (子幺半群.units (M := M))
  证明: fun _ _ hST _ ⟨h₁, h₂⟩ => ⟨hST h₁, hST h₂⟩

@[to_additive (attr := simp)]
-/
lemma Submonoid.units_mono : Monotone (Submonoid.units (M := M)) :=
  fun _ _ hST _ ⟨h₁, h₂⟩ => ⟨hST h₁, hST h₂⟩

@[to_additive (attr := simp)]
/--
lemma `Submonoid.ofUnits_units_le` / 引理 `Submonoid.ofUnits_units_le`

English:
lemma Submonoid.ofUnits_units_le
  given: (S : Submonoid M)
  statement: S.units.ofUnits <= S
  proof: fun _ ⟨_, hm, he⟩ => he ▸ hm.1

@[to_additive]

中文:
引理 子幺半群.ofUnits_units_le
  条件: (S : 子幺半群 M)
  结论: S.units.ofUnits <= S
  证明: fun _ ⟨_, hm, he⟩ => he ▸ hm.1

@[to_additive]
-/
lemma Submonoid.ofUnits_units_le (S : Submonoid M) : S.units.ofUnits <= S :=
  fun _ ⟨_, hm, he⟩ => he ▸ hm.1

@[to_additive]
/--
lemma `Subgroup.ofUnits_mono` / 引理 `Subgroup.ofUnits_mono`

English:
lemma Subgroup.ofUnits_mono
  statement: Monotone (Subgroup.ofUnits (M := M))
  proof: fun _ _ hST _ ⟨x, hx, hy⟩ => ⟨x, hST hx, hy⟩

@[to_additive (attr := simp)]

中文:
引理 子群.ofUnits_mono
  结论: 递增 (子群.ofUnits (M := M))
  证明: fun _ _ hST _ ⟨x, hx, hy⟩ => ⟨x, hST hx, hy⟩

@[to_additive (attr := simp)]
-/
lemma Subgroup.ofUnits_mono : Monotone (Subgroup.ofUnits (M := M)) :=
  fun _ _ hST _ ⟨x, hx, hy⟩ => ⟨x, hST hx, hy⟩

@[to_additive (attr := simp)]
/--
lemma `Subgroup.units_ofUnits_eq` / 引理 `Subgroup.units_ofUnits_eq`

English:
lemma Subgroup.units_ofUnits_eq
  given: (S : Subgroup Mˣ)
  statement: S.ofUnits.units = S
  proof: Subgroup.ext (fun _ =>
  ⟨fun ⟨⟨_, hm, he⟩, _⟩ => (Units.ext he) ▸ hm, fun hm => ⟨⟨_, hm, rfl⟩, _, S.inv_mem hm, rfl⟩⟩)

中文:
引理 子群.units_ofUnits_eq
  条件: (S : 子群 Mˣ)
  结论: S.ofUnits.units = S
  证明: Subgroup.ext (fun _ =>
  ⟨fun ⟨⟨_, hm, he⟩, _⟩ => (Units.ext he) ▸ hm, fun hm => ⟨⟨_, hm, rfl⟩, _, S.inv_mem hm, rfl⟩⟩)

Depends on / 依赖: S.inv_mem, Subgroup, Subgroup.ext, Units.ext, inv_mem
-/
lemma Subgroup.units_ofUnits_eq (S : Subgroup Mˣ) : S.ofUnits.units = S :=
  Subgroup.ext (fun _ =>
  ⟨fun ⟨⟨_, hm, he⟩, _⟩ => (Units.ext he) ▸ hm, fun hm => ⟨⟨_, hm, rfl⟩, _, S.inv_mem hm, rfl⟩⟩)

/-- A Galois coinsertion exists between the coercion from a subgroup of units to a submonoid and
the reduction from a submonoid to its unit group. -/
@[to_additive /-- A Galois coinsertion exists between the coercion from an additive subgroup of
additive units to an additive submonoid and the reduction from an additive submonoid to its unit
group. -/]
/--
Definition of `ofUnits_units_gci` / `ofUnits_units_gci` 的定义

English:
definition ofUnits_units_gci
  signature: : GaloisCoinsertion (Subgroup.ofUnits (M := M)) (Submonoid.units)
  body: GaloisCoinsertion.monotoneIntro Submonoid.units_mono Subgroup.ofUnits_mono
  Submonoid.ofUnits_units_le Subgroup.units_ofUnits_eq

@[to_additive]

中文:
定义 ofUnits_units_gci
  签名: : Galois余嵌入 (子群.ofUnits (M := M)) (子幺半群.units)
  定义体: GaloisCoinsertion.monotoneIntro Submonoid.units_mono Subgroup.ofUnits_mono
  Submonoid.ofUnits_units_le Subgroup.units_ofUnits_eq

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.units
-/
def ofUnits_units_gci : GaloisCoinsertion (Subgroup.ofUnits (M := M)) (Submonoid.units) :=
  GaloisCoinsertion.monotoneIntro Submonoid.units_mono Subgroup.ofUnits_mono
  Submonoid.ofUnits_units_le Subgroup.units_ofUnits_eq

@[to_additive]
/--
lemma `ofUnits_units_gc` / 引理 `ofUnits_units_gc`

English:
lemma ofUnits_units_gc
  statement: GaloisConnection (Subgroup.ofUnits (M := M)) (Submonoid.units)
  proof: ofUnits_units_gci.gc

@[to_additive]

中文:
引理 ofUnits_units_gc
  结论: GaloisConnection (子群.ofUnits (M := M)) (子幺半群.units)
  证明: ofUnits_units_gci.gc

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.units
-/
lemma ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits (M := M)) (Submonoid.units) :=
ofUnits_units_gci.gc

@[to_additive]
/--
lemma `ofUnits_le_iff_le_units` / 引理 `ofUnits_le_iff_le_units`

English:
lemma ofUnits_le_iff_le_units
  given: (S : Submonoid M) (H : Subgroup Mˣ)
  proof: ofUnits_units_gc _ _

@[to_additive]

中文:
引理 ofUnits_le_iff_le_units
  条件: (S : 子幺半群 M) (H : 子群 Mˣ)
  证明: ofUnits_units_gc _ _

@[to_additive]

Depends on / 依赖: ofUnits_units_gc
-/
lemma ofUnits_le_iff_le_units (S : Submonoid M) (H : Subgroup Mˣ) :
    H.ofUnits <= S ↔ H <= S.units := ofUnits_units_gc _ _

@[to_additive]
/--
theorem `IsUnit.coe` / 定理 `IsUnit.coe`

English:
theorem IsUnit.coe
  statement: {S : Type*} [SetLike S M] [SubmonoidClass S M] {N : S} {a : N}
  proof: ha.map (SubmonoidClass.subtype N)

中文:
定理 是单位.coe
  结论: {S : 类型} [集合状 S M] [子幺半群类 S M] {N : S} {a : N}
  证明: ha.map (SubmonoidClass.subtype N)

Depends on / 依赖: SubmonoidClass, SubmonoidClass.subtype, ha.map, subtype
-/
theorem IsUnit.coe {S : Type*} [SetLike S M] [SubmonoidClass S M] {N : S} {a : N}
    (ha : IsUnit a) : IsUnit (a : M) := ha.map (SubmonoidClass.subtype N)

namespace Submonoid

section Units

@[to_additive]
/--
lemma `mem_units_iff` / 引理 `mem_units_iff`

English:
lemma mem_units_iff
  given: (S : Submonoid M) (x : Mˣ)
  statement: x in S.units ↔
  proof: Iff.rfl

@[to_additive]

中文:
引理 mem_units_iff
  条件: (S : 子幺半群 M) (x : Mˣ)
  结论: x in S.units ↔
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
lemma mem_units_iff (S : Submonoid M) (x : Mˣ) : x in S.units ↔
    ((x : M) in S ∧ ((x⁻¹ : Mˣ) : M) in S) := Iff.rfl

@[to_additive]
/--
lemma `mem_units_of_val_mem_inv_val_mem` / 引理 `mem_units_of_val_mem_inv_val_mem`

English:
lemma mem_units_of_val_mem_inv_val_mem
  statement: (S : Submonoid M) {x : Mˣ} (h₁ : (x : M) in S)
  proof: ⟨h₁, h₂⟩

@[to_additive]

中文:
引理 mem_units_of_val_mem_inv_val_mem
  结论: (S : 子幺半群 M) {x : Mˣ} (h₁ : (x : M) in S)
  证明: ⟨h₁, h₂⟩

@[to_additive]
-/
lemma mem_units_of_val_mem_inv_val_mem (S : Submonoid M) {x : Mˣ} (h₁ : (x : M) in S)
    (h₂ : ((x⁻¹ : Mˣ) : M) in S) : x in S.units := ⟨h₁, h₂⟩

@[to_additive]
/--
lemma `val_mem_of_mem_units` / 引理 `val_mem_of_mem_units`

English:
lemma val_mem_of_mem_units
  given: (S : Submonoid M) {x : Mˣ} (h : x in S.units)
  statement: (x : M) in S
  proof: h.1

@[to_additive]

中文:
引理 val_mem_of_mem_units
  条件: (S : 子幺半群 M) {x : Mˣ} (h : x in S.units)
  结论: (x : M) in S
  证明: h.1

@[to_additive]
-/
lemma val_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x in S.units) : (x : M) in S := h.1

@[to_additive]
/--
lemma `inv_val_mem_of_mem_units` / 引理 `inv_val_mem_of_mem_units`

English:
lemma inv_val_mem_of_mem_units
  given: (S : Submonoid M) {x : Mˣ} (h : x in S.units)
  proof: h.2

@[to_additive]

中文:
引理 inv_val_mem_of_mem_units
  条件: (S : 子幺半群 M) {x : Mˣ} (h : x in S.units)
  证明: h.2

@[to_additive]
-/
lemma inv_val_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x in S.units) :
    ((x⁻¹ : Mˣ) : M) in S := h.2

@[to_additive]
/--
lemma `coe_inv_val_mul_coe_val` / 引理 `coe_inv_val_mul_coe_val`

English:
lemma coe_inv_val_mul_coe_val
  given: (S : Submonoid M) {x : Sˣ}
  proof: DFunLike.congr_arg S.subtype x.inv_mul

@[to_additive]

中文:
引理 coe_inv_val_mul_coe_val
  条件: (S : 子幺半群 M) {x : Sˣ}
  证明: DFunLike.congr_arg S.subtype x.inv_mul

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.congr_arg, S.subtype, congr_arg, inv_mul, subtype, x.inv_mul
-/
lemma coe_inv_val_mul_coe_val (S : Submonoid M) {x : Sˣ} :
    ((x⁻¹ : Sˣ) : M) * ((x : Sˣ) : M) = 1 := DFunLike.congr_arg S.subtype x.inv_mul

@[to_additive]
/--
lemma `coe_val_mul_coe_inv_val` / 引理 `coe_val_mul_coe_inv_val`

English:
lemma coe_val_mul_coe_inv_val
  given: (S : Submonoid M) {x : Sˣ}
  proof: DFunLike.congr_arg S.subtype x.mul_inv

@[to_additive]

中文:
引理 coe_val_mul_coe_inv_val
  条件: (S : 子幺半群 M) {x : Sˣ}
  证明: DFunLike.congr_arg S.subtype x.mul_inv

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.congr_arg, S.subtype, congr_arg, mul_inv, subtype, x.mul_inv
-/
lemma coe_val_mul_coe_inv_val (S : Submonoid M) {x : Sˣ} :
    ((x : Sˣ) : M) * ((x⁻¹ : Sˣ) : M) = 1 := DFunLike.congr_arg S.subtype x.mul_inv

@[to_additive]
/--
lemma `mk_inv_mul_mk_eq_one` / 引理 `mk_inv_mul_mk_eq_one`

English:
lemma mk_inv_mul_mk_eq_one
  given: (S : Submonoid M) {x : Mˣ} (h : x in S.units)
  proof: Subtype.ext x.inv_mul

@[to_additive]

中文:
引理 mk_inv_mul_mk_eq_one
  条件: (S : 子幺半群 M) {x : Mˣ} (h : x in S.units)
  证明: Subtype.ext x.inv_mul

@[to_additive]

Depends on / 依赖: Subtype, Subtype.ext, inv_mul, x.inv_mul
-/
lemma mk_inv_mul_mk_eq_one (S : Submonoid M) {x : Mˣ} (h : x in S.units) :
    (⟨_, h.2⟩ : S) * ⟨_, h.1⟩ = 1 := Subtype.ext x.inv_mul

@[to_additive]
/--
lemma `mk_mul_mk_inv_eq_one` / 引理 `mk_mul_mk_inv_eq_one`

English:
lemma mk_mul_mk_inv_eq_one
  given: (S : Submonoid M) {x : Mˣ} (h : x in S.units)
  proof: Subtype.ext x.mul_inv

@[to_additive]

中文:
引理 mk_mul_mk_inv_eq_one
  条件: (S : 子幺半群 M) {x : Mˣ} (h : x in S.units)
  证明: Subtype.ext x.mul_inv

@[to_additive]

Depends on / 依赖: Subtype, Subtype.ext, mul_inv, x.mul_inv
-/
lemma mk_mul_mk_inv_eq_one (S : Submonoid M) {x : Mˣ} (h : x in S.units) :
    (⟨_, h.1⟩ : S) * ⟨_, h.2⟩ = 1 := Subtype.ext x.mul_inv

@[to_additive]
/--
lemma `mul_mem_units` / 引理 `mul_mem_units`

English:
lemma mul_mem_units
  given: (S : Submonoid M) {x y : Mˣ} (h₁ : x in S.units) (h₂ : y in S.units)
  proof: mul_mem h₁ h₂

@[to_additive]

中文:
引理 mul_mem_units
  条件: (S : 子幺半群 M) {x y : Mˣ} (h₁ : x in S.units) (h₂ : y in S.units)
  证明: mul_mem h₁ h₂

@[to_additive]

Depends on / 依赖: mul_mem
-/
lemma mul_mem_units (S : Submonoid M) {x y : Mˣ} (h₁ : x in S.units) (h₂ : y in S.units) :
    x * y in S.units := mul_mem h₁ h₂

@[to_additive]
/--
lemma `inv_mem_units` / 引理 `inv_mem_units`

English:
lemma inv_mem_units
  given: (S : Submonoid M) {x : Mˣ} (h : x in S.units)
  statement: x⁻¹ in S.units
  proof: inv_mem h

@[to_additive]

中文:
引理 inv_mem_units
  条件: (S : 子幺半群 M) {x : Mˣ} (h : x in S.units)
  结论: x⁻¹ in S.units
  证明: inv_mem h

@[to_additive]

Depends on / 依赖: inv_mem
-/
lemma inv_mem_units (S : Submonoid M) {x : Mˣ} (h : x in S.units) : x⁻¹ in S.units := inv_mem h

@[to_additive]
/--
lemma `inv_mem_units_iff` / 引理 `inv_mem_units_iff`

English:
lemma inv_mem_units_iff
  given: (S : Submonoid M) {x : Mˣ}
  statement: x⁻¹ in S.units ↔ x in S.units
  proof: inv_mem_iff

中文:
引理 inv_mem_units_iff
  条件: (S : 子幺半群 M) {x : Mˣ}
  结论: x⁻¹ in S.units ↔ x in S.units
  证明: inv_mem_iff

Depends on / 依赖: inv_mem_iff
-/
lemma inv_mem_units_iff (S : Submonoid M) {x : Mˣ} : x⁻¹ in S.units ↔ x in S.units := inv_mem_iff

/-- The equivalence between the subgroup of units of `S` and the type of units of `S`. -/
@[to_additive (attr := simps)
/-- The equivalence between the additive subgroup of additive units of
`S` and the type of additive units of `S`. -/]
/--
Definition of `unitsEquivUnitsType` / `unitsEquivUnitsType` 的定义

English:
definition unitsEquivUnitsType
  signature: (S : Submonoid M)
  body: fun ⟨_, h⟩ => ⟨⟨_, h.1⟩, ⟨_, h.2⟩, S.mk_mul_mk_inv_eq_one h, S.mk_inv_mul_mk_eq_one h⟩
  invFun := fun x => ⟨⟨_, _, S.coe_val_mul_coe_inv_val, S.coe_inv_val_mul_coe_val⟩, ⟨x.1.2, x.2.2⟩⟩
  map_mul' := fun _ _ => rfl

@[to_additive (attr := simp)]

中文:
定义 unitsEquivUnitsType
  签名: (S : 子幺半群 M)
  定义体: fun ⟨_, h⟩ => ⟨⟨_, h.1⟩, ⟨_, h.2⟩, S.mk_mul_mk_inv_eq_one h, S.mk_inv_mul_mk_eq_one h⟩
  invFun := fun x => ⟨⟨_, _, S.coe_val_mul_coe_inv_val, S.coe_inv_val_mul_coe_val⟩, ⟨x.1.2, x.2.2⟩⟩
  map_mul' := fun _ _ => rfl

@[to_additive (attr := simp)]

Depends on / 依赖: S.mk_inv_mul_mk_eq_one, S.mk_mul_mk_inv_eq_one, mk_inv_mul_mk_eq_one, mk_mul_mk_inv_eq_one
-/
def unitsEquivUnitsType (S : Submonoid M) : S.units ≃* Sˣ where
  toFun := fun ⟨_, h⟩ => ⟨⟨_, h.1⟩, ⟨_, h.2⟩, S.mk_mul_mk_inv_eq_one h, S.mk_inv_mul_mk_eq_one h⟩
  invFun := fun x => ⟨⟨_, _, S.coe_val_mul_coe_inv_val, S.coe_inv_val_mul_coe_val⟩, ⟨x.1.2, x.2.2⟩⟩
  map_mul' := fun _ _ => rfl

@[to_additive (attr := simp)]
/--
lemma `units_top` / 引理 `units_top`

English:
lemma units_top
  statement: (⊤ : Submonoid M).units = ⊤
  proof: ofUnits_units_gc.u_top

@[to_additive]

中文:
引理 units_top
  结论: (⊤ : 子幺半群 M).units = ⊤
  证明: ofUnits_units_gc.u_top

@[to_additive]

Depends on / 依赖: ofUnits_units_gc, ofUnits_units_gc.u_top, u_top
-/
lemma units_top : (⊤ : Submonoid M).units = ⊤ := ofUnits_units_gc.u_top

@[to_additive]
/--
lemma `units_inf` / 引理 `units_inf`

English:
lemma units_inf
  given: (S T : Submonoid M)
  statement: (S ⊓ T).units = S.units ⊓ T.units
  proof: ofUnits_units_gc.u_inf

@[to_additive]

中文:
引理 units_inf
  条件: (S T : 子幺半群 M)
  结论: (S ⊓ T).units = S.units ⊓ T.units
  证明: ofUnits_units_gc.u_inf

@[to_additive]

Depends on / 依赖: ofUnits_units_gc, ofUnits_units_gc.u_inf, u_inf
-/
lemma units_inf (S T : Submonoid M) : (S ⊓ T).units = S.units ⊓ T.units :=
  ofUnits_units_gc.u_inf

@[to_additive]
/--
lemma `units_sInf` / 引理 `units_sInf`

English:
lemma units_sInf
  given: {s : Set (Submonoid M)}
  statement: (sInf s).units = ⨅ S in s, S.units
  proof: ofUnits_units_gc.u_sInf

@[to_additive]

中文:
引理 units_sInf
  条件: {s : 集合 (子幺半群 M)}
  结论: (sInf s).units = ⨅ S in s, S.units
  证明: ofUnits_units_gc.u_sInf

@[to_additive]

Depends on / 依赖: ofUnits_units_gc, ofUnits_units_gc.u_sInf, u_sInf
-/
lemma units_sInf {s : Set (Submonoid M)} : (sInf s).units = ⨅ S in s, S.units :=
  ofUnits_units_gc.u_sInf

@[to_additive]
/--
lemma `units_iInf` / 引理 `units_iInf`

English:
lemma units_iInf
  given: {ι : Sort*} (f : ι -> Submonoid M)
  statement: (iInf f).units = ⨅ (i : ι), (f i).units
  proof: ofUnits_units_gc.u_iInf

@[to_additive]

中文:
引理 units_iInf
  条件: {ι : 类型层*} (f : ι -> 子幺半群 M)
  结论: (iInf f).units = ⨅ (i : ι), (f i).units
  证明: ofUnits_units_gc.u_iInf

@[to_additive]

Depends on / 依赖: ofUnits_units_gc, ofUnits_units_gc.u_iInf, u_iInf
-/
lemma units_iInf {ι : Sort*} (f : ι -> Submonoid M) : (iInf f).units = ⨅ (i : ι), (f i).units :=
  ofUnits_units_gc.u_iInf

@[to_additive]
/--
lemma `units_iInf₂` / 引理 `units_iInf₂`

English:
lemma units_iInf₂
  given: {ι : Sort*} {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Submonoid M)
  proof: ofUnits_units_gc.u_iInf₂

@[to_additive (attr := simp)]

中文:
引理 units_iInf₂
  条件: {ι : 类型层*} {κ : ι -> 类型层*} (f : (i : ι) -> κ i -> 子幺半群 M)
  证明: ofUnits_units_gc.u_iInf₂

@[to_additive (attr := simp)]

Depends on / 依赖: ofUnits_units_gc, ofUnits_units_gc.u_iInf
-/
lemma units_iInf₂ {ι : Sort*} {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Submonoid M) :
    (⨅ (i : ι), ⨅ (j : κ i), f i j).units = ⨅ (i : ι), ⨅ (j : κ i), (f i j).units :=
  ofUnits_units_gc.u_iInf₂

@[to_additive (attr := simp)]
/--
lemma `units_bot` / 引理 `units_bot`

English:
lemma units_bot
  statement: (⊥ : Submonoid M).units = ⊥
  proof: ofUnits_units_gci.u_bot

@[to_additive]

中文:
引理 units_bot
  结论: (⊥ : 子幺半群 M).units = ⊥
  证明: ofUnits_units_gci.u_bot

@[to_additive]

Depends on / 依赖: ofUnits_units_gci, ofUnits_units_gci.u_bot, u_bot
-/
lemma units_bot : (⊥ : Submonoid M).units = ⊥ := ofUnits_units_gci.u_bot

@[to_additive]
/--
lemma `units_surjective` / 引理 `units_surjective`

English:
lemma units_surjective
  statement: Function.Surjective (units (M := M))
  proof: ofUnits_units_gci.u_surjective

@[to_additive]

中文:
引理 units_surjective
  结论: 函数.满射 (units (M := M))
  证明: ofUnits_units_gci.u_surjective

@[to_additive]
-/
lemma units_surjective : Function.Surjective (units (M := M)) :=
  ofUnits_units_gci.u_surjective

@[to_additive]
/--
lemma `units_left_inverse` / 引理 `units_left_inverse`

English:
lemma units_left_inverse
  proof: ofUnits_units_gci.leftInverse_u_l

中文:
引理 units_left_inverse
  证明: ofUnits_units_gci.leftInverse_u_l

Depends on / 依赖: Subgroup, Subgroup.ofUnits, ofUnits
-/
lemma units_left_inverse :
    Function.LeftInverse (units (M := M)) (Subgroup.ofUnits (M := M)) :=
  ofUnits_units_gci.leftInverse_u_l

/-- The equivalence between the subgroup of units of `S` and the submonoid of unit
elements of `S`. -/
@[to_additive /-- The equivalence between the additive subgroup of additive units of
`S` and the additive submonoid of additive unit elements of `S`. -/]
/--
Definition of `unitsEquivIsUnitSubmonoid` / `unitsEquivIsUnitSubmonoid` 的定义

English:
definition unitsEquivIsUnitSubmonoid
  signature: (S : Submonoid M)
  body: S.unitsEquivUnitsType.trans unitsTypeEquivIsUnitSubmonoid

中文:
定义 unitsEquivIsUnitSubmonoid
  签名: (S : 子幺半群 M)
  定义体: S.unitsEquivUnitsType.trans unitsTypeEquivIsUnitSubmonoid

Depends on / 依赖: S.unitsEquivUnitsType.trans, unitsEquivUnitsType, unitsTypeEquivIsUnitSubmonoid
-/
noncomputable def unitsEquivIsUnitSubmonoid (S : Submonoid M) : S.units ≃* IsUnit.submonoid S :=
S.unitsEquivUnitsType.trans unitsTypeEquivIsUnitSubmonoid

end Units

/--
Instance `instSubsingletonUnits` / 实例 `instSubsingletonUnits`

English:
instance instSubsingletonUnits
  signature: [Subsingleton Mˣ] {S : Submonoid M}
  body: .units_of_isUnit fun _a ha => Subtype.ext (ha.map S.subtype).eq_one

中文:
实例 instSubsingletonUnits
  签名: [子单例 Mˣ] {S : 子幺半群 M}
  定义体: .units_of_isUnit fun _a ha => Subtype.ext (ha.map S.subtype).eq_one

Depends on / 依赖: S.subtype, Subtype, Subtype.ext, eq_one, ha.map, subtype, units_of_isUnit
-/
instance instSubsingletonUnits [Subsingleton Mˣ] {S : Submonoid M} : Subsingleton Sˣ :=
  .units_of_isUnit fun _a ha => Subtype.ext (ha.map S.subtype).eq_one

end Submonoid

namespace Subgroup

@[to_additive]
/--
lemma `mem_ofUnits_iff` / 引理 `mem_ofUnits_iff`

English:
lemma mem_ofUnits_iff
  given: (S : Subgroup Mˣ) (x : M)
  statement: x in S.ofUnits ↔ exists y in S, y = x
  proof: Iff.rfl

@[to_additive]

中文:
引理 mem_ofUnits_iff
  条件: (S : 子群 Mˣ) (x : M)
  结论: x in S.ofUnits ↔ 存在 y in S, y = x
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
lemma mem_ofUnits_iff (S : Subgroup Mˣ) (x : M) : x in S.ofUnits ↔ exists y in S, y = x := Iff.rfl

@[to_additive]
/--
lemma `mem_ofUnits` / 引理 `mem_ofUnits`

English:
lemma mem_ofUnits
  given: (S : Subgroup Mˣ) {x : M} {y : Mˣ} (h₁ : y in S) (h₂ : y = x)
  statement: x in S.ofUnits
  proof: ⟨_, h₁, h₂⟩

@[to_additive]

中文:
引理 mem_ofUnits
  条件: (S : 子群 Mˣ) {x : M} {y : Mˣ} (h₁ : y in S) (h₂ : y = x)
  结论: x in S.ofUnits
  证明: ⟨_, h₁, h₂⟩

@[to_additive]
-/
lemma mem_ofUnits (S : Subgroup Mˣ) {x : M} {y : Mˣ} (h₁ : y in S) (h₂ : y = x) : x in S.ofUnits :=
  ⟨_, h₁, h₂⟩

@[to_additive]
/--
lemma `exists_mem_ofUnits_val_eq` / 引理 `exists_mem_ofUnits_val_eq`

English:
lemma exists_mem_ofUnits_val_eq
  given: (S : Subgroup Mˣ) {x : M} (h : x in S.ofUnits)
  proof: h

@[to_additive]

中文:
引理 存在_mem_ofUnits_val_eq
  条件: (S : 子群 Mˣ) {x : M} (h : x in S.ofUnits)
  证明: h

@[to_additive]
-/
lemma exists_mem_ofUnits_val_eq (S : Subgroup Mˣ) {x : M} (h : x in S.ofUnits) :
    exists y in S, y = x := h

@[to_additive]
/--
lemma `mem_of_mem_val_ofUnits` / 引理 `mem_of_mem_val_ofUnits`

English:
lemma mem_of_mem_val_ofUnits
  given: (S : Subgroup Mˣ) {y : Mˣ} (hy : (y : M) in S.ofUnits)
  statement: y in S
  proof: match hy with
  | ⟨_, hm, he⟩ => (Units.ext he) ▸ hm

@[to_additive]

中文:
引理 mem_of_mem_val_ofUnits
  条件: (S : 子群 Mˣ) {y : Mˣ} (hy : (y : M) in S.ofUnits)
  结论: y in S
  证明: match hy with
  | ⟨_, hm, he⟩ => (Units.ext he) ▸ hm

@[to_additive]

Depends on / 依赖: Units.ext
-/
lemma mem_of_mem_val_ofUnits (S : Subgroup Mˣ) {y : Mˣ} (hy : (y : M) in S.ofUnits) : y in S :=
  match hy with
  | ⟨_, hm, he⟩ => (Units.ext he) ▸ hm

@[to_additive]
/--
lemma `isUnit_of_mem_ofUnits` / 引理 `isUnit_of_mem_ofUnits`

English:
lemma isUnit_of_mem_ofUnits
  given: (S : Subgroup Mˣ) {x : M} (hx : x in S.ofUnits)
  statement: IsUnit x
  proof: match hx with
  | ⟨_, _, h⟩ => ⟨_, h⟩

中文:
引理 isUnit_of_mem_ofUnits
  条件: (S : 子群 Mˣ) {x : M} (hx : x in S.ofUnits)
  结论: 是单位 x
  证明: match hx with
  | ⟨_, _, h⟩ => ⟨_, h⟩
-/
lemma isUnit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (hx : x in S.ofUnits) : IsUnit x :=
  match hx with
  | ⟨_, _, h⟩ => ⟨_, h⟩

/-- Given some `x : M` which is a member of the submonoid of unit elements corresponding to a
subgroup of units, produce a unit of `M` whose coercion is equal to `x`. -/
@[to_additive /-- Given some `x : M` which is a member of the additive submonoid of additive unit
elements corresponding to a subgroup of units, produce a unit of `M` whose coercion is equal to
`x`. -/]
/--
Definition of `unit_of_mem_ofUnits` / `unit_of_mem_ofUnits` 的定义

English:
definition unit_of_mem_ofUnits
  signature: (S : Subgroup Mˣ) {x : M} (h : x in S.ofUnits)
  body: (Classical.choose h).copy x (Classical.choose_spec h).2.symm _ rfl

@[to_additive]

中文:
定义 unit_of_mem_ofUnits
  签名: (S : 子群 Mˣ) {x : M} (h : x in S.ofUnits)
  定义体: (Classical.choose h).copy x (Classical.choose_spec h).2.symm _ rfl

@[to_additive]

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, choose_spec
-/
noncomputable def unit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (h : x in S.ofUnits) : Mˣ :=
  (Classical.choose h).copy x (Classical.choose_spec h).2.symm _ rfl

@[to_additive]
/--
lemma `unit_of_mem_ofUnits_spec_eq_of_val_mem` / 引理 `unit_of_mem_ofUnits_spec_eq_of_val_mem`

English:
lemma unit_of_mem_ofUnits_spec_eq_of_val_mem
  given: (S : Subgroup Mˣ) {x : Mˣ} (h : (x : M) in S.ofUnits)
  proof: Units.ext rfl

@[to_additive]

中文:
引理 unit_of_mem_ofUnits_spec_eq_of_val_mem
  条件: (S : 子群 Mˣ) {x : Mˣ} (h : (x : M) in S.ofUnits)
  证明: Units.ext rfl

@[to_additive]

Depends on / 依赖: Units.ext
-/
lemma unit_of_mem_ofUnits_spec_eq_of_val_mem (S : Subgroup Mˣ) {x : Mˣ} (h : (x : M) in S.ofUnits) :
    S.unit_of_mem_ofUnits h = x := Units.ext rfl

@[to_additive]
/--
lemma `unit_of_mem_ofUnits_spec_val_eq_of_mem` / 引理 `unit_of_mem_ofUnits_spec_val_eq_of_mem`

English:
lemma unit_of_mem_ofUnits_spec_val_eq_of_mem
  given: (S : Subgroup Mˣ) {x : M} (h : x in S.ofUnits)
  proof: rfl

@[to_additive]

中文:
引理 unit_of_mem_ofUnits_spec_val_eq_of_mem
  条件: (S : 子群 Mˣ) {x : M} (h : x in S.ofUnits)
  证明: rfl

@[to_additive]
-/
lemma unit_of_mem_ofUnits_spec_val_eq_of_mem (S : Subgroup Mˣ) {x : M} (h : x in S.ofUnits) :
    S.unit_of_mem_ofUnits h = x := rfl

@[to_additive]
/--
lemma `unit_of_mem_ofUnits_spec_mem` / 引理 `unit_of_mem_ofUnits_spec_mem`

English:
lemma unit_of_mem_ofUnits_spec_mem
  given: (S : Subgroup Mˣ) {x : M} {h : x in S.ofUnits}
  proof: S.mem_of_mem_val_ofUnits h

@[to_additive]

中文:
引理 unit_of_mem_ofUnits_spec_mem
  条件: (S : 子群 Mˣ) {x : M} {h : x in S.ofUnits}
  证明: S.mem_of_mem_val_ofUnits h

@[to_additive]

Depends on / 依赖: S.mem_of_mem_val_ofUnits, mem_of_mem_val_ofUnits
-/
lemma unit_of_mem_ofUnits_spec_mem (S : Subgroup Mˣ) {x : M} {h : x in S.ofUnits} :
    S.unit_of_mem_ofUnits h in S := S.mem_of_mem_val_ofUnits h

@[to_additive]
/--
lemma `unit_eq_unit_of_mem_ofUnits` / 引理 `unit_eq_unit_of_mem_ofUnits`

English:
lemma unit_eq_unit_of_mem_ofUnits
  statement: (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x)
  proof: Units.ext rfl

@[to_additive]

中文:
引理 unit_eq_unit_of_mem_ofUnits
  结论: (S : 子群 Mˣ) {x : M} (h₁ : 是单位 x)
  证明: Units.ext rfl

@[to_additive]

Depends on / 依赖: Units.ext
-/
lemma unit_eq_unit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x)
    (h₂ : x in S.ofUnits) : h₁.unit = S.unit_of_mem_ofUnits h₂ := Units.ext rfl

@[to_additive]
/--
lemma `unit_mem_of_mem_ofUnits` / 引理 `unit_mem_of_mem_ofUnits`

English:
lemma unit_mem_of_mem_ofUnits
  statement: (S : Subgroup Mˣ) {x : M} {h₁ : IsUnit x}
  proof: S.unit_eq_unit_of_mem_ofUnits h₁ h₂ ▸ (S.unit_of_mem_ofUnits_spec_mem)

@[to_additive]

中文:
引理 unit_mem_of_mem_ofUnits
  结论: (S : 子群 Mˣ) {x : M} {h₁ : 是单位 x}
  证明: S.unit_eq_unit_of_mem_ofUnits h₁ h₂ ▸ (S.unit_of_mem_ofUnits_spec_mem)

@[to_additive]

Depends on / 依赖: S.unit_eq_unit_of_mem_ofUnits, S.unit_of_mem_ofUnits_spec_mem, unit_eq_unit_of_mem_ofUnits, unit_of_mem_ofUnits_spec_mem
-/
lemma unit_mem_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} {h₁ : IsUnit x}
    (h₂ : x in S.ofUnits) : h₁.unit in S :=
  S.unit_eq_unit_of_mem_ofUnits h₁ h₂ ▸ (S.unit_of_mem_ofUnits_spec_mem)

@[to_additive]
/--
lemma `mem_ofUnits_of_isUnit_of_unit_mem` / 引理 `mem_ofUnits_of_isUnit_of_unit_mem`

English:
lemma mem_ofUnits_of_isUnit_of_unit_mem
  statement: (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x)
  proof: S.mem_ofUnits h₂ h₁.unit_spec

@[to_additive]

中文:
引理 mem_ofUnits_of_isUnit_of_unit_mem
  结论: (S : 子群 Mˣ) {x : M} (h₁ : 是单位 x)
  证明: S.mem_ofUnits h₂ h₁.unit_spec

@[to_additive]

Depends on / 依赖: S.mem_ofUnits, mem_ofUnits, unit_spec
-/
lemma mem_ofUnits_of_isUnit_of_unit_mem (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x)
    (h₂ : h₁.unit in S) : x in S.ofUnits := S.mem_ofUnits h₂ h₁.unit_spec

@[to_additive]
/--
lemma `mem_ofUnits_iff_exists_isUnit` / 引理 `mem_ofUnits_iff_exists_isUnit`

English:
lemma mem_ofUnits_iff_exists_isUnit
  given: (S : Subgroup Mˣ) (x : M)
  proof: ⟨fun h => ⟨S.isUnit_of_mem_ofUnits h, S.unit_mem_of_mem_ofUnits h⟩,
  fun ⟨hm, he⟩ => S.mem_ofUnits_of_isUnit_of_unit_mem hm he⟩

中文:
引理 mem_ofUnits_iff_存在_isUnit
  条件: (S : 子群 Mˣ) (x : M)
  证明: ⟨fun h => ⟨S.isUnit_of_mem_ofUnits h, S.unit_mem_of_mem_ofUnits h⟩,
  fun ⟨hm, he⟩ => S.mem_ofUnits_of_isUnit_of_unit_mem hm he⟩

Depends on / 依赖: S.isUnit_of_mem_ofUnits, S.mem_ofUnits_of_isUnit_of_unit_mem, S.unit_mem_of_mem_ofUnits, isUnit_of_mem_ofUnits, mem_ofUnits_of_isUnit_of_unit_mem, unit_mem_of_mem_ofUnits
-/
lemma mem_ofUnits_iff_exists_isUnit (S : Subgroup Mˣ) (x : M) :
    x in S.ofUnits ↔ exists h : IsUnit x, h.unit in S :=
  ⟨fun h => ⟨S.isUnit_of_mem_ofUnits h, S.unit_mem_of_mem_ofUnits h⟩,
  fun ⟨hm, he⟩ => S.mem_ofUnits_of_isUnit_of_unit_mem hm he⟩

/-- The equivalence between the coercion of a subgroup `S` of `Mˣ` to a submonoid of `M` and
the subgroup itself as a type. -/
@[to_additive /-- The equivalence between the coercion of an additive subgroup `S` of
`Mˣ` to an additive submonoid of `M` and the additive subgroup itself as a type. -/]
/--
Definition of `ofUnitsEquivType` / `ofUnitsEquivType` 的定义

English:
definition ofUnitsEquivType
  signature: (S : Subgroup Mˣ)
  body: fun x => ⟨S.unit_of_mem_ofUnits x.2, S.unit_of_mem_ofUnits_spec_mem⟩
  invFun := fun x => ⟨x.1, ⟨x.1, x.2, rfl⟩⟩
  map_mul' := fun _ _ => Subtype.ext (Units.ext rfl)

@[to_additive (attr := simp)]

中文:
定义 ofUnitsEquivType
  签名: (S : 子群 Mˣ)
  定义体: fun x => ⟨S.unit_of_mem_ofUnits x.2, S.unit_of_mem_ofUnits_spec_mem⟩
  invFun := fun x => ⟨x.1, ⟨x.1, x.2, rfl⟩⟩
  map_mul' := fun _ _ => Subtype.ext (Units.ext rfl)

@[to_additive (attr := simp)]

Depends on / 依赖: S.unit_of_mem_ofUnits, S.unit_of_mem_ofUnits_spec_mem, unit_of_mem_ofUnits, unit_of_mem_ofUnits_spec_mem
-/
noncomputable def ofUnitsEquivType (S : Subgroup Mˣ) : S.ofUnits ≃* S where
  toFun := fun x => ⟨S.unit_of_mem_ofUnits x.2, S.unit_of_mem_ofUnits_spec_mem⟩
  invFun := fun x => ⟨x.1, ⟨x.1, x.2, rfl⟩⟩
  map_mul' := fun _ _ => Subtype.ext (Units.ext rfl)

@[to_additive (attr := simp)]
/--
lemma `ofUnits_bot` / 引理 `ofUnits_bot`

English:
lemma ofUnits_bot
  statement: (⊥ : Subgroup Mˣ).ofUnits = ⊥
  proof: ofUnits_units_gc.l_bot

@[to_additive]

中文:
引理 ofUnits_bot
  结论: (⊥ : 子群 Mˣ).ofUnits = ⊥
  证明: ofUnits_units_gc.l_bot

@[to_additive]

Depends on / 依赖: l_bot, ofUnits_units_gc, ofUnits_units_gc.l_bot
-/
lemma ofUnits_bot : (⊥ : Subgroup Mˣ).ofUnits = ⊥ := ofUnits_units_gc.l_bot

@[to_additive]
/--
lemma `ofUnits_inf` / 引理 `ofUnits_inf`

English:
lemma ofUnits_inf
  given: (S T : Subgroup Mˣ)
  statement: (S ⊔ T).ofUnits = S.ofUnits ⊔ T.ofUnits
  proof: ofUnits_units_gc.l_sup

@[to_additive]

中文:
引理 ofUnits_inf
  条件: (S T : 子群 Mˣ)
  结论: (S ⊔ T).ofUnits = S.ofUnits ⊔ T.ofUnits
  证明: ofUnits_units_gc.l_sup

@[to_additive]

Depends on / 依赖: l_sup, ofUnits_units_gc, ofUnits_units_gc.l_sup
-/
lemma ofUnits_inf (S T : Subgroup Mˣ) : (S ⊔ T).ofUnits = S.ofUnits ⊔ T.ofUnits :=
ofUnits_units_gc.l_sup

@[to_additive]
/--
lemma `ofUnits_sSup` / 引理 `ofUnits_sSup`

English:
lemma ofUnits_sSup
  given: (s : Set (Subgroup Mˣ))
  statement: (sSup s).ofUnits = ⨆ S in s, S.ofUnits
  proof: ofUnits_units_gc.l_sSup

@[to_additive]

中文:
引理 ofUnits_sSup
  条件: (s : 集合 (子群 Mˣ))
  结论: (sSup s).ofUnits = ⨆ S in s, S.ofUnits
  证明: ofUnits_units_gc.l_sSup

@[to_additive]

Depends on / 依赖: l_sSup, ofUnits_units_gc, ofUnits_units_gc.l_sSup
-/
lemma ofUnits_sSup (s : Set (Subgroup Mˣ)) : (sSup s).ofUnits = ⨆ S in s, S.ofUnits :=
ofUnits_units_gc.l_sSup

@[to_additive]
/--
lemma `ofUnits_iSup` / 引理 `ofUnits_iSup`

English:
lemma ofUnits_iSup
  given: {ι : Sort*} {f : ι -> Subgroup Mˣ}
  proof: ofUnits_units_gc.l_iSup

@[to_additive]

中文:
引理 ofUnits_iSup
  条件: {ι : 类型层*} {f : ι -> 子群 Mˣ}
  证明: ofUnits_units_gc.l_iSup

@[to_additive]

Depends on / 依赖: l_iSup, ofUnits_units_gc, ofUnits_units_gc.l_iSup
-/
lemma ofUnits_iSup {ι : Sort*} {f : ι -> Subgroup Mˣ} :
    (iSup f).ofUnits = ⨆ (i : ι), (f i).ofUnits := ofUnits_units_gc.l_iSup

@[to_additive]
/--
lemma `ofUnits_iSup₂` / 引理 `ofUnits_iSup₂`

English:
lemma ofUnits_iSup₂
  given: {ι : Sort*} {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Subgroup Mˣ)
  proof: ofUnits_units_gc.l_iSup₂

@[to_additive]

中文:
引理 ofUnits_iSup₂
  条件: {ι : 类型层*} {κ : ι -> 类型层*} (f : (i : ι) -> κ i -> 子群 Mˣ)
  证明: ofUnits_units_gc.l_iSup₂

@[to_additive]

Depends on / 依赖: ofUnits_units_gc, ofUnits_units_gc.l_iSup
-/
lemma ofUnits_iSup₂ {ι : Sort*} {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Subgroup Mˣ) :
    (⨆ (i : ι), ⨆ (j : κ i), f i j).ofUnits = ⨆ (i : ι), ⨆ (j : κ i), (f i j).ofUnits :=
  ofUnits_units_gc.l_iSup₂

@[to_additive]
/--
lemma `ofUnits_injective` / 引理 `ofUnits_injective`

English:
lemma ofUnits_injective
  statement: Function.Injective (ofUnits (M := M))
  proof: ofUnits_units_gci.l_injective

@[to_additive (attr := simp)]

中文:
引理 ofUnits_injective
  结论: 函数.单射 (ofUnits (M := M))
  证明: ofUnits_units_gci.l_injective

@[to_additive (attr := simp)]
-/
lemma ofUnits_injective : Function.Injective (ofUnits (M := M)) :=
  ofUnits_units_gci.l_injective

@[to_additive (attr := simp)]
/--
lemma `ofUnits_sup_units` / 引理 `ofUnits_sup_units`

English:
lemma ofUnits_sup_units
  given: (S T : Subgroup Mˣ)
  statement: (S.ofUnits ⊔ T.ofUnits).units = S ⊔ T
  proof: ofUnits_units_gci.u_sup_l _ _

@[to_additive (attr := simp)]

中文:
引理 ofUnits_sup_units
  条件: (S T : 子群 Mˣ)
  结论: (S.ofUnits ⊔ T.ofUnits).units = S ⊔ T
  证明: ofUnits_units_gci.u_sup_l _ _

@[to_additive (attr := simp)]

Depends on / 依赖: ofUnits_units_gci, ofUnits_units_gci.u_sup_l, u_sup_l
-/
lemma ofUnits_sup_units (S T : Subgroup Mˣ) : (S.ofUnits ⊔ T.ofUnits).units = S ⊔ T :=
  ofUnits_units_gci.u_sup_l _ _

@[to_additive (attr := simp)]
/--
lemma `ofUnits_inf_units` / 引理 `ofUnits_inf_units`

English:
lemma ofUnits_inf_units
  given: (S T : Subgroup Mˣ)
  statement: (S.ofUnits ⊓ T.ofUnits).units = S ⊓ T
  proof: ofUnits_units_gci.u_inf_l _ _

@[to_additive]

中文:
引理 ofUnits_inf_units
  条件: (S T : 子群 Mˣ)
  结论: (S.ofUnits ⊓ T.ofUnits).units = S ⊓ T
  证明: ofUnits_units_gci.u_inf_l _ _

@[to_additive]

Depends on / 依赖: ofUnits_units_gci, ofUnits_units_gci.u_inf_l, u_inf_l
-/
lemma ofUnits_inf_units (S T : Subgroup Mˣ) : (S.ofUnits ⊓ T.ofUnits).units = S ⊓ T :=
  ofUnits_units_gci.u_inf_l _ _

@[to_additive]
/--
lemma `ofUnits_right_inverse` / 引理 `ofUnits_right_inverse`

English:
lemma ofUnits_right_inverse
  proof: ofUnits_units_gci.leftInverse_u_l

@[to_additive]

中文:
引理 ofUnits_right_inverse
  证明: ofUnits_units_gci.leftInverse_u_l

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.units
-/
lemma ofUnits_right_inverse :
    Function.RightInverse (ofUnits (M := M)) (Submonoid.units (M := M)) :=
  ofUnits_units_gci.leftInverse_u_l

@[to_additive]
/--
lemma `ofUnits_strictMono` / 引理 `ofUnits_strictMono`

English:
lemma ofUnits_strictMono
  statement: StrictMono (ofUnits (M := M))
  proof: ofUnits_units_gci.strictMono_l

中文:
引理 ofUnits_strictMono
  结论: 严格递增 (ofUnits (M := M))
  证明: ofUnits_units_gci.strictMono_l

Depends on / 依赖: ofUnits_units_gci, ofUnits_units_gci.strictMono_l, strictMono_l
-/
lemma ofUnits_strictMono : StrictMono (ofUnits (M := M)) := ofUnits_units_gci.strictMono_l

/--
lemma `ofUnits_le_ofUnits_iff` / 引理 `ofUnits_le_ofUnits_iff`

English:
lemma ofUnits_le_ofUnits_iff
  given: {S T : Subgroup Mˣ}
  statement: S.ofUnits <= T.ofUnits ↔ S <= T
  proof: ofUnits_units_gci.l_le_l_iff

中文:
引理 ofUnits_le_ofUnits_iff
  条件: {S T : 子群 Mˣ}
  结论: S.ofUnits <= T.ofUnits ↔ S <= T
  证明: ofUnits_units_gci.l_le_l_iff

Depends on / 依赖: l_le_l_iff, ofUnits_units_gci, ofUnits_units_gci.l_le_l_iff
-/
lemma ofUnits_le_ofUnits_iff {S T : Subgroup Mˣ} : S.ofUnits <= T.ofUnits ↔ S <= T :=
  ofUnits_units_gci.l_le_l_iff

/-- The equivalence between the top subgroup of `Mˣ` coerced to a submonoid `M` and the
units of `M`. -/
@[to_additive /-- The equivalence between the additive subgroup of additive units of
`S` and the additive submonoid of additive unit elements of `S`. -/]
/--
Definition of `ofUnitsTopEquiv` / `ofUnitsTopEquiv` 的定义

English:
definition ofUnitsTopEquiv
  signature: : (⊤ : Subgroup Mˣ).ofUnits ≃* Mˣ
  body: (⊤ : Subgroup Mˣ).ofUnitsEquivType.trans topEquiv

中文:
定义 ofUnitsTopEquiv
  签名: : (⊤ : 子群 Mˣ).ofUnits ≃* Mˣ
  定义体: (⊤ : Subgroup Mˣ).ofUnitsEquivType.trans topEquiv

Depends on / 依赖: Subgroup, ofUnitsEquivType, ofUnitsEquivType.trans, topEquiv
-/
noncomputable def ofUnitsTopEquiv : (⊤ : Subgroup Mˣ).ofUnits ≃* Mˣ :=
  (⊤ : Subgroup Mˣ).ofUnitsEquivType.trans topEquiv

variable {G : Type*} [Group G]

@[to_additive]
/--
lemma `mem_units_iff_val_mem` / 引理 `mem_units_iff_val_mem`

English:
lemma mem_units_iff_val_mem
  given: (H : Subgroup G) (x : Gˣ)
  statement: x in H.units ↔ (x : G) in H
  proof: by
  simp_rw [Submonoid.mem_units_iff, mem_toSubmonoid, val_inv_eq_inv_val, inv_mem_iff, and_self]

@[to_additive]

中文:
引理 mem_units_iff_val_mem
  条件: (H : 子群 G) (x : Gˣ)
  结论: x in H.units ↔ (x : G) in H
  证明: by
  simp_rw [Submonoid.mem_units_iff, mem_toSubmonoid, val_inv_eq_inv_val, inv_mem_iff, and_self]

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.mem_units_iff, and_self, inv_mem_iff, mem_toSubmonoid, mem_units_iff, simp_rw, val_inv_eq_inv_val
-/
lemma mem_units_iff_val_mem (H : Subgroup G) (x : Gˣ) : x in H.units ↔ (x : G) in H := by
  simp_rw [Submonoid.mem_units_iff, mem_toSubmonoid, val_inv_eq_inv_val, inv_mem_iff, and_self]

@[to_additive]
/--
lemma `mem_ofUnits_iff_toUnits_mem` / 引理 `mem_ofUnits_iff_toUnits_mem`

English:
lemma mem_ofUnits_iff_toUnits_mem
  given: (H : Subgroup Gˣ) (x : G)
  statement: x in H.ofUnits ↔ (toUnits x) in H
  proof: by
  simp_rw [mem_ofUnits_iff, toUnits.surjective.exists, val_toUnits_apply, exists_eq_right]

@[to_additive (attr := simp)]

中文:
引理 mem_ofUnits_iff_toUnits_mem
  条件: (H : 子群 Gˣ) (x : G)
  结论: x in H.ofUnits ↔ (toUnits x) in H
  证明: by
  simp_rw [mem_ofUnits_iff, toUnits.surjective.exists, val_toUnits_apply, exists_eq_right]

@[to_additive (attr := simp)]

Depends on / 依赖: exists_eq_right, mem_ofUnits_iff, simp_rw, surjective, toUnits, toUnits.surjective.exists, val_toUnits_apply
-/
lemma mem_ofUnits_iff_toUnits_mem (H : Subgroup Gˣ) (x : G) : x in H.ofUnits ↔ (toUnits x) in H := by
  simp_rw [mem_ofUnits_iff, toUnits.surjective.exists, val_toUnits_apply, exists_eq_right]

@[to_additive (attr := simp)]
/--
lemma `mem_iff_toUnits_mem_units` / 引理 `mem_iff_toUnits_mem_units`

English:
lemma mem_iff_toUnits_mem_units
  given: (H : Subgroup G) (x : G)
  statement: toUnits x in H.units ↔ x in H
  proof: by
  simp_rw [mem_units_iff_val_mem, val_toUnits_apply]

@[to_additive (attr := simp)]

中文:
引理 mem_iff_toUnits_mem_units
  条件: (H : 子群 G) (x : G)
  结论: toUnits x in H.units ↔ x in H
  证明: by
  simp_rw [mem_units_iff_val_mem, val_toUnits_apply]

@[to_additive (attr := simp)]

Depends on / 依赖: mem_units_iff_val_mem, simp_rw, val_toUnits_apply
-/
lemma mem_iff_toUnits_mem_units (H : Subgroup G) (x : G) : toUnits x in H.units ↔ x in H := by
  simp_rw [mem_units_iff_val_mem, val_toUnits_apply]

@[to_additive (attr := simp)]
/--
lemma `val_mem_ofUnits_iff_mem` / 引理 `val_mem_ofUnits_iff_mem`

English:
lemma val_mem_ofUnits_iff_mem
  given: (H : Subgroup Gˣ) (x : Gˣ)
  statement: (x : G) in H.ofUnits ↔ x in H
  proof: by
  simp_rw [mem_ofUnits_iff_toUnits_mem, toUnits_val_apply]

中文:
引理 val_mem_ofUnits_iff_mem
  条件: (H : 子群 Gˣ) (x : Gˣ)
  结论: (x : G) in H.ofUnits ↔ x in H
  证明: by
  simp_rw [mem_ofUnits_iff_toUnits_mem, toUnits_val_apply]

Depends on / 依赖: mem_ofUnits_iff_toUnits_mem, simp_rw, toUnits_val_apply
-/
lemma val_mem_ofUnits_iff_mem (H : Subgroup Gˣ) (x : Gˣ) : (x : G) in H.ofUnits ↔ x in H := by
  simp_rw [mem_ofUnits_iff_toUnits_mem, toUnits_val_apply]

/-- The equivalence between the greatest subgroup of units contained within `T` and `T` itself. -/
@[to_additive /-- The equivalence between the greatest subgroup of additive units
contained within `T` and `T` itself. -/]
/--
Definition of `unitsEquivSelf` / `unitsEquivSelf` 的定义

English:
definition unitsEquivSelf
  signature: (H : Subgroup G)
  body: H.unitsEquivUnitsType.trans (toUnits (G := H)).symm

中文:
定义 unitsEquivSelf
  签名: (H : 子群 G)
  定义体: H.unitsEquivUnitsType.trans (toUnits (G := H)).symm

Depends on / 依赖: H.unitsEquivUnitsType.trans, toUnits, unitsEquivUnitsType
-/
def unitsEquivSelf (H : Subgroup G) : H.units ≃* H :=
  H.unitsEquivUnitsType.trans (toUnits (G := H)).symm

end Subgroup

@[to_additive]
/--
theorem `MonoidHom.isUnit_eqLocusM_mk_iff` / 定理 `MonoidHom.isUnit_eqLocusM_mk_iff`

English:
theorem MonoidHom.isUnit_eqLocusM_mk_iff
  statement: {N : Type*} [Monoid N] (f g : M ->* N) {r : M}
  proof: by
  refine ⟨fun h => h.map (SubmonoidClass.subtype _), fun h => ?_⟩
  obtain ⟨s, hs⟩ := isUnit_iff_exists.mp h
  suffices exists a, r * a = 1 ∧ f a = g a ∧ a * r = 1 by
    simpa [isUnit_iff_exists, ← Subtype.val_inj]
  refine ⟨s, hs.left, ?_, hs.right⟩
  rw [← mul_one (f s)]; rw [← map_one g]; rw 

中文:
定理 幺半群态射.isUnit_eqLocusM_mk_iff
  结论: {N : 类型} [幺半群 N] (f g : M ->* N) {r : M}
  证明: by
  refine ⟨fun h => h.map (SubmonoidClass.subtype _), fun h => ?_⟩
  obtain ⟨s, hs⟩ := isUnit_iff_exists.mp h
  suffices exists a, r * a = 1 ∧ f a = g a ∧ a * r = 1 by
    simpa [isUnit_iff_exists, ← Subtype.val_inj]
  refine ⟨s, hs.left, ?_, hs.right⟩
  rw [← mul_one (f s)]; rw [← map_one g]; rw 

Depends on / 依赖: SubmonoidClass, SubmonoidClass.subtype, Subtype, Subtype.val_inj, h.map, hs.left, hs.right, isUnit_iff_exists, isUnit_iff_exists.mp, map_mul, map_one, mul_assoc, mul_one, one_mul, subtype, val_inj
-/
theorem MonoidHom.isUnit_eqLocusM_mk_iff {N : Type*} [Monoid N] (f g : M ->* N) {r : M}
    (hr : f r = g r) : IsUnit (⟨r, hr⟩ : f.eqLocusM g) ↔ IsUnit r := by
  refine ⟨fun h => h.map (SubmonoidClass.subtype _), fun h => ?_⟩
  obtain ⟨s, hs⟩ := isUnit_iff_exists.mp h
  suffices exists a, r * a = 1 ∧ f a = g a ∧ a * r = 1 by
    simpa [isUnit_iff_exists, ← Subtype.val_inj]
  refine ⟨s, hs.left, ?_, hs.right⟩
  rw [← mul_one (f s)]; rw [← map_one g]; rw [← hs.left]; rw [map_mul]; rw [← mul_assoc]; rw [← hr]; rw [← map_mul]; rw [hs.right]; rw [map_one]; rw [one_mul]

instance {N : Type*} [Monoid N] (f g : M ->* N) : IsLocalHom (f.eqLocusM g).subtype where
.2 map_nonunit r := f.isUnit_eqLocusM_mk_iff g r.prop
