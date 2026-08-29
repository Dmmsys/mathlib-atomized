/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.GroupTheory.Subsemigroup.Center

/-!
# Centers of monoids

## Main definitions

* `Submonoid.center`: the center of a monoid
* `AddSubmonoid.center`: the center of an additive monoid

We provide `Subgroup.center`, `AddSubgroup.center`, `Subsemiring.center`, and `Subring.center` in
other files.
-/

@[expose] public section

-- Guard against import creep
assert_not_exists Finset

namespace Submonoid

section MulOneClass

variable (M : Type*) [MulOneClass M]

/-- The center of a multiplication with unit `M` is the set of elements that commute with everything
in `M` -/
@[to_additive
/-- The center of an addition with zero `M` is the set of elements that commute with everything in
`M` -/]
/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: : Submonoid M where
  body: Set.center M
  one_mem' := Set.one_mem_center
  mul_mem' := Set.mul_mem_center

@[to_additive]

中文:
定义 center
  签名: : Submonoid M where
  定义体: Set.center M
  one_mem' := Set.one_mem_center
  mul_mem' := Set.mul_mem_center

@[to_additive]

Depends on / 依赖: Set.center, center
-/
def center : Submonoid M where
  carrier := Set.center M
  one_mem' := Set.one_mem_center
  mul_mem' := Set.mul_mem_center

@[to_additive]
/--
theorem `coe_center` / 定理 `coe_center`

English:
theorem coe_center
  statement: ↑(center M) = Set.center M
  proof: rfl

@[to_additive (attr := simp) AddSubmonoid.center_toAddSubsemigroup]

中文:
定理 coe_center
  结论: ↑(center M) = Set.center M
  证明: rfl

@[to_additive (attr := simp) AddSubmonoid.center_toAddSubsemigroup]
-/
theorem coe_center : ↑(center M) = Set.center M :=
  rfl

@[to_additive (attr := simp) AddSubmonoid.center_toAddSubsemigroup]
/--
theorem `center_toSubsemigroup` / 定理 `center_toSubsemigroup`

English:
theorem center_toSubsemigroup
  statement: (center M).toSubsemigroup = Subsemigroup.center M
  proof: rfl

中文:
定理 center_toSubsemigroup
  结论: (center M).toSubsemigroup = Subsemigroup.center M
  证明: rfl
-/
theorem center_toSubsemigroup : (center M).toSubsemigroup = Subsemigroup.center M :=
  rfl

instance {M α : Type*} [Monoid M] [MulAction M α] :
    SMulCommClass ↥(Submonoid.center M) M α where
  smul_comm c r v := by
    have := Semigroup.mem_center_iff.1 c.2
    simp_rw [Submonoid.smul_def, smul_smul, this]

instance {M α : Type*} [Monoid M] [MulAction M α] :
    SMulCommClass M (Submonoid.center M) α :=
  SMulCommClass.symm (Submonoid.center M) M α

variable {M}

/-- The center of a multiplication with unit is commutative and associative.

This is not an instance as it forms a non-defeq diamond with `Submonoid.toMonoid` in the `npow`
field. -/
@[to_additive /-- The center of an addition with zero is commutative and associative. -/]
/--
Definition of `center.commMonoid'` / `center.commMonoid'` 的定义

English:
abbreviation center.commMonoid'
  signature: : CommMonoid (center M)
  body: { (center M).toMulOneClass, Subsemigroup.center.commSemigroup with }

@[to_additive]

中文:
缩写 center.commMonoid'
  签名: : CommMonoid (center M)
  定义体: { (center M).toMulOneClass, Subsemigroup.center.commSemigroup with }

@[to_additive]

Depends on / 依赖: Subsemigroup, Subsemigroup.center.commSemigroup, center, commSemigroup, toMulOneClass
-/
abbrev center.commMonoid' : CommMonoid (center M) :=
  { (center M).toMulOneClass, Subsemigroup.center.commSemigroup with }

@[to_additive]
/--
theorem `center_prod` / 定理 `center_prod`

English:
theorem center_prod
  given: {N : Type*} [MulOneClass N]
  proof: SetLike.coe_injective Set.center_prod

@[to_additive]

中文:
定理 center_prod
  条件: {N : 类型} [MulOneClass N]
  证明: SetLike.coe_injective Set.center_prod

@[to_additive]
-/
protected theorem center_prod {N : Type*} [MulOneClass N] :
    center (M × N) = prod (center M) (center N) :=
  SetLike.coe_injective Set.center_prod

@[to_additive]
/--
theorem `center_pi` / 定理 `center_pi`

English:
theorem center_pi
  given: {ι : Type*} {M : ι -> Type*} [Π i, MulOneClass (M i)]
  proof: SetLike.coe_injective Set.center_pi

中文:
定理 center_pi
  条件: {ι : 类型} {M : ι -> 类型} [Π i, MulOneClass (M i)]
  证明: SetLike.coe_injective Set.center_pi
-/
protected theorem center_pi {ι : Type*} {M : ι -> Type*} [Π i, MulOneClass (M i)] :
    center (Π i, M i) = pi .univ fun i => center (M i) :=
  SetLike.coe_injective Set.center_pi

end MulOneClass

section Monoid

variable {M} [Monoid M]

/-- The center of a monoid is commutative. -/
@[to_additive]
/--
Instance `center.commMonoid` / 实例 `center.commMonoid`

English:
instance center.commMonoid
  signature: : CommMonoid (center M)
  body: { (center M).toMonoid, Subsemigroup.center.commSemigroup with }

中文:
实例 center.commMonoid
  签名: : CommMonoid (center M)
  定义体: { (center M).toMonoid, Subsemigroup.center.commSemigroup with }

Depends on / 依赖: Subsemigroup, Subsemigroup.center.commSemigroup, center, commSemigroup, toMonoid
-/
instance center.commMonoid : CommMonoid (center M) :=
  { (center M).toMonoid, Subsemigroup.center.commSemigroup with }

-- no instance diamond, unlike the primed version
example : center.commMonoid.toMonoid = Submonoid.toMonoid (center M) := by
  with_reducible_and_instances rfl

@[to_additive]
/--
theorem `mem_center_iff` / 定理 `mem_center_iff`

English:
theorem mem_center_iff
  given: {z : M}
  statement: z in center M ↔ forall g, g * z = z * g
  proof: by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl

@[to_additive]

中文:
定理 mem_center_iff
  条件: {z : M}
  结论: z in center M ↔ 对任意 g, g * z = z * g
  证明: by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl, Semigroup, Semigroup.mem_center_iff, mem_center_iff
-/
theorem mem_center_iff {z : M} : z in center M ↔ forall g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl

@[to_additive]
/--
Instance `decidableMemCenter` / 实例 `decidableMemCenter`

English:
instance decidableMemCenter
  signature: (a) [Decidable <| forall b : M, b * a = a * b]
  body: decidable_of_iff' _ mem_center_iff

中文:
实例 decidableMemCenter
  签名: (a) [Decidable <| 对任意 b : M, b * a = a * b]
  定义体: decidable_of_iff' _ mem_center_iff

Depends on / 依赖: decidable_of_iff, mem_center_iff
-/
instance decidableMemCenter (a) [Decidable <| forall b : M, b * a = a * b] : Decidable (a in center M) :=
  decidable_of_iff' _ mem_center_iff



/--
Instance `center.smulCommClass_left` / 实例 `center.smulCommClass_left`

English:
instance center.smulCommClass_left
  signature: : SMulCommClass (center M) M M where
  body: Commute.left_comm (m.prop.comm x) y

中文:
实例 center.smulCommClass_left
  签名: : SMulCommClass (center M) M M where
  定义体: Commute.left_comm (m.prop.comm x) y
-/
instance center.smulCommClass_left : SMulCommClass (center M) M M where
  smul_comm m x y := Commute.left_comm (m.prop.comm x) y

/--
Instance `center.smulCommClass_right` / 实例 `center.smulCommClass_right`

English:
instance center.smulCommClass_right
  signature: : SMulCommClass M (center M) M
  body: SMulCommClass.symm _ _ _

中文:
实例 center.smulCommClass_right
  签名: : SMulCommClass M (center M) M
  定义体: SMulCommClass.symm _ _ _
-/
instance center.smulCommClass_right : SMulCommClass M (center M) M :=
  SMulCommClass.symm _ _ _

/-! Note that `smulCommClass (center M) (center M) M` is already implied by
`Submonoid.smulCommClass_right` -/

example : SMulCommClass (center M) (center M) M := by infer_instance

end Monoid

section

variable (M : Type*) [CommMonoid M]

@[simp]
/--
theorem `center_eq_top` / 定理 `center_eq_top`

English:
theorem center_eq_top
  statement: center M = ⊤
  proof: SetLike.coe_injective (Set.center_eq_univ M)

中文:
定理 center_eq_top
  结论: center M = ⊤
  证明: SetLike.coe_injective (Set.center_eq_univ M)

Depends on / 依赖: Set.center_eq_univ, SetLike, SetLike.coe_injective, center_eq_univ, coe_injective
-/
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)

end

end Submonoid

variable (M)

/-- For a monoid, the units of the center inject into the center of the units. This is not an
equivalence in general; one case where this holds is for groups with zero, which is covered in
`centerUnitsEquivUnitsCenter`. -/
@[to_additive (attr := simps! apply_coe_val)
  /-- For an additive monoid, the units of the center inject into the center of the units. -/]
/--
Definition of `unitsCenterToCenterUnits` / `unitsCenterToCenterUnits` 的定义

English:
definition unitsCenterToCenterUnits
  signature: [Monoid M]
  body: (Units.map (Submonoid.center M).subtype).codRestrict _
fun u => Submonoid.mem_center_iff.mpr
fun r => Units.ext by
        rw [Units.val_mul]; rw [Units.coe_map]; rw [Submonoid.coe_subtype]; rw [Units.val_mul]; rw [Units.coe_map]; rw [Submonoid.coe_subtype]; rw [u.1.prop.comm r]

@[to_additive]

中文:
定义 unitsCenterToCenterUnits
  签名: [Monoid M]
  定义体: (Units.map (Submonoid.center M).subtype).codRestrict _
fun u => Submonoid.mem_center_iff.mpr
fun r => Units.ext by
        rw [Units.val_mul]; rw [Units.coe_map]; rw [Submonoid.coe_subtype]; rw [Units.val_mul]; rw [Units.coe_map]; rw [Submonoid.coe_subtype]; rw [u.1.prop.comm r]

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.center, Submonoid.coe_subtype, Submonoid.mem_center_iff.mpr, Units.coe_map, Units.ext, Units.map, Units.val_mul, center, codRestrict, coe_map, coe_subtype, mem_center_iff, prop.comm, subtype, val_mul
-/
def unitsCenterToCenterUnits [Monoid M] : (Submonoid.center M)ˣ ->* Submonoid.center (Mˣ) :=
(Units.map (Submonoid.center M).subtype).codRestrict _
fun u => Submonoid.mem_center_iff.mpr
fun r => Units.ext by
        rw [Units.val_mul]; rw [Units.coe_map]; rw [Submonoid.coe_subtype]; rw [Units.val_mul]; rw [Units.coe_map]; rw [Submonoid.coe_subtype]; rw [u.1.prop.comm r]

@[to_additive]
/--
theorem `unitsCenterToCenterUnits_injective` / 定理 `unitsCenterToCenterUnits_injective`

English:
theorem unitsCenterToCenterUnits_injective
  given: [Monoid M]
  proof: fun _a _b h => Units.ext Subtype.ext congr_arg (Units.val ∘ Subtype.val) h

中文:
定理 unitsCenterToCenterUnits_injective
  条件: [Monoid M]
  证明: fun _a _b h => Units.ext Subtype.ext congr_arg (Units.val ∘ Subtype.val) h

Depends on / 依赖: Subtype, Subtype.ext, Subtype.val, Units.ext, Units.val, congr_arg
-/
theorem unitsCenterToCenterUnits_injective [Monoid M] :
    Function.Injective (unitsCenterToCenterUnits M) :=
fun _a _b h => Units.ext Subtype.ext congr_arg (Units.val ∘ Subtype.val) h

section congr

variable {M} {N : Type*}

/--
theorem `_root_.MulEquivClass.apply_mem_center` / 定理 `_root_.MulEquivClass.apply_mem_center`

English:
theorem _root_.MulEquivClass.apply_mem_center
  statement: {F} [EquivLike F M N] [Mul M] [Mul N]
  proof: by
  let e := MulEquivClass.toMulEquiv e
  change e x in Set.center N
  constructor <;>
  (intros; apply e.symm.injective; simp only
    [map_mul, e.symm_apply_apply, (hx.comm _).eq, (isMulCentral_iff _).mp hx, ← hx.right_comm])

中文:
定理 _root_.MulEquivClass.apply_mem_center
  结论: {F} [EquivLike F M N] [Mul M] [Mul N]
  证明: by
  let e := MulEquivClass.toMulEquiv e
  change e x in Set.center N
  constructor <;>
  (intros; apply e.symm.injective; simp only
    [map_mul, e.symm_apply_apply, (hx.comm _).eq, (isMulCentral_iff _).mp hx, ← hx.right_comm])
-/
@[to_additive] theorem _root_.MulEquivClass.apply_mem_center {F} [EquivLike F M N] [Mul M] [Mul N]
    [MulEquivClass F M N] (e : F) {x : M} (hx : x in Set.center M) : e x in Set.center N := by
  let e := MulEquivClass.toMulEquiv e
  change e x in Set.center N
  constructor <;>
  (intros; apply e.symm.injective; simp only
    [map_mul, e.symm_apply_apply, (hx.comm _).eq, (isMulCentral_iff _).mp hx, ← hx.right_comm])

/--
theorem `_root_.MulEquivClass.apply_mem_center_iff` / 定理 `_root_.MulEquivClass.apply_mem_center_iff`

English:
theorem _root_.MulEquivClass.apply_mem_center_iff
  statement: {F} [EquivLike F M N]
  proof: ⟨(by simpa using MulEquivClass.apply_mem_center (MulEquivClass.toMulEquiv e).symm ·),
    MulEquivClass.apply_mem_center e⟩

中文:
定理 _root_.MulEquivClass.apply_mem_center_iff
  结论: {F} [EquivLike F M N]
  证明: ⟨(by simpa using MulEquivClass.apply_mem_center (MulEquivClass.toMulEquiv e).symm ·),
    MulEquivClass.apply_mem_center e⟩
-/
@[to_additive] theorem _root_.MulEquivClass.apply_mem_center_iff {F} [EquivLike F M N]
    [Mul M] [Mul N] [MulEquivClass F M N] (e : F) {x : M} :
    e x in Set.center N ↔ x in Set.center M :=
  ⟨(by simpa using MulEquivClass.apply_mem_center (MulEquivClass.toMulEquiv e).symm ·),
    MulEquivClass.apply_mem_center e⟩

/-- The center of isomorphic magmas are isomorphic. -/
@[to_additive (attr := simps) /-- The center of isomorphic additive magmas are isomorphic. -/]
/--
Definition of `Subsemigroup.centerCongr` / `Subsemigroup.centerCongr` 的定义

English:
definition Subsemigroup.centerCongr
  signature: [Mul M] [Mul N] (e : M ≃* N)
  body: ⟨e r, MulEquivClass.apply_mem_center e r.2⟩
  invFun s := ⟨e.symm s, MulEquivClass.apply_mem_center e.symm s.2⟩
  left_inv _ := Subtype.ext (e.left_inv _)
  right_inv _ := Subtype.ext (e.right_inv _)
  map_mul' _ _ := Subtype.ext (map_mul ..)

中文:
定义 Subsemigroup.centerCongr
  签名: [Mul M] [Mul N] (e : M ≃* N)
  定义体: ⟨e r, MulEquivClass.apply_mem_center e r.2⟩
  invFun s := ⟨e.symm s, MulEquivClass.apply_mem_center e.symm s.2⟩
  left_inv _ := Subtype.ext (e.left_inv _)
  right_inv _ := Subtype.ext (e.right_inv _)
  map_mul' _ _ := Subtype.ext (map_mul ..)

Depends on / 依赖: MulEquivClass, MulEquivClass.apply_mem_center, apply_mem_center
-/
def Subsemigroup.centerCongr [Mul M] [Mul N] (e : M ≃* N) : center M ≃* center N where
  toFun r := ⟨e r, MulEquivClass.apply_mem_center e r.2⟩
  invFun s := ⟨e.symm s, MulEquivClass.apply_mem_center e.symm s.2⟩
  left_inv _ := Subtype.ext (e.left_inv _)
  right_inv _ := Subtype.ext (e.right_inv _)
  map_mul' _ _ := Subtype.ext (map_mul ..)

/-- The center of isomorphic monoids are isomorphic. -/
@[to_additive (attr := simps!) /-- The center of isomorphic additive monoids are isomorphic. -/]
/--
Definition of `Submonoid.centerCongr` / `Submonoid.centerCongr` 的定义

English:
definition Submonoid.centerCongr
  signature: [MulOneClass M] [MulOneClass N] (e : M ≃* N)
  body: Subsemigroup.centerCongr e

中文:
定义 Submonoid.centerCongr
  签名: [MulOneClass M] [MulOneClass N] (e : M ≃* N)
  定义体: Subsemigroup.centerCongr e

Depends on / 依赖: Subsemigroup, Subsemigroup.centerCongr, centerCongr
-/
def Submonoid.centerCongr [MulOneClass M] [MulOneClass N] (e : M ≃* N) : center M ≃* center N :=
  Subsemigroup.centerCongr e

/--
theorem `MulOpposite.op_mem_center_iff` / 定理 `MulOpposite.op_mem_center_iff`

English:
theorem MulOpposite.op_mem_center_iff
  given: [Mul M] {x : M}
  proof: by
  simp_rw [Set.mem_center_iff, isMulCentral_iff, MulOpposite.forall, ← op_mul, op_inj]; aesop

中文:
定理 MulOpposite.op_mem_center_iff
  条件: [Mul M] {x : M}
  证明: by
  simp_rw [Set.mem_center_iff, isMulCentral_iff, MulOpposite.forall, ← op_mul, op_inj]; aesop
-/
@[to_additive] theorem MulOpposite.op_mem_center_iff [Mul M] {x : M} :
    op x in Set.center Mᵐᵒᵖ ↔ x in Set.center M := by
  simp_rw [Set.mem_center_iff, isMulCentral_iff, MulOpposite.forall, ← op_mul, op_inj]; aesop

/--
theorem `MulOpposite.unop_mem_center_iff` / 定理 `MulOpposite.unop_mem_center_iff`

English:
theorem MulOpposite.unop_mem_center_iff
  given: [Mul M] {x : Mᵐᵒᵖ}
  proof: op_mem_center_iff.symm

中文:
定理 MulOpposite.unop_mem_center_iff
  条件: [Mul M] {x : Mᵐᵒᵖ}
  证明: op_mem_center_iff.symm
-/
@[to_additive] theorem MulOpposite.unop_mem_center_iff [Mul M] {x : Mᵐᵒᵖ} :
    unop x in Set.center M ↔ x in Set.center Mᵐᵒᵖ :=
  op_mem_center_iff.symm

/-- The center of a magma is isomorphic to the center of its opposite. -/
@[to_additive (attr := simps)
/-- The center of an additive magma is isomorphic to the center of its opposite. -/]
/--
Definition of `Subsemigroup.centerToMulOpposite` / `Subsemigroup.centerToMulOpposite` 的定义

English:
definition Subsemigroup.centerToMulOpposite
  signature: [Mul M]
  body: ⟨_, MulOpposite.op_mem_center_iff.mpr r.2⟩
  invFun r := ⟨_, MulOpposite.unop_mem_center_iff.mpr r.2⟩
  map_mul' r _ := Subtype.ext (congr_arg MulOpposite.op <| r.2.1 _)

中文:
定义 Subsemigroup.centerToMulOpposite
  签名: [Mul M]
  定义体: ⟨_, MulOpposite.op_mem_center_iff.mpr r.2⟩
  invFun r := ⟨_, MulOpposite.unop_mem_center_iff.mpr r.2⟩
  map_mul' r _ := Subtype.ext (congr_arg MulOpposite.op <| r.2.1 _)

Depends on / 依赖: MulOpposite, MulOpposite.op_mem_center_iff.mpr, op_mem_center_iff
-/
def Subsemigroup.centerToMulOpposite [Mul M] : center M ≃* center Mᵐᵒᵖ where
  toFun r := ⟨_, MulOpposite.op_mem_center_iff.mpr r.2⟩
  invFun r := ⟨_, MulOpposite.unop_mem_center_iff.mpr r.2⟩
  map_mul' r _ := Subtype.ext (congr_arg MulOpposite.op <| r.2.1 _)

/-- The center of a monoid is isomorphic to the center of its opposite. -/
@[to_additive (attr := simps!)
/-- The center of an additive monoid is isomorphic to the center of its opposite. -/]
/--
Definition of `Submonoid.centerToMulOpposite` / `Submonoid.centerToMulOpposite` 的定义

English:
definition Submonoid.centerToMulOpposite
  signature: [MulOneClass M]
  body: Subsemigroup.centerToMulOpposite

中文:
定义 Submonoid.centerToMulOpposite
  签名: [MulOneClass M]
  定义体: Subsemigroup.centerToMulOpposite

Depends on / 依赖: Subsemigroup, Subsemigroup.centerToMulOpposite, centerToMulOpposite
-/
def Submonoid.centerToMulOpposite [MulOneClass M] : center M ≃* center Mᵐᵒᵖ :=
  Subsemigroup.centerToMulOpposite

end congr
