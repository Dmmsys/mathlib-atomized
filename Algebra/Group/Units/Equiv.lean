/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Units.Hom

/-!
# Multiplicative and additive equivalence acting on units.
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

variable {F α M N G : Type*}

/-- A group is isomorphic to its group of units. -/
@[to_additive (attr := simps apply_val symm_apply)
/-- An additive group is isomorphic to its group of additive units -/]
/--
Definition of `toUnits` / `toUnits` 的定义

English:
definition toUnits
  signature: [Group G]
  body: ⟨x, x⁻¹, mul_inv_cancel _, inv_mul_cancel _⟩
  invFun x := x
  map_mul' _ _ := Units.ext rfl

@[to_additive (attr := simp)]

中文:
定义 toUnits
  签名: [Group G]
  定义体: ⟨x, x⁻¹, mul_inv_cancel _, inv_mul_cancel _⟩
  invFun x := x
  map_mul' _ _ := Units.ext rfl

@[to_additive (attr := simp)]

Depends on / 依赖: inv_mul_cancel, mul_inv_cancel
-/
def toUnits [Group G] : G ≃* Gˣ where
  toFun x := ⟨x, x⁻¹, mul_inv_cancel _, inv_mul_cancel _⟩
  invFun x := x
  map_mul' _ _ := Units.ext rfl

@[to_additive (attr := simp)]
/--
lemma `toUnits_val_apply` / 引理 `toUnits_val_apply`

English:
lemma toUnits_val_apply
  given: {G : Type*} [Group G] (x : Gˣ)
  statement: toUnits (x : G) = x
  proof: by
  simp_rw [← MulEquiv.eq_symm_apply, toUnits_symm_apply]

中文:
引理 toUnits_val_apply
  条件: {G : 类型} [Group G] (x : Gˣ)
  结论: toUnits (x : G) = x
  证明: by
  simp_rw [← MulEquiv.eq_symm_apply, toUnits_symm_apply]

Depends on / 依赖: MulEquiv, MulEquiv.eq_symm_apply, eq_symm_apply, simp_rw, toUnits_symm_apply
-/
lemma toUnits_val_apply {G : Type*} [Group G] (x : Gˣ) : toUnits (x : G) = x := by
  simp_rw [← MulEquiv.eq_symm_apply, toUnits_symm_apply]

namespace Units

variable [Monoid M] [Monoid N]

/--
Definition of `mapEquiv` / `mapEquiv` 的定义

English:
definition mapEquiv
  signature: (h : M ≃* N)
  body: { map h.toMonoidHom with
    invFun := map h.symm.toMonoidHom,
left_inv := fun u => ext h.left_inv u,
right_inv := fun u => ext h.right_inv u }

@[simp]

中文:
定义 mapEquiv
  签名: (h : M ≃* N)
  定义体: { map h.toMonoidHom with
    invFun := map h.symm.toMonoidHom,
left_inv := fun u => ext h.left_inv u,
right_inv := fun u => ext h.right_inv u }

@[simp]

Depends on / 依赖: h.left_inv, h.right_inv, h.symm.toMonoidHom, h.toMonoidHom, invFun, left_inv, right_inv, toMonoidHom
-/
def mapEquiv (h : M ≃* N) : Mˣ ≃* Nˣ :=
  { map h.toMonoidHom with
    invFun := map h.symm.toMonoidHom,
left_inv := fun u => ext h.left_inv u,
right_inv := fun u => ext h.right_inv u }

@[simp]
/--
theorem `mapEquiv_symm` / 定理 `mapEquiv_symm`

English:
theorem mapEquiv_symm
  given: (h : M ≃* N)
  statement: (mapEquiv h).symm = mapEquiv h.symm
  proof: rfl

@[simp]

中文:
定理 mapEquiv_symm
  条件: (h : M ≃* N)
  结论: (mapEquiv h).symm = mapEquiv h.symm
  证明: rfl

@[simp]
-/
theorem mapEquiv_symm (h : M ≃* N) : (mapEquiv h).symm = mapEquiv h.symm :=
  rfl

@[simp]
/--
theorem `coe_mapEquiv` / 定理 `coe_mapEquiv`

English:
theorem coe_mapEquiv
  given: (h : M ≃* N) (x : Mˣ)
  statement: (mapEquiv h x : N) = h x
  proof: rfl

中文:
定理 coe_mapEquiv
  条件: (h : M ≃* N) (x : Mˣ)
  结论: (mapEquiv h x : N) = h x
  证明: rfl
-/
theorem coe_mapEquiv (h : M ≃* N) (x : Mˣ) : (mapEquiv h x : N) = h x :=
  rfl

/-- Left multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive (attr := simps -fullyApplied apply)
  /-- Left addition of an additive unit is a permutation of the underlying type. -/]
/--
Definition of `mulLeft` / `mulLeft` 的定义

English:
definition mulLeft
  signature: (u : Mˣ)
  body: u * x
  invFun x := u⁻¹ * x
  left_inv := u.inv_mul_cancel_left
  right_inv := u.mul_inv_cancel_left

@[to_additive (attr := simp)]

中文:
定义 mulLeft
  签名: (u : Mˣ)
  定义体: u * x
  invFun x := u⁻¹ * x
  left_inv := u.inv_mul_cancel_left
  right_inv := u.mul_inv_cancel_left

@[to_additive (attr := simp)]
-/
def mulLeft (u : Mˣ) : Equiv.Perm M where
  toFun x := u * x
  invFun x := u⁻¹ * x
  left_inv := u.inv_mul_cancel_left
  right_inv := u.mul_inv_cancel_left

@[to_additive (attr := simp)]
/--
theorem `mulLeft_symm` / 定理 `mulLeft_symm`

English:
theorem mulLeft_symm
  given: (u : Mˣ)
  statement: u.mulLeft.symm = u⁻¹.mulLeft
  proof: Equiv.ext fun _ => rfl

@[to_additive]

中文:
定理 mulLeft_symm
  条件: (u : Mˣ)
  结论: u.mulLeft.symm = u⁻¹.mulLeft
  证明: Equiv.ext fun _ => rfl

@[to_additive]

Depends on / 依赖: Equiv.ext
-/
theorem mulLeft_symm (u : Mˣ) : u.mulLeft.symm = u⁻¹.mulLeft :=
  Equiv.ext fun _ => rfl

@[to_additive]
/--
theorem `mulLeft_bijective` / 定理 `mulLeft_bijective`

English:
theorem mulLeft_bijective
  given: (a : Mˣ)
  statement: Function.Bijective ((a * ·) : M -> M)
  proof: (mulLeft a).bijective

中文:
定理 mulLeft_bijective
  条件: (a : Mˣ)
  结论: Function.Bijective ((a * ·) : M -> M)
  证明: (mulLeft a).bijective

Depends on / 依赖: bijective, mulLeft
-/
theorem mulLeft_bijective (a : Mˣ) : Function.Bijective ((a * ·) : M -> M) :=
  (mulLeft a).bijective

/-- Right multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive (attr := simps -fullyApplied apply)
/-- Right addition of an additive unit is a permutation of the underlying type. -/]
/--
Definition of `mulRight` / `mulRight` 的定义

English:
definition mulRight
  signature: (u : Mˣ)
  body: x * u
  invFun x := x * ↑u⁻¹
  left_inv x := mul_inv_cancel_right x u
  right_inv x := inv_mul_cancel_right x u

@[to_additive (attr := simp)]

中文:
定义 mulRight
  签名: (u : Mˣ)
  定义体: x * u
  invFun x := x * ↑u⁻¹
  left_inv x := mul_inv_cancel_right x u
  right_inv x := inv_mul_cancel_right x u

@[to_additive (attr := simp)]
-/
def mulRight (u : Mˣ) : Equiv.Perm M where
  toFun x := x * u
  invFun x := x * ↑u⁻¹
  left_inv x := mul_inv_cancel_right x u
  right_inv x := inv_mul_cancel_right x u

@[to_additive (attr := simp)]
/--
theorem `mulRight_symm` / 定理 `mulRight_symm`

English:
theorem mulRight_symm
  given: (u : Mˣ)
  statement: u.mulRight.symm = u⁻¹.mulRight
  proof: Equiv.ext fun _ => rfl

@[to_additive]

中文:
定理 mulRight_symm
  条件: (u : Mˣ)
  结论: u.mulRight.symm = u⁻¹.mulRight
  证明: Equiv.ext fun _ => rfl

@[to_additive]

Depends on / 依赖: Equiv.ext
-/
theorem mulRight_symm (u : Mˣ) : u.mulRight.symm = u⁻¹.mulRight :=
  Equiv.ext fun _ => rfl

@[to_additive]
/--
theorem `mulRight_bijective` / 定理 `mulRight_bijective`

English:
theorem mulRight_bijective
  given: (a : Mˣ)
  statement: Function.Bijective ((· * a) : M -> M)
  proof: (mulRight a).bijective

中文:
定理 mulRight_bijective
  条件: (a : Mˣ)
  结论: Function.Bijective ((· * a) : M -> M)
  证明: (mulRight a).bijective

Depends on / 依赖: bijective, mulRight
-/
theorem mulRight_bijective (a : Mˣ) : Function.Bijective ((· * a) : M -> M) :=
  (mulRight a).bijective

end Units

namespace Equiv

section Group

variable [Group G]

/-- Left multiplication in a `Group` is a permutation of the underlying type. -/
@[to_additive /-- Left addition in an `AddGroup` is a permutation of the underlying type. -/]
/--
Definition of `mulLeft` / `mulLeft` 的定义

English:
definition mulLeft
  signature: (a : G)
  body: (toUnits a).mulLeft

@[to_additive (attr := simp)]

中文:
定义 mulLeft
  签名: (a : G)
  定义体: (toUnits a).mulLeft

@[to_additive (attr := simp)]
-/
protected def mulLeft (a : G) : Perm G :=
  (toUnits a).mulLeft

@[to_additive (attr := simp)]
/--
theorem `coe_mulLeft` / 定理 `coe_mulLeft`

English:
theorem coe_mulLeft
  given: (a : G)
  statement: ⇑(Equiv.mulLeft a) = (a * ·)
  proof: rfl

中文:
定理 coe_mulLeft
  条件: (a : G)
  结论: ⇑(Equiv.mulLeft a) = (a * ·)
  证明: rfl
-/
theorem coe_mulLeft (a : G) : ⇑(Equiv.mulLeft a) = (a * ·) :=
  rfl

/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[to_additive (attr := simp)
/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/]
/--
theorem `mulLeft_symm_apply` / 定理 `mulLeft_symm_apply`

English:
theorem mulLeft_symm_apply
  given: (a : G)
  statement: ((Equiv.mulLeft a).symm : G -> G) = (a⁻¹ * ·)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 mulLeft_symm_apply
  条件: (a : G)
  结论: ((Equiv.mulLeft a).symm : G -> G) = (a⁻¹ * ·)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem mulLeft_symm_apply (a : G) : ((Equiv.mulLeft a).symm : G -> G) = (a⁻¹ * ·) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mulLeft_symm` / 定理 `mulLeft_symm`

English:
theorem mulLeft_symm
  given: (a : G)
  statement: (Equiv.mulLeft a).symm = Equiv.mulLeft a⁻¹
  proof: ext fun _ => rfl

@[to_additive]

中文:
定理 mulLeft_symm
  条件: (a : G)
  结论: (Equiv.mulLeft a).symm = Equiv.mulLeft a⁻¹
  证明: ext fun _ => rfl

@[to_additive]
-/
theorem mulLeft_symm (a : G) : (Equiv.mulLeft a).symm = Equiv.mulLeft a⁻¹ :=
  ext fun _ => rfl

@[to_additive]
/--
theorem `_root_.Group.mulLeft_bijective` / 定理 `_root_.Group.mulLeft_bijective`

English:
theorem _root_.Group.mulLeft_bijective
  given: (a : G)
  statement: Function.Bijective (a * ·)
  proof: (Equiv.mulLeft a).bijective

中文:
定理 _root_.Group.mulLeft_bijective
  条件: (a : G)
  结论: Function.Bijective (a * ·)
  证明: (Equiv.mulLeft a).bijective

Depends on / 依赖: Equiv.mulLeft, bijective, mulLeft
-/
theorem _root_.Group.mulLeft_bijective (a : G) : Function.Bijective (a * ·) :=
  (Equiv.mulLeft a).bijective

/-- Right multiplication in a `Group` is a permutation of the underlying type. -/
@[to_additive /-- Right addition in an `AddGroup` is a permutation of the underlying type. -/]
/--
Definition of `mulRight` / `mulRight` 的定义

English:
definition mulRight
  signature: (a : G)
  body: (toUnits a).mulRight

@[to_additive (attr := simp)]

中文:
定义 mulRight
  签名: (a : G)
  定义体: (toUnits a).mulRight

@[to_additive (attr := simp)]
-/
protected def mulRight (a : G) : Perm G :=
  (toUnits a).mulRight

@[to_additive (attr := simp)]
/--
theorem `coe_mulRight` / 定理 `coe_mulRight`

English:
theorem coe_mulRight
  given: (a : G)
  statement: ⇑(Equiv.mulRight a) = fun x => x * a
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mulRight
  条件: (a : G)
  结论: ⇑(Equiv.mulRight a) = fun x => x * a
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_mulRight (a : G) : ⇑(Equiv.mulRight a) = fun x => x * a :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mulRight_symm` / 定理 `mulRight_symm`

English:
theorem mulRight_symm
  given: (a : G)
  statement: (Equiv.mulRight a).symm = Equiv.mulRight a⁻¹
  proof: ext fun _ => rfl

中文:
定理 mulRight_symm
  条件: (a : G)
  结论: (Equiv.mulRight a).symm = Equiv.mulRight a⁻¹
  证明: ext fun _ => rfl
-/
theorem mulRight_symm (a : G) : (Equiv.mulRight a).symm = Equiv.mulRight a⁻¹ :=
  ext fun _ => rfl

/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[to_additive (attr := simp)
/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/]
/--
theorem `mulRight_symm_apply` / 定理 `mulRight_symm_apply`

English:
theorem mulRight_symm_apply
  given: (a : G)
  statement: ((Equiv.mulRight a).symm : G -> G) = fun x => x * a⁻¹
  proof: rfl

@[to_additive]

中文:
定理 mulRight_symm_apply
  条件: (a : G)
  结论: ((Equiv.mulRight a).symm : G -> G) = fun x => x * a⁻¹
  证明: rfl

@[to_additive]
-/
theorem mulRight_symm_apply (a : G) : ((Equiv.mulRight a).symm : G -> G) = fun x => x * a⁻¹ :=
  rfl

@[to_additive]
/--
theorem `_root_.Group.mulRight_bijective` / 定理 `_root_.Group.mulRight_bijective`

English:
theorem _root_.Group.mulRight_bijective
  given: (a : G)
  statement: Function.Bijective (· * a)
  proof: (Equiv.mulRight a).bijective

中文:
定理 _root_.Group.mulRight_bijective
  条件: (a : G)
  结论: Function.Bijective (· * a)
  证明: (Equiv.mulRight a).bijective

Depends on / 依赖: Equiv.mulRight, bijective, mulRight
-/
theorem _root_.Group.mulRight_bijective (a : G) : Function.Bijective (· * a) :=
  (Equiv.mulRight a).bijective

/-- A version of `Equiv.mulLeft a b⁻¹` that is defeq to `a / b`. -/
@[to_additive (attr := simps) /-- A version of `Equiv.addLeft a (-b)` that is defeq to `a - b`. -/]
/--
Definition of `divLeft` / `divLeft` 的定义

English:
definition divLeft
  signature: (a : G)
  body: a / b
  invFun b := b⁻¹ * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]

@[to_additive]

中文:
定义 divLeft
  签名: (a : G)
  定义体: a / b
  invFun b := b⁻¹ * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]

@[to_additive]
-/
protected def divLeft (a : G) : G ≃ G where
  toFun b := a / b
  invFun b := b⁻¹ * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]

@[to_additive]
/--
theorem `divLeft_eq_inv_trans_mulLeft` / 定理 `divLeft_eq_inv_trans_mulLeft`

English:
theorem divLeft_eq_inv_trans_mulLeft
  given: (a : G)
  proof: ext fun _ => div_eq_mul_inv _ _

中文:
定理 divLeft_eq_inv_trans_mulLeft
  条件: (a : G)
  证明: ext fun _ => div_eq_mul_inv _ _

Depends on / 依赖: div_eq_mul_inv
-/
theorem divLeft_eq_inv_trans_mulLeft (a : G) :
    Equiv.divLeft a = (Equiv.inv G).trans (Equiv.mulLeft a) :=
  ext fun _ => div_eq_mul_inv _ _

/-- A version of `Equiv.mulRight a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive (attr := simps) /-- A version of `Equiv.addRight (-a) b` that is defeq to `b - a`. -/]
/--
Definition of `divRight` / `divRight` 的定义

English:
definition divRight
  signature: (a : G)
  body: b / a
  invFun b := b * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]

@[to_additive]

中文:
定义 divRight
  签名: (a : G)
  定义体: b / a
  invFun b := b * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]

@[to_additive]
-/
protected def divRight (a : G) : G ≃ G where
  toFun b := b / a
  invFun b := b * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]

@[to_additive]
/--
theorem `divRight_eq_mulRight_inv` / 定理 `divRight_eq_mulRight_inv`

English:
theorem divRight_eq_mulRight_inv
  given: (a : G)
  statement: Equiv.divRight a = Equiv.mulRight a⁻¹
  proof: ext fun _ => div_eq_mul_inv _ _

中文:
定理 divRight_eq_mulRight_inv
  条件: (a : G)
  结论: Equiv.divRight a = Equiv.mulRight a⁻¹
  证明: ext fun _ => div_eq_mul_inv _ _

Depends on / 依赖: div_eq_mul_inv
-/
theorem divRight_eq_mulRight_inv (a : G) : Equiv.divRight a = Equiv.mulRight a⁻¹ :=
  ext fun _ => div_eq_mul_inv _ _

end Group

section CommGroup

variable [CommGroup G]

@[to_additive]
/--
lemma `symm_divLeft` / 引理 `symm_divLeft`

English:
lemma symm_divLeft
  given: (a : G)
  statement: (Equiv.divLeft a).symm = Equiv.divLeft a
  proof: ext fun _ => inv_mul_eq_div _ _

@[to_additive (attr := simp)]

中文:
引理 symm_divLeft
  条件: (a : G)
  结论: (Equiv.divLeft a).symm = Equiv.divLeft a
  证明: ext fun _ => inv_mul_eq_div _ _

@[to_additive (attr := simp)]

Depends on / 依赖: inv_mul_eq_div
-/
lemma symm_divLeft (a : G) : (Equiv.divLeft a).symm = Equiv.divLeft a :=
  ext fun _ => inv_mul_eq_div _ _

@[to_additive (attr := simp)]
/--
lemma `divLeft_involutive` / 引理 `divLeft_involutive`

English:
lemma divLeft_involutive
  given: (a : G)
  statement: Function.Involutive (Equiv.divLeft a)
  proof: fun _ => div_div_cancel ..

中文:
引理 divLeft_involutive
  条件: (a : G)
  结论: Function.Involutive (Equiv.divLeft a)
  证明: fun _ => div_div_cancel ..

Depends on / 依赖: div_div_cancel
-/
lemma divLeft_involutive (a : G) : Function.Involutive (Equiv.divLeft a) :=
  fun _ => div_div_cancel ..

end CommGroup

end Equiv

variable (α) in
/-- The `αˣ` type is equivalent to a subtype of `α × α`. -/
@[simps]
/--
Definition of `unitsEquivProdSubtype` / `unitsEquivProdSubtype` 的定义

English:
definition unitsEquivProdSubtype
  signature: [Monoid α]
  body: ⟨(u, ↑u⁻¹), u.val_inv, u.inv_val⟩
  invFun p := Units.mk (p : α × α).1 (p : α × α).2 p.prop.1 p.prop.2

中文:
定义 unitsEquivProdSubtype
  签名: [Monoid α]
  定义体: ⟨(u, ↑u⁻¹), u.val_inv, u.inv_val⟩
  invFun p := Units.mk (p : α × α).1 (p : α × α).2 p.prop.1 p.prop.2

Depends on / 依赖: inv_val, u.inv_val, u.val_inv, val_inv
-/
def unitsEquivProdSubtype [Monoid α] : αˣ ≃ {p : α × α // p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} where
  toFun u := ⟨(u, ↑u⁻¹), u.val_inv, u.inv_val⟩
  invFun p := Units.mk (p : α × α).1 (p : α × α).2 p.prop.1 p.prop.2

/-- In a `DivisionCommMonoid`, `Equiv.inv` is a `MulEquiv`. There is a variant of this
`MulEquiv.inv' G : G ≃* Gᵐᵒᵖ` for the non-commutative case. -/
@[to_additive (attr := simps apply)
  /-- When the `AddGroup` is commutative, `Equiv.neg` is an `AddEquiv`. -/]
/--
Definition of `MulEquiv.inv` / `MulEquiv.inv` 的定义

English:
definition MulEquiv.inv
  signature: (G : Type*) [DivisionCommMonoid G]
  body: { Equiv.inv G with toFun := Inv.inv, invFun := Inv.inv, map_mul' := mul_inv }

@[to_additive (attr := simp)]

中文:
定义 MulEquiv.inv
  签名: (G : 类型) [DivisionCommMonoid G]
  定义体: { Equiv.inv G with toFun := Inv.inv, invFun := Inv.inv, map_mul' := mul_inv }

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.inv, Inv.inv, invFun, map_mul, mul_inv
-/
def MulEquiv.inv (G : Type*) [DivisionCommMonoid G] : G ≃* G :=
  { Equiv.inv G with toFun := Inv.inv, invFun := Inv.inv, map_mul' := mul_inv }

@[to_additive (attr := simp)]
/--
theorem `MulEquiv.inv_symm` / 定理 `MulEquiv.inv_symm`

English:
theorem MulEquiv.inv_symm
  given: (G : Type*) [DivisionCommMonoid G]
  proof: rfl

中文:
定理 MulEquiv.inv_symm
  条件: (G : 类型) [DivisionCommMonoid G]
  证明: rfl
-/
theorem MulEquiv.inv_symm (G : Type*) [DivisionCommMonoid G] :
    (MulEquiv.inv G).symm = MulEquiv.inv G :=
  rfl

section EquivLike
variable [Monoid M] [Monoid N] [EquivLike F M N] [MulEquivClass F M N] (f : F) {x : M}

-- Higher priority to take over the non-additivisable `isUnit_map_iff`
@[to_additive (attr := simp high)]
/--
lemma `MulEquiv.isUnit_map` / 引理 `MulEquiv.isUnit_map`

English:
lemma MulEquiv.isUnit_map
  statement: IsUnit (f x) ↔ IsUnit x where
  proof: by
simpa using hx.map MonoidHom.mk ⟨EquivLike.inv f, EquivLike.injective f by simp⟩
fun x y => EquivLike.injective f by simp
  mpr := .map f

中文:
引理 MulEquiv.isUnit_map
  结论: IsUnit (f x) ↔ IsUnit x where
  证明: by
simpa using hx.map MonoidHom.mk ⟨EquivLike.inv f, EquivLike.injective f by simp⟩
fun x y => EquivLike.injective f by simp
  mpr := .map f

Depends on / 依赖: EquivLike, EquivLike.injective, EquivLike.inv, MonoidHom, MonoidHom.mk, hx.map, injective
-/
lemma MulEquiv.isUnit_map : IsUnit (f x) ↔ IsUnit x where
  mp hx := by
simpa using hx.map MonoidHom.mk ⟨EquivLike.inv f, EquivLike.injective f by simp⟩
fun x y => EquivLike.injective f by simp
  mpr := .map f

/--
theorem `isLocalHom_equiv` / 定理 `isLocalHom_equiv`

English:
theorem isLocalHom_equiv
  statement: IsLocalHom f where map_nonunit
  proof: by simp

中文:
定理 isLocalHom_equiv
  结论: IsLocalHom f where map_nonunit
  证明: by simp
-/
@[instance] theorem isLocalHom_equiv : IsLocalHom f where map_nonunit := by simp

end EquivLike
