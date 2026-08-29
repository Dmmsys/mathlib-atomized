/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.Pi.Units

/-!
# Units of restricted products

This file contains results about the units of a restricted product. The restricted
product `Πʳ i : ι, [R i, B i]_[𝓕]` of a family of types `R` with respect to a family of
subsets `B` along a filter `𝓕` is defined in `Mathlib.Topology.Algebra.RestrictedProduct.Basic`.
Here, we give conditions that characterize when an element of the restricted product is a unit,
and provide an isomorphism between the units of the restricted product and the restricted product
of the units.

## Main definitions

* `RestrictedProduct.unitsEquiv`: the (monoid) isomorphism between `(Πʳ i, [R i, B i]_[𝓕])ˣ`
  and `Πʳ i, [(R i)ˣ, (B i).units]_[𝓕]`.

## Tags

restricted product, adeles, ideles
-/

@[expose] public section

namespace RestrictedProduct

variable {ι : Type*}
variable {R : ι -> Type*} [forall i, Monoid (R i)]
variable {S : ι -> Type*} [Π i, SetLike (S i) (R i)] [forall (i : ι), SubmonoidClass (S i) (R i)]
variable {B : Π i, S i}
variable {𝓕 : Filter ι}

/--
theorem `isUnit_of_eventually_isUnit` / 定理 `isUnit_of_eventually_isUnit`

English:
theorem isUnit_of_eventually_isUnit
  statement: {x : Πʳ i, [R i, B i]_[𝓕]} (hx : forall i, IsUnit (x i))
  proof: by
  rw [isUnit_iff_exists]
  use .mk (fun i => (hx i).unit.inv) (by
    filter_upwards [hxr] with i ⟨h, hu⟩
    have hu : (hx i).unit.1 * hu.unit.inv = 1 := Subtype.val_inj.2 hu.mul_val_inv
    simp [← Units.eq_inv_of_mul_eq_one_left hu])
  simp [RestrictedProduct.ext_iff]

中文:
定理 isUnit_of_eventually_isUnit
  结论: {x : Πʳ i, [R i, B i]_[𝓕]} (hx : 对任意 i, 是单位 (x i))
  证明: by
  rw [isUnit_iff_exists]
  use .mk (fun i => (hx i).unit.inv) (by
    filter_upwards [hxr] with i ⟨h, hu⟩
    have hu : (hx i).unit.1 * hu.unit.inv = 1 := Subtype.val_inj.2 hu.mul_val_inv
    simp [← Units.eq_inv_of_mul_eq_one_left hu])
  simp [RestrictedProduct.ext_iff]

Depends on / 依赖: RestrictedProduct, RestrictedProduct.ext_iff, Subtype, Subtype.val_inj, Units.eq_inv_of_mul_eq_one_left, eq_inv_of_mul_eq_one_left, ext_iff, filter_upwards, hu.mul_val_inv, hu.unit.inv, isUnit_iff_exists, mul_val_inv, unit.inv, val_inj
-/
theorem isUnit_of_eventually_isUnit {x : Πʳ i, [R i, B i]_[𝓕]} (hx : forall i, IsUnit (x i))
    (hxr : forallᶠ i in 𝓕, exists (h : x i in B i), IsUnit (⟨x i, h⟩ : B i)) :
    IsUnit x := by
  rw [isUnit_iff_exists]
  use .mk (fun i => (hx i).unit.inv) (by
    filter_upwards [hxr] with i ⟨h, hu⟩
    have hu : (hx i).unit.1 * hu.unit.inv = 1 := Subtype.val_inj.2 hu.mul_val_inv
    simp [← Units.eq_inv_of_mul_eq_one_left hu])
  simp [RestrictedProduct.ext_iff]

/--
theorem `eventually_isUnit_of_isUnit` / 定理 `eventually_isUnit_of_isUnit`

English:
theorem eventually_isUnit_of_isUnit
  given: {x : Πʳ i, [R i, B i]_[𝓕]} (hx : IsUnit x)
  proof: by
  simp only [isUnit_iff_exists, RestrictedProduct.ext_iff, ← forall_and] at hx
  simp only [isUnit_iff_exists]
  choose b hb using hx
  exact ⟨Classical.skolem.symm.1 ⟨b, hb⟩, by filter_upwards [x.2, b.2] using
    fun i hx hb => ⟨hx, ⟨b i, hb⟩, by simp_all [← SetLike.coe_eq_coe]⟩⟩

@[deprecated (since := "2026-04-06")]
alias eventualy_isUnit_of_isUnit := eventually_isUnit_of_isUnit

中文:
定理 eventually_isUnit_of_isUnit
  条件: {x : Πʳ i, [R i, B i]_[𝓕]} (hx : 是单位 x)
  证明: by
  simp only [isUnit_iff_exists, RestrictedProduct.ext_iff, ← forall_and] at hx
  simp only [isUnit_iff_exists]
  choose b hb using hx
  exact ⟨Classical.skolem.symm.1 ⟨b, hb⟩, by filter_upwards [x.2, b.2] using
    fun i hx hb => ⟨hx, ⟨b i, hb⟩, by simp_all [← SetLike.coe_eq_coe]⟩⟩

@[deprecated (since := "2026-04-06")]
alias eventualy_isUnit_of_isUnit := eventually_isUnit_of_isUnit

Depends on / 依赖: Classical, Classical.skolem.symm, RestrictedProduct, RestrictedProduct.ext_iff, SetLike, SetLike.coe_eq_coe, coe_eq_coe, ext_iff, filter_upwards, forall_and, isUnit_iff_exists, skolem
-/
theorem eventually_isUnit_of_isUnit {x : Πʳ i, [R i, B i]_[𝓕]} (hx : IsUnit x) :
    (forall i, IsUnit (x i)) ∧ forallᶠ i in 𝓕, exists (h : x i in B i), IsUnit (⟨x i, h⟩ : B i) := by
  simp only [isUnit_iff_exists, RestrictedProduct.ext_iff, ← forall_and] at hx
  simp only [isUnit_iff_exists]
  choose b hb using hx
  exact ⟨Classical.skolem.symm.1 ⟨b, hb⟩, by filter_upwards [x.2, b.2] using
    fun i hx hb => ⟨hx, ⟨b i, hb⟩, by simp_all [← SetLike.coe_eq_coe]⟩⟩

@[deprecated (since := "2026-04-06")]
alias eventualy_isUnit_of_isUnit := eventually_isUnit_of_isUnit

/--
theorem `isUnit_iff` / 定理 `isUnit_iff`

English:
theorem isUnit_iff
  given: {x : Πʳ i, [R i, B i]_[𝓕]}
  proof: ⟨eventually_isUnit_of_isUnit, fun h => isUnit_of_eventually_isUnit h.1 h.2⟩

中文:
定理 isUnit_iff
  条件: {x : Πʳ i, [R i, B i]_[𝓕]}
  证明: ⟨eventually_isUnit_of_isUnit, fun h => isUnit_of_eventually_isUnit h.1 h.2⟩

Depends on / 依赖: eventually_isUnit_of_isUnit, isUnit_of_eventually_isUnit
-/
theorem isUnit_iff {x : Πʳ i, [R i, B i]_[𝓕]} :
    IsUnit x ↔ (forall i, IsUnit (x i)) ∧ forallᶠ i in 𝓕, exists (h : x i in B i), IsUnit (⟨x i, h⟩ : B i) :=
  ⟨eventually_isUnit_of_isUnit, fun h => isUnit_of_eventually_isUnit h.1 h.2⟩

/--
Definition of `coeUnits` / `coeUnits` 的定义

English:
definition coeUnits
  signature: : Πʳ i, [R i, B i]_[𝓕]ˣ ->* (i : ι) -> (R i)ˣ
  body: MulEquiv.piUnits.toMonoidHom.comp Units.map coeMonoidHom

中文:
定义 coeUnits
  签名: : Πʳ i, [R i, B i]_[𝓕]ˣ ->* (i : ι) -> (R i)ˣ
  定义体: MulEquiv.piUnits.toMonoidHom.comp Units.map coeMonoidHom

Depends on / 依赖: MulEquiv, MulEquiv.piUnits.toMonoidHom.comp, Units.map, coeMonoidHom, piUnits, toMonoidHom
-/
def coeUnits : Πʳ i, [R i, B i]_[𝓕]ˣ ->* (i : ι) -> (R i)ˣ :=
MulEquiv.piUnits.toMonoidHom.comp Units.map coeMonoidHom

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mkUnit` / `mkUnit` 的定义

English:
definition mkUnit
  signature: (x : Π i, (R i)ˣ) (hx : forallᶠ i in 𝓕, x i in (Submonoid.ofClass (B i)).units)
  body: ⟨fun i => (x i).1, by filter_upwards [hx] using fun i hi => hi.1⟩
  inv := ⟨fun i => (x i)⁻¹.1, by filter_upwards [hx] using fun i hi => hi.2⟩
  val_inv := by ext; simp
  inv_val := by ext; simp

中文:
定义 mkUnit
  签名: (x : Π i, (R i)ˣ) (hx : 对任意ᶠ i in 𝓕, x i in (子幺半群.ofClass (B i)).units)
  定义体: ⟨fun i => (x i).1, by filter_upwards [hx] using fun i hi => hi.1⟩
  inv := ⟨fun i => (x i)⁻¹.1, by filter_upwards [hx] using fun i hi => hi.2⟩
  val_inv := by ext; simp
  inv_val := by ext; simp

Depends on / 依赖: filter_upwards
-/
def mkUnit (x : Π i, (R i)ˣ) (hx : forallᶠ i in 𝓕, x i in (Submonoid.ofClass (B i)).units) :
    Πʳ i, [R i, B i]_[𝓕]ˣ where
  val := ⟨fun i => (x i).1, by filter_upwards [hx] using fun i hi => hi.1⟩
  inv := ⟨fun i => (x i)⁻¹.1, by filter_upwards [hx] using fun i hi => hi.2⟩
  val_inv := by ext; simp
  inv_val := by ext; simp

variable (R) in
/--
Definition of `unitsEquiv` / `unitsEquiv` 的定义

English:
definition unitsEquiv
  signature: : Πʳ i, [R i, B i]_[𝓕]ˣ ≃* Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓕] where
  body: ⟨coeUnits x, by filter_upwards [x.val.2, x.inv.2] using fun i hi hi' => ⟨hi, hi'⟩⟩
  invFun y := mkUnit y.1 y.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

中文:
定义 unitsEquiv
  签名: : Πʳ i, [R i, B i]_[𝓕]ˣ ≃* Πʳ i, [(R i)ˣ, (子幺半群.ofClass (B i)).units]_[𝓕] where
  定义体: ⟨coeUnits x, by filter_upwards [x.val.2, x.inv.2] using fun i hi hi' => ⟨hi, hi'⟩⟩
  invFun y := mkUnit y.1 y.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: coeUnits, filter_upwards, x.inv, x.val
-/
def unitsEquiv : Πʳ i, [R i, B i]_[𝓕]ˣ ≃* Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓕] where
  toFun x := ⟨coeUnits x, by filter_upwards [x.val.2, x.inv.2] using fun i hi hi' => ⟨hi, hi'⟩⟩
  invFun y := mkUnit y.1 y.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/--
lemma `unitsEquiv_apply` / 引理 `unitsEquiv_apply`

English:
lemma unitsEquiv_apply
  given: (i : ι) (x : Πʳ i, [R i, B i]_[𝓕]ˣ)
  proof: rfl

中文:
引理 unitsEquiv_apply
  条件: (i : ι) (x : Πʳ i, [R i, B i]_[𝓕]ˣ)
  证明: rfl
-/
@[simp] lemma unitsEquiv_apply (i : ι) (x : Πʳ i, [R i, B i]_[𝓕]ˣ) :
    (unitsEquiv R x i) = x.1 i := rfl

/--
lemma `coe_unitsEquiv_apply` / 引理 `coe_unitsEquiv_apply`

English:
lemma coe_unitsEquiv_apply
  given: (x : Πʳ i, [R i, B i]_[𝓕]ˣ) (i : ι)
  proof: rfl

中文:
引理 coe_unitsEquiv_apply
  条件: (x : Πʳ i, [R i, B i]_[𝓕]ˣ) (i : ι)
  证明: rfl
-/
@[simp] lemma coe_unitsEquiv_apply (x : Πʳ i, [R i, B i]_[𝓕]ˣ) (i : ι) :
    (unitsEquiv R x).1 i = unitsEquiv R x i := rfl

end RestrictedProduct
