/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.GroupTheory.Congruence.Basic
public import Mathlib.RingTheory.Congruence.Defs

/-!
# Congruence relations on rings

This file contains basic results concerning congruence relations on rings,
which extend `Con` and `AddCon` on monoids and additive monoids.

Most of the time you likely want to use the `Ideal.Quotient` API that is built on top of this.

## Main Definitions

* `RingCon R`: the type of congruence relations respecting `+` and `*`.
* `RingConGen r`: the inductively defined smallest ring congruence relation containing a given
  binary relation.

## TODO

* Copy across more API from `Con` and `AddCon` in `Mathlib/GroupTheory/Congruence/`.
-/

@[expose] public section

variable {α β R R' : Type*}

namespace RingCon

section Quotient

section Algebraic

/-! ### Scalar multiplication

The operation of scalar multiplication `•` descends naturally to the quotient.
-/

section SMul

variable [Add R] [MulOneClass R]
variable [SMul α R] [IsScalarTower α R R]
variable [SMul β R] [IsScalarTower β R R]
variable (c : RingCon R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul α c.Quotient
  body: ⟨c.smulAux (Con.smul c.toCon)⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 标量乘法 α c.商
  定义体: ⟨c.smulAux (Con.smul c.toCon)⟩

@[simp, norm_cast]

Depends on / 依赖: Con.smul, c.smulAux, c.toCon, smulAux
-/
instance : SMul α c.Quotient := ⟨c.smulAux (Con.smul c.toCon)⟩

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (a : α) (x : R)
  statement: (↑(a • x) : c.Quotient) = a • (x : c.Quotient)
  proof: rfl

中文:
定理 coe_smul
  条件: (a : α) (x : R)
  结论: (↑(a • x) : c.商) = a • (x : c.商)
  证明: rfl
-/
theorem coe_smul (a : α) (x : R) : (↑(a • x) : c.Quotient) = a • (x : c.Quotient) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: α β R] : SMulCommClass α β c.Quotient
  body: inferInstanceAs (SMulCommClass α β c.toCon.Quotient)

中文:
实例 [标量交换类
  签名: α β R] : 标量交换类 α β c.商
  定义体: inferInstanceAs (SMulCommClass α β c.toCon.Quotient)

Depends on / 依赖: Quotient, SMulCommClass, c.toCon.Quotient
-/
instance [SMulCommClass α β R] : SMulCommClass α β c.Quotient :=
  inferInstanceAs (SMulCommClass α β c.toCon.Quotient)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: α β] [IsScalarTower α β R] : IsScalarTower α β c.Quotient
  body: inferInstanceAs (IsScalarTower α β c.toCon.Quotient)

中文:
实例 [标量乘法
  签名: α β] [标量塔 α β R] : 标量塔 α β c.商
  定义体: inferInstanceAs (IsScalarTower α β c.toCon.Quotient)

Depends on / 依赖: IsScalarTower, Quotient, c.toCon.Quotient
-/
instance [SMul α β] [IsScalarTower α β R] : IsScalarTower α β c.Quotient :=
  inferInstanceAs (IsScalarTower α β c.toCon.Quotient)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: αᵐᵒᵖ R] [IsCentralScalar α R] : IsCentralScalar α c.Quotient
  body: inferInstanceAs (IsCentralScalar α c.toCon.Quotient)

中文:
实例 [标量乘法
  签名: αᵐᵒᵖ R] [中心标量 α R] : 中心标量 α c.商
  定义体: inferInstanceAs (IsCentralScalar α c.toCon.Quotient)

Depends on / 依赖: IsCentralScalar, Quotient, c.toCon.Quotient
-/
instance [SMul αᵐᵒᵖ R] [IsCentralScalar α R] : IsCentralScalar α c.Quotient :=
  inferInstanceAs (IsCentralScalar α c.toCon.Quotient)

end SMul

/--
Instance `isScalarTower_right` / 实例 `isScalarTower_right`

English:
instance isScalarTower_right
  signature: [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
  body: Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' smul_mul_assoc _ _ _

中文:
实例 isScalarTower_right
  签名: [加法 R] [MulOne类 R] [标量乘法 α R] [标量塔 α R R]
  定义体: Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' smul_mul_assoc _ _ _

Depends on / 依赖: Quotient, Quotient.ind, Quotient.mk, congr_arg, smul_mul_assoc
-/
instance isScalarTower_right [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    (c : RingCon R) : IsScalarTower α c.Quotient c.Quotient where
smul_assoc _ := Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' smul_mul_assoc _ _ _

/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
  body: Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' (mul_smul_comm _ _ _).symm

中文:
实例 smulCommClass
  签名: [加法 R] [MulOne类 R] [标量乘法 α R] [标量塔 α R R]
  定义体: Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' (mul_smul_comm _ _ _).symm

Depends on / 依赖: Quotient, Quotient.ind, Quotient.mk, congr_arg, mul_smul_comm
-/
instance smulCommClass [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    [SMulCommClass α R R] (c : RingCon R) : SMulCommClass α c.Quotient c.Quotient where
smul_comm _ := Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' (mul_smul_comm _ _ _).symm

/--
Instance `smulCommClass'` / 实例 `smulCommClass'`

English:
instance smulCommClass'
  signature: [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
  body: haveI := SMulCommClass.symm R α R
  SMulCommClass.symm _ _ _

中文:
实例 smulCommClass'
  签名: [加法 R] [MulOne类 R] [标量乘法 α R] [标量塔 α R R]
  定义体: haveI := SMulCommClass.symm R α R
  SMulCommClass.symm _ _ _

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance smulCommClass' [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    [SMulCommClass R α R] (c : RingCon R) : SMulCommClass c.Quotient α c.Quotient :=
  haveI := SMulCommClass.symm R α R
  SMulCommClass.symm _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] [NonAssocSemiring R] [MulAction α R] [IsScalarTower α R R]
  body: inferInstanceAs MulAction α c.toCon.Quotient

中文:
实例 [幺半群
  签名: α] [非结合半环 R] [乘法作用 α R] [标量塔 α R R]
  定义体: inferInstanceAs MulAction α c.toCon.Quotient

Depends on / 依赖: MulAction, Quotient, c.toCon.Quotient
-/
instance [Monoid α] [NonAssocSemiring R] [MulAction α R] [IsScalarTower α R R]
    (c : RingCon R) : MulAction α c.Quotient :=
inferInstanceAs MulAction α c.toCon.Quotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] [NonAssocSemiring R] [DistribMulAction α R] [IsScalarTower α R R]
  body: fun _ => congr_arg toQuotient smul_zero _
smul_add := fun _ => Quotient.ind₂' fun _ _ => congr_arg toQuotient smul_add _ _ _

中文:
实例 [幺半群
  签名: α] [非结合半环 R] [分配乘法作用 α R] [标量塔 α R R]
  定义体: fun _ => congr_arg toQuotient smul_zero _
smul_add := fun _ => Quotient.ind₂' fun _ _ => congr_arg toQuotient smul_add _ _ _

Depends on / 依赖: congr_arg, smul_zero, toQuotient
-/
instance [Monoid α] [NonAssocSemiring R] [DistribMulAction α R] [IsScalarTower α R R]
    (c : RingCon R) : DistribMulAction α c.Quotient where
smul_zero := fun _ => congr_arg toQuotient smul_zero _
smul_add := fun _ => Quotient.ind₂' fun _ _ => congr_arg toQuotient smul_add _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] [Semiring R] [MulSemiringAction α R] [IsScalarTower α R R] (c
  body: fun _ => congr_arg toQuotient smul_one _
smul_mul := fun _ => Quotient.ind₂' fun _ _ => congr_arg toQuotient
    MulSemiringAction.smul_mul _ _ _

中文:
实例 [幺半群
  签名: α] [半环 R] [MulSemiring作用 α R] [标量塔 α R R] (c
  定义体: fun _ => congr_arg toQuotient smul_one _
smul_mul := fun _ => Quotient.ind₂' fun _ _ => congr_arg toQuotient
    MulSemiringAction.smul_mul _ _ _

Depends on / 依赖: congr_arg, smul_one, toQuotient
-/
instance [Monoid α] [Semiring R] [MulSemiringAction α R] [IsScalarTower α R R] (c : RingCon R) :
    MulSemiringAction α c.Quotient where
smul_one := fun _ => congr_arg toQuotient smul_one _
smul_mul := fun _ => Quotient.ind₂' fun _ _ => congr_arg toQuotient
    MulSemiringAction.smul_mul _ _ _

section
variable [CommSemiring α] [Semiring R] [Algebra α R]

instance (c : RingCon R) : Algebra α c.Quotient where
  algebraMap := c.mk'.comp (algebraMap α R)
commutes' _ := Quotient.ind' fun _ => congr_arg Quotient.mk'' Algebra.commutes _ _
smul_def' _ := Quotient.ind' fun _ => congr_arg Quotient.mk'' Algebra.smul_def _ _

@[simp, norm_cast]
/--
theorem `coe_algebraMap` / 定理 `coe_algebraMap`

English:
theorem coe_algebraMap
  given: (c : RingCon R) (s : α)
  proof: rfl

中文:
定理 coe_algebraMap
  条件: (c : RingCon R) (s : α)
  证明: rfl
-/
theorem coe_algebraMap (c : RingCon R) (s : α) :
    (algebraMap α R s : c.Quotient) = algebraMap α c.Quotient s :=
  rfl

variable (α) in
/--
Definition of `mkₐ` / `mkₐ` 的定义

English:
definition mkₐ
  signature: (c : RingCon R)
  body: { mk' c with commutes' _ := rfl }

中文:
定义 mkₐ
  签名: (c : RingCon R)
  定义体: { mk' c with commutes' _ := rfl }
-/
@[simps!] def mkₐ (c : RingCon R) : R ->ₐ[α] c.Quotient :=
  { mk' c with commutes' _ := rfl }

/--
theorem `mkₐ_surjective` / 定理 `mkₐ_surjective`

English:
theorem mkₐ_surjective
  given: (c : RingCon R)
  proof: mk'_surjective c

中文:
定理 mkₐ_surjective
  条件: (c : RingCon R)
  证明: mk'_surjective c
-/
theorem mkₐ_surjective (c : RingCon R) :
    Function.Surjective (c.mkₐ (α := α)) :=
  mk'_surjective c

end

end Algebraic

end Quotient

/-! ### Lattice structure

The API in this section is copied from `Mathlib/GroupTheory/Congruence/Defs.lean`
-/

section Lattice

variable [Add R] [Mul R] [Add R'] [Mul R'] {c d : RingCon R}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (RingCon R)
  body: forall ⦃x y⦄, c x y -> d x y

中文:
实例 :
  签名: LE (RingCon R)
  定义体: forall ⦃x y⦄, c x y -> d x y
-/
instance : LE (RingCon R) where
  le c d := forall ⦃x y⦄, c x y -> d x y

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  statement: c <= d ↔ forall {x y}, c x y -> d x y
  proof: .rfl

@[gcongr]

中文:
定理 le_def
  结论: c <= d ↔ 对任意 {x y}, c x y -> d x y
  证明: .rfl

@[gcongr]
-/
theorem le_def : c <= d ↔ forall {x y}, c x y -> d x y := .rfl

@[gcongr]
/--
theorem `comap_mono` / 定理 `comap_mono`

English:
theorem comap_mono
  proof: fun _ _ h₁ => h h₁

中文:
定理 comap_mono
  证明: fun _ _ h₁ => h h₁
-/
theorem comap_mono
    {F : Type*} [FunLike F R R'] [AddHomClass F R R'] [MulHomClass F R R']
    {J J' : RingCon R'} {f : F} (h : J <= J') :
    J.comap f <= J'.comap f :=
  fun _ _ h₁ => h h₁

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (RingCon R)
  body: { r := fun x y => forall c : RingCon R, c in S -> c x y
      iseqv :=
⟨fun x c _hc => c.refl x, fun h c hc => c.symm h c hc, fun h1 h2 c hc =>
c.trans (h1 c hc) h2 c hc⟩
add' := fun h1 h2 c hc => c.add (h1 c hc) h2 c hc
mul' := fun h1 h2 c hc => c.mul (h1 c hc) h2 c hc }

中文:
实例 :
  签名: 下确界集 (RingCon R)
  定义体: { r := fun x y => forall c : RingCon R, c in S -> c x y
      iseqv :=
⟨fun x c _hc => c.refl x, fun h c hc => c.symm h c hc, fun h1 h2 c hc =>
c.trans (h1 c hc) h2 c hc⟩
add' := fun h1 h2 c hc => c.add (h1 c hc) h2 c hc
mul' := fun h1 h2 c hc => c.mul (h1 c hc) h2 c hc }

Depends on / 依赖: RingCon, c.add, c.mul, c.refl, c.symm, c.trans
-/
instance : InfSet (RingCon R) where
  sInf S :=
    { r := fun x y => forall c : RingCon R, c in S -> c x y
      iseqv :=
⟨fun x c _hc => c.refl x, fun h c hc => c.symm h c hc, fun h1 h2 c hc =>
c.trans (h1 c hc) h2 c hc⟩
add' := fun h1 h2 c hc => c.add (h1 c hc) h2 c hc
mul' := fun h1 h2 c hc => c.mul (h1 c hc) h2 c hc }

/--
theorem `sInf_toSetoid` / 定理 `sInf_toSetoid`

English:
theorem sInf_toSetoid
  given: (S : Set (RingCon R))
  statement: (sInf S).toSetoid = sInf ((·.toSetoid) '' S)
  proof: Setoid.ext fun x y =>
    ⟨fun h r ⟨c, hS, hr⟩ => by rw [← hr]; exact h c hS, fun h c hS => h c.toSetoid ⟨c, hS, rfl⟩⟩

中文:
定理 sInf_toSetoid
  条件: (S : 集合 (RingCon R))
  结论: (sInf S).toSetoid = sInf ((·.toSetoid) '' S)
  证明: Setoid.ext fun x y =>
    ⟨fun h r ⟨c, hS, hr⟩ => by rw [← hr]; exact h c hS, fun h c hS => h c.toSetoid ⟨c, hS, rfl⟩⟩

Depends on / 依赖: Setoid, Setoid.ext, c.toSetoid, toSetoid
-/
theorem sInf_toSetoid (S : Set (RingCon R)) : (sInf S).toSetoid = sInf ((·.toSetoid) '' S) :=
  Setoid.ext fun x y =>
    ⟨fun h r ⟨c, hS, hr⟩ => by rw [← hr]; exact h c hS, fun h c hS => h c.toSetoid ⟨c, hS, rfl⟩⟩

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
under the map to the underlying binary relation. -/
@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (RingCon R))
  statement: ⇑(sInf S) = sInf ((⇑) '' S)
  proof: by
  ext; simp only [sInf_image, iInf_apply, iInf_Prop_eq]; rfl

@[simp, norm_cast]

中文:
定理 coe_sInf
  条件: (S : 集合 (RingCon R))
  结论: ⇑(sInf S) = sInf ((⇑) '' S)
  证明: by
  ext; simp only [sInf_image, iInf_apply, iInf_Prop_eq]; rfl

@[simp, norm_cast]

Depends on / 依赖: iInf_Prop_eq, iInf_apply, sInf_image
-/
theorem coe_sInf (S : Set (RingCon R)) : ⇑(sInf S) = sInf ((⇑) '' S) := by
  ext; simp only [sInf_image, iInf_apply, iInf_Prop_eq]; rfl

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} (f : ι -> RingCon R)
  statement: ⇑(iInf f) = ⨅ i, ⇑(f i)
  proof: by
  rw [iInf]; rw [coe_sInf]; rw [← Set.range_comp]; rw [sInf_range]; rw [Function.comp_def]

中文:
定理 coe_iInf
  条件: {ι : 类型层*} (f : ι -> RingCon R)
  结论: ⇑(iInf f) = ⨅ i, ⇑(f i)
  证明: by
  rw [iInf]; rw [coe_sInf]; rw [← Set.range_comp]; rw [sInf_range]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Set.range_comp, coe_sInf, comp_def, range_comp, sInf_range
-/
theorem coe_iInf {ι : Sort*} (f : ι -> RingCon R) : ⇑(iInf f) = ⨅ i, ⇑(f i) := by
  rw [iInf]; rw [coe_sInf]; rw [← Set.range_comp]; rw [sInf_range]; rw [Function.comp_def]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (RingCon R)
  body: id
le_trans _c1 _c2 _c3 h1 h2 _x _y h := h2 h1 h
  le_antisymm _c _d hc hd := ext fun _x _y => ⟨fun h => hc h, fun h => hd h⟩

中文:
实例 :
  签名: 偏序 (RingCon R)
  定义体: id
le_trans _c1 _c2 _c3 h1 h2 _x _y h := h2 h1 h
  le_antisymm _c _d hc hd := ext fun _x _y => ⟨fun h => hc h, fun h => hd h⟩
-/
instance : PartialOrder (RingCon R) where
  le_refl _c _ _ := id
le_trans _c1 _c2 _c3 h1 h2 _x _y h := h2 h1 h
  le_antisymm _c _d hc hd := ext fun _x _y => ⟨fun h => hc h, fun h => hd h⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (RingCon R)
  body: completeLatticeOfInf (RingCon R) fun s =>
    ⟨fun r hr x y h => (h : forall r in s, (r : RingCon R) x y) r hr,
      fun _r hr _x _y h _r' hr' => hr hr' h⟩
  inf c d :=
    { toSetoid := c.toSetoid ⊓ d.toSetoid
      mul' := fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩
      add' := fun h1 h2 => ⟨c.add h1.1 h2.1, d.add h1.2 h2.2⟩ }
  inf_le_left _ _ := fun _ _ h => h.1
  inf_le_right _ _ := fun _ _ h => h.2
  le_inf _ _ _ hb hc := fun _ _ h => ⟨hb h, hc h⟩
  top :=
    { (⊤ : Setoid R) with
      mul' := fun _ _ => trivial
      add' := fun _ _ => trivial }
  le_top _ := fun _ _ _h => trivial
  bot :=
    { (⊥ : Setoid R) with
      mul' := congr_arg₂ _
      add' := congr_arg₂ _ }
  bot_le c := fun x _y h => h ▸ c.refl x

中文:
实例 :
  签名: 完备格 (RingCon R)
  定义体: completeLatticeOfInf (RingCon R) fun s =>
    ⟨fun r hr x y h => (h : forall r in s, (r : RingCon R) x y) r hr,
      fun _r hr _x _y h _r' hr' => hr hr' h⟩
  inf c d :=
    { toSetoid := c.toSetoid ⊓ d.toSetoid
      mul' := fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩
      add' := fun h1 h2 => ⟨c.add h1.1 h2.1, d.add h1.2 h2.2⟩ }
  inf_le_left _ _ := fun _ _ h => h.1
  inf_le_right _ _ := fun _ _ h => h.2
  le_inf _ _ _ hb hc := fun _ _ h => ⟨hb h, hc h⟩
  top :=
    { (⊤ : Setoid R) with
      mul' := fun _ _ => trivial
      add' := fun _ _ => trivial }
  le_top _ := fun _ _ _h => trivial
  bot :=
    { (⊥ : Setoid R) with
      mul' := congr_arg₂ _
      add' := congr_arg₂ _ }
  bot_le c := fun x _y h => h ▸ c.refl x

Depends on / 依赖: RingCon, completeLatticeOfInf
-/
instance : CompleteLattice (RingCon R) where
  __ := completeLatticeOfInf (RingCon R) fun s =>
    ⟨fun r hr x y h => (h : forall r in s, (r : RingCon R) x y) r hr,
      fun _r hr _x _y h _r' hr' => hr hr' h⟩
  inf c d :=
    { toSetoid := c.toSetoid ⊓ d.toSetoid
      mul' := fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩
      add' := fun h1 h2 => ⟨c.add h1.1 h2.1, d.add h1.2 h2.2⟩ }
  inf_le_left _ _ := fun _ _ h => h.1
  inf_le_right _ _ := fun _ _ h => h.2
  le_inf _ _ _ hb hc := fun _ _ h => ⟨hb h, hc h⟩
  top :=
    { (⊤ : Setoid R) with
      mul' := fun _ _ => trivial
      add' := fun _ _ => trivial }
  le_top _ := fun _ _ _h => trivial
  bot :=
    { (⊥ : Setoid R) with
      mul' := congr_arg₂ _
      add' := congr_arg₂ _ }
  bot_le c := fun x _y h => h ▸ c.refl x

/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  statement: ⇑(⊤ : RingCon R) = ⊤
  proof: rfl

中文:
引理 coe_top
  结论: ⇑(⊤ : RingCon R) = ⊤
  证明: rfl
-/
@[simp, norm_cast] lemma coe_top : ⇑(⊤ : RingCon R) = ⊤ := rfl
/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  statement: ⇑(⊥ : RingCon R) = Eq
  proof: rfl

中文:
引理 coe_bot
  结论: ⇑(⊥ : RingCon R) = 相等
  证明: rfl
-/
@[simp, norm_cast] lemma coe_bot : ⇑(⊥ : RingCon R) = Eq := rfl

/--
lemma `toCon_top` / 引理 `toCon_top`

English:
lemma toCon_top
  statement: (⊤ : RingCon R).toCon = ⊤
  proof: rfl

中文:
引理 toCon_top
  结论: (⊤ : RingCon R).toCon = ⊤
  证明: rfl
-/
@[simp] lemma toCon_top : (⊤ : RingCon R).toCon = ⊤ := rfl
/--
lemma `toCon_bot` / 引理 `toCon_bot`

English:
lemma toCon_bot
  statement: (⊥ : RingCon R).toCon = ⊥
  proof: rfl

中文:
引理 toCon_bot
  结论: (⊥ : RingCon R).toCon = ⊥
  证明: rfl
-/
@[simp] lemma toCon_bot : (⊥ : RingCon R).toCon = ⊥ := rfl

/--
lemma `toCon_eq_top` / 引理 `toCon_eq_top`

English:
lemma toCon_eq_top
  statement: c.toCon = ⊤ ↔ c = ⊤
  proof: by rw [← toCon_top, toCon_inj]

中文:
引理 toCon_eq_top
  结论: c.toCon = ⊤ ↔ c = ⊤
  证明: by rw [← toCon_top, toCon_inj]
-/
@[simp] lemma toCon_eq_top : c.toCon = ⊤ ↔ c = ⊤ := by rw [← toCon_top, toCon_inj]
/--
lemma `toCon_eq_bot` / 引理 `toCon_eq_bot`

English:
lemma toCon_eq_bot
  statement: c.toCon = ⊥ ↔ c = ⊥
  proof: by rw [← toCon_bot, toCon_inj]

中文:
引理 toCon_eq_bot
  结论: c.toCon = ⊥ ↔ c = ⊥
  证明: by rw [← toCon_bot, toCon_inj]
-/
@[simp] lemma toCon_eq_bot : c.toCon = ⊥ ↔ c = ⊥ := by rw [← toCon_bot, toCon_inj]

/--
lemma `subsingleton_quotient` / 引理 `subsingleton_quotient`

English:
lemma subsingleton_quotient
  statement: Subsingleton c.Quotient ↔ c = ⊤
  proof: by simp [RingCon.Quotient]

中文:
引理 subsingleton_quotient
  结论: 子单例 c.商 ↔ c = ⊤
  证明: by simp [RingCon.Quotient]
-/
@[simp] lemma subsingleton_quotient : Subsingleton c.Quotient ↔ c = ⊤ := by simp [RingCon.Quotient]

/--
lemma `nontrivial_quotient` / 引理 `nontrivial_quotient`

English:
lemma nontrivial_quotient
  statement: Nontrivial c.Quotient ↔ c != ⊤
  proof: by
  simp [← not_subsingleton_iff_nontrivial]

中文:
引理 nontrivial_quotient
  结论: 非平凡 c.商 ↔ c != ⊤
  证明: by
  simp [← not_subsingleton_iff_nontrivial]
-/
@[simp] lemma nontrivial_quotient : Nontrivial c.Quotient ↔ c != ⊤ := by
  simp [← not_subsingleton_iff_nontrivial]

/-- The infimum of two congruence relations equals the infimum of the underlying binary
operations. -/
@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: {c d : RingCon R}
  statement: ⇑(c ⊓ d) = ⇑c ⊓ ⇑d
  proof: rfl

中文:
定理 coe_inf
  条件: {c d : RingCon R}
  结论: ⇑(c ⊓ d) = ⇑c ⊓ ⇑d
  证明: rfl
-/
theorem coe_inf {c d : RingCon R} : ⇑(c ⊓ d) = ⇑c ⊓ ⇑d := rfl

/--
theorem `inf_iff_and` / 定理 `inf_iff_and`

English:
theorem inf_iff_and
  given: {c d : RingCon R} {x y}
  statement: (c ⊓ d) x y ↔ c x y ∧ d x y
  proof: Iff.rfl

中文:
定理 inf_iff_and
  条件: {c d : RingCon R} {x y}
  结论: (c ⊓ d) x y ↔ c x y ∧ d x y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem inf_iff_and {c d : RingCon R} {x y} : (c ⊓ d) x y ↔ c x y ∧ d x y :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nontrivial (RingCon R) where
  body: let ⟨x, y, ne⟩ := exists_pair_ne R
⟨⊥, ⊤, ne_of_apply_ne (· x y) by simp [ne]⟩

中文:
实例 [非平凡
  签名: R] : 非平凡 (RingCon R) where
  定义体: let ⟨x, y, ne⟩ := exists_pair_ne R
⟨⊥, ⊤, ne_of_apply_ne (· x y) by simp [ne]⟩

Depends on / 依赖: exists_pair_ne, ne_of_apply_ne
-/
instance [Nontrivial R] : Nontrivial (RingCon R) where
  exists_pair_ne :=
    let ⟨x, y, ne⟩ := exists_pair_ne R
⟨⊥, ⊤, ne_of_apply_ne (· x y) by simp [ne]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: R] : Subsingleton (RingCon R) where
  body: ext fun r r' => by simp_rw [Subsingleton.elim r' r, c.refl, c'.refl]

中文:
实例 [子单例
  签名: R] : 子单例 (RingCon R) where
  定义体: ext fun r r' => by simp_rw [Subsingleton.elim r' r, c.refl, c'.refl]

Depends on / 依赖: Subsingleton, Subsingleton.elim, c.refl, simp_rw
-/
instance [Subsingleton R] : Subsingleton (RingCon R) where
  allEq c c' := ext fun r r' => by simp_rw [Subsingleton.elim r' r, c.refl, c'.refl]

/--
theorem `nontrivial_iff` / 定理 `nontrivial_iff`

English:
theorem nontrivial_iff
  statement: Nontrivial (RingCon R) ↔ Nontrivial R
  proof: by
  cases subsingleton_or_nontrivial R
  on_goal 1 => simp_rw [← not_subsingleton_iff_nontrivial, not_iff_not]
  all_goals exact iff_of_true inferInstance ‹_›

中文:
定理 nontrivial_iff
  结论: 非平凡 (RingCon R) ↔ 非平凡 R
  证明: by
  cases subsingleton_or_nontrivial R
  on_goal 1 => simp_rw [← not_subsingleton_iff_nontrivial, not_iff_not]
  all_goals exact iff_of_true inferInstance ‹_›

Depends on / 依赖: all_goals, iff_of_true, not_iff_not, not_subsingleton_iff_nontrivial, on_goal, simp_rw, subsingleton_or_nontrivial
-/
theorem nontrivial_iff : Nontrivial (RingCon R) ↔ Nontrivial R := by
  cases subsingleton_or_nontrivial R
  on_goal 1 => simp_rw [← not_subsingleton_iff_nontrivial, not_iff_not]
  all_goals exact iff_of_true inferInstance ‹_›

/--
theorem `subsingleton_iff` / 定理 `subsingleton_iff`

English:
theorem subsingleton_iff
  statement: Subsingleton (RingCon R) ↔ Subsingleton R
  proof: by
  simp_rw [← not_nontrivial_iff_subsingleton, nontrivial_iff]

中文:
定理 subsingleton_iff
  结论: 子单例 (RingCon R) ↔ 子单例 R
  证明: by
  simp_rw [← not_nontrivial_iff_subsingleton, nontrivial_iff]

Depends on / 依赖: nontrivial_iff, not_nontrivial_iff_subsingleton, simp_rw
-/
theorem subsingleton_iff : Subsingleton (RingCon R) ↔ Subsingleton R := by
  simp_rw [← not_nontrivial_iff_subsingleton, nontrivial_iff]

/--
theorem `le_ringConGen` / 定理 `le_ringConGen`

English:
theorem le_ringConGen
  given: {r : R -> R -> Prop}
  statement: r <= ⇑(ringConGen r)
  proof: RingConGen.Rel.of

中文:
定理 le_ringConGen
  条件: {r : R -> R -> 命题}
  结论: r <= ⇑(ringConGen r)
  证明: RingConGen.Rel.of

Depends on / 依赖: RingConGen, RingConGen.Rel.of
-/
theorem le_ringConGen {r : R -> R -> Prop} : r <= ⇑(ringConGen r) :=
  RingConGen.Rel.of

/--
theorem `ringConGen_eq` / 定理 `ringConGen_eq`

English:
theorem ringConGen_eq
  given: (r : R -> R -> Prop)
  proof: le_antisymm
    (fun _x _y H =>
      RingConGen.Rel.recOn H (fun _ _ h _ hs => hs _ _ h) (RingCon.refl _)
        (fun _ => RingCon.symm _) (fun _ _ => RingCon.trans _)
        (fun _ _ h1 h2 c hc => c.add (h1 c hc) <| h2 c hc)
        (fun _ _ h1 h2 c hc => c.mul (h1 c hc) <| h2 c hc))
    (sInf_le le_ringConGen)

中文:
定理 ringConGen_eq
  条件: (r : R -> R -> 命题)
  证明: le_antisymm
    (fun _x _y H =>
      RingConGen.Rel.recOn H (fun _ _ h _ hs => hs _ _ h) (RingCon.refl _)
        (fun _ => RingCon.symm _) (fun _ _ => RingCon.trans _)
        (fun _ _ h1 h2 c hc => c.add (h1 c hc) <| h2 c hc)
        (fun _ _ h1 h2 c hc => c.mul (h1 c hc) <| h2 c hc))
    (sInf_le le_ringConGen)

Depends on / 依赖: RingCon, RingCon.refl, RingCon.symm, RingCon.trans, RingConGen, RingConGen.Rel.recOn, c.add, c.mul, le_antisymm, le_ringConGen, sInf_le
-/
theorem ringConGen_eq (r : R -> R -> Prop) :
    ringConGen r = sInf {s : RingCon R | forall x y, r x y -> s x y} :=
  le_antisymm
    (fun _x _y H =>
      RingConGen.Rel.recOn H (fun _ _ h _ hs => hs _ _ h) (RingCon.refl _)
        (fun _ => RingCon.symm _) (fun _ _ => RingCon.trans _)
        (fun _ _ h1 h2 c hc => c.add (h1 c hc) <| h2 c hc)
        (fun _ _ h1 h2 c hc => c.mul (h1 c hc) <| h2 c hc))
    (sInf_le le_ringConGen)

/--
theorem `ringConGen_le` / 定理 `ringConGen_le`

English:
theorem ringConGen_le
  given: {r : R -> R -> Prop} {c : RingCon R}
  statement: ringConGen r <= c ↔ r <= ⇑c
  proof: ⟨le_trans le_ringConGen, ringConGen_eq r ▸ fun h => sInf_le h⟩

中文:
定理 ringConGen_le
  条件: {r : R -> R -> 命题} {c : RingCon R}
  结论: ringConGen r <= c ↔ r <= ⇑c
  证明: ⟨le_trans le_ringConGen, ringConGen_eq r ▸ fun h => sInf_le h⟩

Depends on / 依赖: le_ringConGen, le_trans, ringConGen_eq, sInf_le
-/
theorem ringConGen_le {r : R -> R -> Prop} {c : RingCon R} : ringConGen r <= c ↔ r <= ⇑c :=
  ⟨le_trans le_ringConGen, ringConGen_eq r ▸ fun h => sInf_le h⟩

variable (R) in
/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (ringConGen (R := R)) (⇑) where
  body: ringConGen r
  gc _r _ := ringConGen_le
  le_l_u _ := le_ringConGen
  choice_eq _ _ := rfl

中文:
定义 gi
  签名: : Galois嵌入 (ringConGen (R := R)) (⇑) where
  定义体: ringConGen r
  gc _r _ := ringConGen_le
  le_l_u _ := le_ringConGen
  choice_eq _ _ := rfl
-/
protected def gi : GaloisInsertion (ringConGen (R := R)) (⇑) where
  choice r _h := ringConGen r
  gc _r _ := ringConGen_le
  le_l_u _ := le_ringConGen
  choice_eq _ _ := rfl

/--
theorem `ringConGen_monotone` / 定理 `ringConGen_monotone`

English:
theorem ringConGen_monotone
  statement: Monotone (ringConGen (R := R))
  proof: .gc.monotone_l RingCon.gi R

中文:
定理 ringConGen_monotone
  结论: 递增 (ringConGen (R := R))
  证明: .gc.monotone_l RingCon.gi R
-/
theorem ringConGen_monotone : Monotone (ringConGen (R := R)) :=
.gc.monotone_l RingCon.gi R

/-- Given binary relations `r, s` with `r` contained in `s`, the smallest congruence relation
containing `s` contains the smallest congruence relation containing `r`. -/
@[gcongr]
/--
theorem `ringConGen_mono` / 定理 `ringConGen_mono`

English:
theorem ringConGen_mono
  given: {r s : R -> R -> Prop} (h : forall x y, r x y -> s x y)
  proof: ringConGen_monotone h

中文:
定理 ringConGen_mono
  条件: {r s : R -> R -> 命题} (h : 对任意 x y, r x y -> s x y)
  证明: ringConGen_monotone h

Depends on / 依赖: ringConGen_monotone
-/
theorem ringConGen_mono {r s : R -> R -> Prop} (h : forall x y, r x y -> s x y) :
    ringConGen r <= ringConGen s :=
  ringConGen_monotone h

/--
theorem `ringConGen_of_ringCon` / 定理 `ringConGen_of_ringCon`

English:
theorem ringConGen_of_ringCon
  given: (c : RingCon R)
  statement: ringConGen c = c
  proof: .l_u_eq _ RingCon.gi R

中文:
定理 ringConGen_of_ringCon
  条件: (c : RingCon R)
  结论: ringConGen c = c
  证明: .l_u_eq _ RingCon.gi R

Depends on / 依赖: RingCon, RingCon.gi, l_u_eq
-/
theorem ringConGen_of_ringCon (c : RingCon R) : ringConGen c = c :=
.l_u_eq _ RingCon.gi R

/--
theorem `ringConGen_idem` / 定理 `ringConGen_idem`

English:
theorem ringConGen_idem
  given: (r : R -> R -> Prop)
  statement: ringConGen (ringConGen r) = ringConGen r
  proof: .gc.l_u_l_eq_l _ RingCon.gi R

中文:
定理 ringConGen_idem
  条件: (r : R -> R -> 命题)
  结论: ringConGen (ringConGen r) = ringConGen r
  证明: .gc.l_u_l_eq_l _ RingCon.gi R

Depends on / 依赖: RingCon, RingCon.gi, gc.l_u_l_eq_l, l_u_l_eq_l
-/
theorem ringConGen_idem (r : R -> R -> Prop) : ringConGen (ringConGen r) = ringConGen r :=
.gc.l_u_l_eq_l _ RingCon.gi R

/--
theorem `ringConGen_sup` / 定理 `ringConGen_sup`

English:
theorem ringConGen_sup
  given: (r s : R -> R -> Prop)
  statement: ringConGen (r ⊔ s) = ringConGen r ⊔ ringConGen s
  proof: .gc.l_sup RingCon.gi R

中文:
定理 ringConGen_sup
  条件: (r s : R -> R -> 命题)
  结论: ringConGen (r ⊔ s) = ringConGen r ⊔ ringConGen s
  证明: .gc.l_sup RingCon.gi R

Depends on / 依赖: RingCon, RingCon.gi, gc.l_sup, l_sup
-/
theorem ringConGen_sup (r s : R -> R -> Prop) : ringConGen (r ⊔ s) = ringConGen r ⊔ ringConGen s :=
.gc.l_sup RingCon.gi R

/--
theorem `ringConGen_sSup` / 定理 `ringConGen_sSup`

English:
theorem ringConGen_sSup
  given: (rs : Set (R -> R -> Prop))
  statement: ringConGen (sSup rs) = ⨆ r in rs, ringConGen r
  proof: .gc.l_sSup RingCon.gi R

中文:
定理 ringConGen_sSup
  条件: (rs : 集合 (R -> R -> 命题))
  结论: ringConGen (sSup rs) = ⨆ r in rs, ringConGen r
  证明: .gc.l_sSup RingCon.gi R

Depends on / 依赖: RingCon, RingCon.gi, gc.l_sSup, l_sSup
-/
theorem ringConGen_sSup (rs : Set (R -> R -> Prop)) : ringConGen (sSup rs) = ⨆ r in rs, ringConGen r :=
.gc.l_sSup RingCon.gi R

/--
theorem `ringConGen_iSup` / 定理 `ringConGen_iSup`

English:
theorem ringConGen_iSup
  given: {ι : Sort*} (r : ι -> R -> R -> Prop)
  proof: .gc.l_iSup RingCon.gi R

中文:
定理 ringConGen_iSup
  条件: {ι : 类型层*} (r : ι -> R -> R -> 命题)
  证明: .gc.l_iSup RingCon.gi R

Depends on / 依赖: RingCon, RingCon.gi, gc.l_iSup, l_iSup
-/
theorem ringConGen_iSup {ι : Sort*} (r : ι -> R -> R -> Prop) :
    ringConGen (iSup r) = ⨆ i, ringConGen (r i) :=
.gc.l_iSup RingCon.gi R

/--
theorem `sup_def` / 定理 `sup_def`

English:
theorem sup_def
  given: (c d : RingCon R)
  statement: c ⊔ d = ringConGen (⇑c ⊔ ⇑d)
  proof: .symm .l_sup_u _ _ RingCon.gi R

中文:
定理 sup_def
  条件: (c d : RingCon R)
  结论: c ⊔ d = ringConGen (⇑c ⊔ ⇑d)
  证明: .symm .l_sup_u _ _ RingCon.gi R

Depends on / 依赖: RingCon, RingCon.gi, l_sup_u
-/
theorem sup_def (c d : RingCon R) : c ⊔ d = ringConGen (⇑c ⊔ ⇑d) :=
.symm .l_sup_u _ _ RingCon.gi R

/--
theorem `sup_eq_ringConGen` / 定理 `sup_eq_ringConGen`

English:
theorem sup_eq_ringConGen
  given: (c d : RingCon R)
  statement: c ⊔ d = ringConGen fun x y => c x y ∨ d x y
  proof: sup_def c d

中文:
定理 sup_eq_ringConGen
  条件: (c d : RingCon R)
  结论: c ⊔ d = ringConGen fun x y => c x y ∨ d x y
  证明: sup_def c d

Depends on / 依赖: sup_def
-/
theorem sup_eq_ringConGen (c d : RingCon R) : c ⊔ d = ringConGen fun x y => c x y ∨ d x y :=
  sup_def c d

/--
theorem `sSup_def` / 定理 `sSup_def`

English:
theorem sSup_def
  given: (S : Set (RingCon R))
  statement: sSup S = ringConGen (sSup ((⇑) '' S))
  proof: .symm .l_sSup_u_image _ RingCon.gi R

中文:
定理 sSup_def
  条件: (S : 集合 (RingCon R))
  结论: sSup S = ringConGen (sSup ((⇑) '' S))
  证明: .symm .l_sSup_u_image _ RingCon.gi R

Depends on / 依赖: RingCon, RingCon.gi, l_sSup_u_image
-/
theorem sSup_def (S : Set (RingCon R)) : sSup S = ringConGen (sSup ((⇑) '' S)) :=
.symm .l_sSup_u_image _ RingCon.gi R

/--
theorem `sSup_eq_ringConGen` / 定理 `sSup_eq_ringConGen`

English:
theorem sSup_eq_ringConGen
  given: (S : Set (RingCon R))
  proof: by
  rw [sSup_def]
  congr! with x y
  simp

中文:
定理 sSup_eq_ringConGen
  条件: (S : 集合 (RingCon R))
  证明: by
  rw [sSup_def]
  congr! with x y
  simp

Depends on / 依赖: sSup_def
-/
theorem sSup_eq_ringConGen (S : Set (RingCon R)) :
    sSup S = ringConGen fun x y => exists c : RingCon R, c in S ∧ c x y := by
  rw [sSup_def]
  congr! with x y
  simp

open scoped Function

/--
theorem `le_comap_ringConGen` / 定理 `le_comap_ringConGen`

English:
theorem le_comap_ringConGen
  statement: {F} [FunLike F R' R] [MulHomClass F R' R] [AddHomClass F R' R]
  proof: ringConGen_le.2 fun _ _ h => RingConGen.Rel.of _ _ h

中文:
定理 le_comap_ringConGen
  结论: {F} [函数状 F R' R] [乘法态射类 F R' R] [加法态射类 F R' R]
  证明: ringConGen_le.2 fun _ _ h => RingConGen.Rel.of _ _ h

Depends on / 依赖: RingConGen, RingConGen.Rel.of, ringConGen_le
-/
theorem le_comap_ringConGen {F} [FunLike F R' R] [MulHomClass F R' R] [AddHomClass F R' R]
    (r : R -> R -> Prop) (f : F) :
    ringConGen (r on f) <= (ringConGen r).comap f :=
  ringConGen_le.2 fun _ _ h => RingConGen.Rel.of _ _ h

/--
theorem `comap_injective` / 定理 `comap_injective`

English:
theorem comap_injective
  statement: {F} [FunLike F R' R] [MulHomClass F R' R] [AddHomClass F R' R]
  proof: .of_comp (f := toCon) (Con.comap_injective f hf <| map_mul f).comp toCon_injective

中文:
定理 comap_injective
  结论: {F} [函数状 F R' R] [乘法态射类 F R' R] [加法态射类 F R' R]
  证明: .of_comp (f := toCon) (Con.comap_injective f hf <| map_mul f).comp toCon_injective

Depends on / 依赖: Con.comap_injective, comap_injective, map_mul, of_comp, toCon_injective
-/
theorem comap_injective {F} [FunLike F R' R] [MulHomClass F R' R] [AddHomClass F R' R]
    (f : F) (hf : Function.Surjective f) :
    Function.Injective (comap · f) :=
.of_comp (f := toCon) (Con.comap_injective f hf <| map_mul f).comp toCon_injective

/--
theorem `comap_ringConGen_ringEquiv` / 定理 `comap_ringConGen_ringEquiv`

English:
theorem comap_ringConGen_ringEquiv
  statement: {R R'} [NonAssocSemiring R] [NonAssocSemiring R']
  proof: by
  refine le_antisymm ?_ (le_comap_ringConGen _ _)
  trans (ringConGen (r on ⇑f) |>.comap f.symm.toNonUnitalRingHom).comap f.toNonUnitalRingHom
  · apply comap_mono
    grw [← le_comap_ringConGen]
    gcongr
    simp [Function.onFun, RingEquiv.coe_toNonUnitalRingHom']
  · rw [← comap_nonUnitalRingHomComp]
    simp

中文:
定理 comap_ringConGen_ringEquiv
  结论: {R R'} [非结合半环 R] [非结合半环 R']
  证明: by
  refine le_antisymm ?_ (le_comap_ringConGen _ _)
  trans (ringConGen (r on ⇑f) |>.comap f.symm.toNonUnitalRingHom).comap f.toNonUnitalRingHom
  · apply comap_mono
    grw [← le_comap_ringConGen]
    gcongr
    simp [Function.onFun, RingEquiv.coe_toNonUnitalRingHom']
  · rw [← comap_nonUnitalRingHomComp]
    simp

Depends on / 依赖: Function, Function.onFun, RingEquiv, RingEquiv.coe_toNonUnitalRingHom, coe_toNonUnitalRingHom, comap_mono, comap_nonUnitalRingHomComp, f.symm.toNonUnitalRingHom, f.toNonUnitalRingHom, le_antisymm, le_comap_ringConGen, ringConGen, toNonUnitalRingHom
-/
theorem comap_ringConGen_ringEquiv {R R'} [NonAssocSemiring R] [NonAssocSemiring R']
    (r : R' -> R' -> Prop) (f : R ≃+* R') :
    (ringConGen r).comap f = ringConGen (r on f) := by
  refine le_antisymm ?_ (le_comap_ringConGen _ _)
  trans (ringConGen (r on ⇑f) |>.comap f.symm.toNonUnitalRingHom).comap f.toNonUnitalRingHom
  · apply comap_mono
    grw [← le_comap_ringConGen]
    gcongr
    simp [Function.onFun, RingEquiv.coe_toNonUnitalRingHom']
  · rw [← comap_nonUnitalRingHomComp]
    simp

-- This one probably needs the RingCon version of `Setoid.comap_surjective`
proof_wanted comap_ringConGen_equiv
    {F} [FunLike F R' R] [MulHomClass F R' R] [AddHomClass F R' R] [EquivLike F R' R]
    (r : R -> R -> Prop) (f : F) :
    (ringConGen r).comap f = ringConGen (r on f)

end Lattice

end RingCon
