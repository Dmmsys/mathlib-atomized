/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.DFinsupp.Module
public import Mathlib.Data.Finsupp.SMul

/-!
# Conversion between `Finsupp` and homogeneous `DFinsupp`

This module provides conversions between `Finsupp` and `DFinsupp`.
It is in its own file since neither `Finsupp` or `DFinsupp` depend on each other.

## Main definitions

* "identity" maps between `Finsupp` and `DFinsupp`:
  * `Finsupp.toDFinsupp : (ι →₀ M) → (Π₀ i : ι, M)`
  * `DFinsupp.toFinsupp : (Π₀ i : ι, M) → (ι →₀ M)`
  * Bundled equiv versions of the above:
    * `finsuppEquivDFinsupp : (ι →₀ M) ≃ (Π₀ i : ι, M)`
    * `finsuppAddEquivDFinsupp : (ι →₀ M) ≃+ (Π₀ i : ι, M)`
    * `finsuppLequivDFinsupp R : (ι →₀ M) ≃ₗ[R] (Π₀ i : ι, M)`
* stronger versions of `Finsupp.split`:
  * `sigmaFinsuppEquivDFinsupp : ((Σ i, η i) →₀ N) ≃ (Π₀ i, (η i →₀ N))`
  * `sigmaFinsuppAddEquivDFinsupp : ((Σ i, η i) →₀ N) ≃+ (Π₀ i, (η i →₀ N))`
  * `sigmaFinsuppLequivDFinsupp : ((Σ i, η i) →₀ N) ≃ₗ[R] (Π₀ i, (η i →₀ N))`

## Theorems

The defining features of these operations is that they preserve the function and support:

* `Finsupp.toDFinsupp_coe`
* `Finsupp.toDFinsupp_support`
* `DFinsupp.toFinsupp_coe`
* `DFinsupp.toFinsupp_support`

and therefore map `Finsupp.single` to `DFinsupp.single` and vice versa:

* `Finsupp.toDFinsupp_single`
* `DFinsupp.toFinsupp_single`

as well as preserving arithmetic operations.

For the bundled equivalences, we provide lemmas that they reduce to `Finsupp.toDFinsupp`:

* `finsupp_add_equiv_dfinsupp_apply`
* `finsupp_lequiv_dfinsupp_apply`
* `finsupp_add_equiv_dfinsupp_symm_apply`
* `finsupp_lequiv_dfinsupp_symm_apply`

## Implementation notes

We provide `DFinsupp.toFinsupp` and `finsuppEquivDFinsupp` computably by adding
`[DecidableEq ι]` and `[Π m : M, Decidable (m ≠ 0)]` arguments. To aid with definitional unfolding,
these arguments are also present on the `noncomputable` equivs.
-/

@[expose] public section


variable {ι : Type*} {R : Type*} {M : Type*}

/-! ### Basic definitions and lemmas -/


section Defs

/--
Definition of `Finsupp.toDFinsupp` / `Finsupp.toDFinsupp` 的定义

English:
definition Finsupp.toDFinsupp
  signature: [Zero M] (f : ι ->₀ M)
  body: f
  support' :=
    Trunc.mk
      ⟨f.support.1, fun i => (Classical.em (f i = 0)).symm.imp_left Finsupp.mem_support_iff.mpr⟩

@[simp]

中文:
定义 Finsupp.toDFinsupp
  签名: [Zero M] (f : ι ->₀ M)
  定义体: f
  support' :=
    Trunc.mk
      ⟨f.support.1, fun i => (Classical.em (f i = 0)).symm.imp_left Finsupp.mem_support_iff.mpr⟩

@[simp]
-/
def Finsupp.toDFinsupp [Zero M] (f : ι ->₀ M) : Π₀ _ : ι, M where
  toFun := f
  support' :=
    Trunc.mk
      ⟨f.support.1, fun i => (Classical.em (f i = 0)).symm.imp_left Finsupp.mem_support_iff.mpr⟩

@[simp]
/--
theorem `Finsupp.toDFinsupp_coe` / 定理 `Finsupp.toDFinsupp_coe`

English:
theorem Finsupp.toDFinsupp_coe
  given: [Zero M] (f : ι ->₀ M)
  statement: ⇑f.toDFinsupp = f
  proof: rfl

中文:
定理 Finsupp.toDFinsupp_coe
  条件: [Zero M] (f : ι ->₀ M)
  结论: ⇑f.toDFinsupp = f
  证明: rfl
-/
theorem Finsupp.toDFinsupp_coe [Zero M] (f : ι ->₀ M) : ⇑f.toDFinsupp = f :=
  rfl

section

variable [DecidableEq ι] [Zero M]

@[simp]
/--
theorem `Finsupp.toDFinsupp_single` / 定理 `Finsupp.toDFinsupp_single`

English:
theorem Finsupp.toDFinsupp_single
  given: (i : ι) (m : M)
  proof: by
  ext
  simp [Finsupp.single_apply, DFinsupp.single_apply]

中文:
定理 Finsupp.toDFinsupp_single
  条件: (i : ι) (m : M)
  证明: by
  ext
  simp [Finsupp.single_apply, DFinsupp.single_apply]

Depends on / 依赖: DFinsupp, DFinsupp.single_apply, Finsupp, Finsupp.single_apply, single_apply
-/
theorem Finsupp.toDFinsupp_single (i : ι) (m : M) :
    (Finsupp.single i m).toDFinsupp = DFinsupp.single i m := by
  ext
  simp [Finsupp.single_apply, DFinsupp.single_apply]

variable [forall m : M, Decidable (m != 0)]

@[simp]
/--
theorem `toDFinsupp_support` / 定理 `toDFinsupp_support`

English:
theorem toDFinsupp_support
  given: (f : ι ->₀ M)
  statement: f.toDFinsupp.support = f.support
  proof: by
  ext
  simp

中文:
定理 toDFinsupp_support
  条件: (f : ι ->₀ M)
  结论: f.toDFinsupp.support = f.support
  证明: by
  ext
  simp
-/
theorem toDFinsupp_support (f : ι ->₀ M) : f.toDFinsupp.support = f.support := by
  ext
  simp

/--
Definition of `DFinsupp.toFinsupp` / `DFinsupp.toFinsupp` 的定义

English:
definition DFinsupp.toFinsupp
  signature: (f : Π₀ _ : ι, M)
  body: ⟨f.support, f, fun i => by simp only [DFinsupp.mem_support_iff]⟩

@[simp]

中文:
定义 DFinsupp.toFinsupp
  签名: (f : Π₀ _ : ι, M)
  定义体: ⟨f.support, f, fun i => by simp only [DFinsupp.mem_support_iff]⟩

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.mem_support_iff, f.support, mem_support_iff, support
-/
def DFinsupp.toFinsupp (f : Π₀ _ : ι, M) : ι ->₀ M :=
  ⟨f.support, f, fun i => by simp only [DFinsupp.mem_support_iff]⟩

@[simp]
/--
theorem `DFinsupp.toFinsupp_coe` / 定理 `DFinsupp.toFinsupp_coe`

English:
theorem DFinsupp.toFinsupp_coe
  given: (f : Π₀ _ : ι, M)
  statement: ⇑f.toFinsupp = f
  proof: rfl

@[simp]

中文:
定理 DFinsupp.toFinsupp_coe
  条件: (f : Π₀ _ : ι, M)
  结论: ⇑f.toFinsupp = f
  证明: rfl

@[simp]
-/
theorem DFinsupp.toFinsupp_coe (f : Π₀ _ : ι, M) : ⇑f.toFinsupp = f :=
  rfl

@[simp]
/--
theorem `DFinsupp.toFinsupp_support` / 定理 `DFinsupp.toFinsupp_support`

English:
theorem DFinsupp.toFinsupp_support
  given: (f : Π₀ _ : ι, M)
  statement: f.toFinsupp.support = f.support
  proof: by
  ext
  simp

@[simp]

中文:
定理 DFinsupp.toFinsupp_support
  条件: (f : Π₀ _ : ι, M)
  结论: f.toFinsupp.support = f.support
  证明: by
  ext
  simp

@[simp]
-/
theorem DFinsupp.toFinsupp_support (f : Π₀ _ : ι, M) : f.toFinsupp.support = f.support := by
  ext
  simp

@[simp]
/--
theorem `DFinsupp.toFinsupp_single` / 定理 `DFinsupp.toFinsupp_single`

English:
theorem DFinsupp.toFinsupp_single
  given: (i : ι) (m : M)
  proof: by
  ext
  simp [Finsupp.single_apply, DFinsupp.single_apply]

@[simp]

中文:
定理 DFinsupp.toFinsupp_single
  条件: (i : ι) (m : M)
  证明: by
  ext
  simp [Finsupp.single_apply, DFinsupp.single_apply]

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.single_apply, Finsupp, Finsupp.single_apply, single_apply
-/
theorem DFinsupp.toFinsupp_single (i : ι) (m : M) :
    (DFinsupp.single i m : Π₀ _ : ι, M).toFinsupp = Finsupp.single i m := by
  ext
  simp [Finsupp.single_apply, DFinsupp.single_apply]

@[simp]
/--
theorem `Finsupp.toDFinsupp_toFinsupp` / 定理 `Finsupp.toDFinsupp_toFinsupp`

English:
theorem Finsupp.toDFinsupp_toFinsupp
  given: (f : ι ->₀ M)
  statement: f.toDFinsupp.toFinsupp = f
  proof: DFunLike.coe_injective rfl

@[simp]

中文:
定理 Finsupp.toDFinsupp_toFinsupp
  条件: (f : ι ->₀ M)
  结论: f.toDFinsupp.toFinsupp = f
  证明: DFunLike.coe_injective rfl

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem Finsupp.toDFinsupp_toFinsupp (f : ι ->₀ M) : f.toDFinsupp.toFinsupp = f :=
  DFunLike.coe_injective rfl

@[simp]
/--
theorem `DFinsupp.toFinsupp_toDFinsupp` / 定理 `DFinsupp.toFinsupp_toDFinsupp`

English:
theorem DFinsupp.toFinsupp_toDFinsupp
  given: (f : Π₀ _ : ι, M)
  statement: f.toFinsupp.toDFinsupp = f
  proof: DFunLike.coe_injective rfl

中文:
定理 DFinsupp.toFinsupp_toDFinsupp
  条件: (f : Π₀ _ : ι, M)
  结论: f.toFinsupp.toDFinsupp = f
  证明: DFunLike.coe_injective rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem DFinsupp.toFinsupp_toDFinsupp (f : Π₀ _ : ι, M) : f.toFinsupp.toDFinsupp = f :=
  DFunLike.coe_injective rfl

end

end Defs

/-! ### Lemmas about arithmetic operations -/


section Lemmas

namespace Finsupp

@[simp]
/--
theorem `toDFinsupp_zero` / 定理 `toDFinsupp_zero`

English:
theorem toDFinsupp_zero
  given: [Zero M]
  statement: (0 : ι ->₀ M).toDFinsupp = 0
  proof: DFunLike.coe_injective rfl

@[simp]

中文:
定理 toDFinsupp_zero
  条件: [Zero M]
  结论: (0 : ι ->₀ M).toDFinsupp = 0
  证明: DFunLike.coe_injective rfl

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem toDFinsupp_zero [Zero M] : (0 : ι ->₀ M).toDFinsupp = 0 :=
  DFunLike.coe_injective rfl

@[simp]
/--
theorem `toDFinsupp_add` / 定理 `toDFinsupp_add`

English:
theorem toDFinsupp_add
  given: [AddZeroClass M] (f g : ι ->₀ M)
  proof: DFunLike.coe_injective rfl

@[simp]

中文:
定理 toDFinsupp_add
  条件: [AddZeroClass M] (f g : ι ->₀ M)
  证明: DFunLike.coe_injective rfl

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem toDFinsupp_add [AddZeroClass M] (f g : ι ->₀ M) :
    (f + g).toDFinsupp = f.toDFinsupp + g.toDFinsupp :=
  DFunLike.coe_injective rfl

@[simp]
/--
theorem `toDFinsupp_neg` / 定理 `toDFinsupp_neg`

English:
theorem toDFinsupp_neg
  given: [AddGroup M] (f : ι ->₀ M)
  statement: (-f).toDFinsupp = -f.toDFinsupp
  proof: DFunLike.coe_injective rfl

@[simp]

中文:
定理 toDFinsupp_neg
  条件: [AddGroup M] (f : ι ->₀ M)
  结论: (-f).toDFinsupp = -f.toDFinsupp
  证明: DFunLike.coe_injective rfl

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem toDFinsupp_neg [AddGroup M] (f : ι ->₀ M) : (-f).toDFinsupp = -f.toDFinsupp :=
  DFunLike.coe_injective rfl

@[simp]
/--
theorem `toDFinsupp_sub` / 定理 `toDFinsupp_sub`

English:
theorem toDFinsupp_sub
  given: [AddGroup M] (f g : ι ->₀ M)
  proof: DFunLike.coe_injective rfl

@[simp]

中文:
定理 toDFinsupp_sub
  条件: [AddGroup M] (f g : ι ->₀ M)
  证明: DFunLike.coe_injective rfl

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem toDFinsupp_sub [AddGroup M] (f g : ι ->₀ M) :
    (f - g).toDFinsupp = f.toDFinsupp - g.toDFinsupp :=
  DFunLike.coe_injective rfl

@[simp]
/--
theorem `toDFinsupp_smul` / 定理 `toDFinsupp_smul`

English:
theorem toDFinsupp_smul
  given: [Monoid R] [AddMonoid M] [DistribMulAction R M] (r : R) (f : ι ->₀ M)
  proof: DFunLike.coe_injective rfl

中文:
定理 toDFinsupp_smul
  条件: [Monoid R] [AddMonoid M] [DistribMulAction R M] (r : R) (f : ι ->₀ M)
  证明: DFunLike.coe_injective rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem toDFinsupp_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] (r : R) (f : ι ->₀ M) :
    (r • f).toDFinsupp = r • f.toDFinsupp :=
  DFunLike.coe_injective rfl

end Finsupp

namespace DFinsupp

variable [DecidableEq ι]

@[simp]
/--
theorem `toFinsupp_zero` / 定理 `toFinsupp_zero`

English:
theorem toFinsupp_zero
  given: [Zero M] [forall m : M, Decidable (m != 0)]
  statement: toFinsupp 0 = (0 : ι ->₀ M)
  proof: DFunLike.coe_injective rfl

@[simp]

中文:
定理 toFinsupp_zero
  条件: [Zero M] [对任意 m : M, Decidable (m != 0)]
  结论: toFinsupp 0 = (0 : ι ->₀ M)
  证明: DFunLike.coe_injective rfl

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem toFinsupp_zero [Zero M] [forall m : M, Decidable (m != 0)] : toFinsupp 0 = (0 : ι ->₀ M) :=
  DFunLike.coe_injective rfl

@[simp]
/--
theorem `toFinsupp_add` / 定理 `toFinsupp_add`

English:
theorem toFinsupp_add
  given: [AddZeroClass M] [forall m : M, Decidable (m != 0)] (f g : Π₀ _ : ι, M)
  proof: DFunLike.coe_injective DFinsupp.coe_add _ _

@[simp]

中文:
定理 toFinsupp_add
  条件: [AddZeroClass M] [对任意 m : M, Decidable (m != 0)] (f g : Π₀ _ : ι, M)
  证明: DFunLike.coe_injective DFinsupp.coe_add _ _

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.coe_add, DFunLike, DFunLike.coe_injective, coe_add, coe_injective
-/
theorem toFinsupp_add [AddZeroClass M] [forall m : M, Decidable (m != 0)] (f g : Π₀ _ : ι, M) :
    (toFinsupp (f + g) : ι ->₀ M) = toFinsupp f + toFinsupp g :=
DFunLike.coe_injective DFinsupp.coe_add _ _

@[simp]
/--
theorem `toFinsupp_neg` / 定理 `toFinsupp_neg`

English:
theorem toFinsupp_neg
  given: [AddGroup M] [forall m : M, Decidable (m != 0)] (f : Π₀ _ : ι, M)
  proof: DFunLike.coe_injective DFinsupp.coe_neg _

@[simp]

中文:
定理 toFinsupp_neg
  条件: [AddGroup M] [对任意 m : M, Decidable (m != 0)] (f : Π₀ _ : ι, M)
  证明: DFunLike.coe_injective DFinsupp.coe_neg _

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.coe_neg, DFunLike, DFunLike.coe_injective, coe_injective, coe_neg
-/
theorem toFinsupp_neg [AddGroup M] [forall m : M, Decidable (m != 0)] (f : Π₀ _ : ι, M) :
    (toFinsupp (-f) : ι ->₀ M) = -toFinsupp f :=
DFunLike.coe_injective DFinsupp.coe_neg _

@[simp]
/--
theorem `toFinsupp_sub` / 定理 `toFinsupp_sub`

English:
theorem toFinsupp_sub
  given: [AddGroup M] [forall m : M, Decidable (m != 0)] (f g : Π₀ _ : ι, M)
  proof: DFunLike.coe_injective DFinsupp.coe_sub _ _

@[simp]

中文:
定理 toFinsupp_sub
  条件: [AddGroup M] [对任意 m : M, Decidable (m != 0)] (f g : Π₀ _ : ι, M)
  证明: DFunLike.coe_injective DFinsupp.coe_sub _ _

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.coe_sub, DFunLike, DFunLike.coe_injective, coe_injective, coe_sub
-/
theorem toFinsupp_sub [AddGroup M] [forall m : M, Decidable (m != 0)] (f g : Π₀ _ : ι, M) :
    (toFinsupp (f - g) : ι ->₀ M) = toFinsupp f - toFinsupp g :=
DFunLike.coe_injective DFinsupp.coe_sub _ _

@[simp]
/--
theorem `toFinsupp_smul` / 定理 `toFinsupp_smul`

English:
theorem toFinsupp_smul
  statement: [Monoid R] [AddMonoid M] [DistribMulAction R M] [forall m : M, Decidable (m != 0)]
  proof: DFunLike.coe_injective DFinsupp.coe_smul _ _

中文:
定理 toFinsupp_smul
  结论: [Monoid R] [AddMonoid M] [DistribMulAction R M] [对任意 m : M, Decidable (m != 0)]
  证明: DFunLike.coe_injective DFinsupp.coe_smul _ _

Depends on / 依赖: DFinsupp, DFinsupp.coe_smul, DFunLike, DFunLike.coe_injective, coe_injective, coe_smul
-/
theorem toFinsupp_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] [forall m : M, Decidable (m != 0)]
    (r : R) (f : Π₀ _ : ι, M) : (toFinsupp (r • f) : ι ->₀ M) = r • toFinsupp f :=
DFunLike.coe_injective DFinsupp.coe_smul _ _

end DFinsupp

end Lemmas

/-! ### Bundled `Equiv`s -/


section Equivs

/-- `Finsupp.toDFinsupp` and `DFinsupp.toFinsupp` together form an equiv. -/
@[simps -fullyApplied]
/--
Definition of `finsuppEquivDFinsupp` / `finsuppEquivDFinsupp` 的定义

English:
definition finsuppEquivDFinsupp
  signature: [DecidableEq ι] [Zero M] [forall m : M, Decidable (m != 0)]
  body: Finsupp.toDFinsupp
  invFun := DFinsupp.toFinsupp
  left_inv := Finsupp.toDFinsupp_toFinsupp
  right_inv := DFinsupp.toFinsupp_toDFinsupp

中文:
定义 finsuppEquivDFinsupp
  签名: [DecidableEq ι] [Zero M] [对任意 m : M, Decidable (m != 0)]
  定义体: Finsupp.toDFinsupp
  invFun := DFinsupp.toFinsupp
  left_inv := Finsupp.toDFinsupp_toFinsupp
  right_inv := DFinsupp.toFinsupp_toDFinsupp

Depends on / 依赖: Finsupp, Finsupp.toDFinsupp, toDFinsupp
-/
def finsuppEquivDFinsupp [DecidableEq ι] [Zero M] [forall m : M, Decidable (m != 0)] :
    (ι ->₀ M) ≃ Π₀ _ : ι, M where
  toFun := Finsupp.toDFinsupp
  invFun := DFinsupp.toFinsupp
  left_inv := Finsupp.toDFinsupp_toFinsupp
  right_inv := DFinsupp.toFinsupp_toDFinsupp

/-- The additive version of `finsupp.toFinsupp`. Note that this is `noncomputable` because
`Finsupp.add` is noncomputable. -/
@[simps -fullyApplied]
/--
Definition of `finsuppAddEquivDFinsupp` / `finsuppAddEquivDFinsupp` 的定义

English:
definition finsuppAddEquivDFinsupp
  signature: [DecidableEq ι] [AddZeroClass M] [forall m : M, Decidable (m != 0)]
  body: { finsuppEquivDFinsupp with
    toFun := Finsupp.toDFinsupp
    invFun := DFinsupp.toFinsupp
    map_add' := Finsupp.toDFinsupp_add }

中文:
定义 finsuppAddEquivDFinsupp
  签名: [DecidableEq ι] [AddZeroClass M] [对任意 m : M, Decidable (m != 0)]
  定义体: { finsuppEquivDFinsupp with
    toFun := Finsupp.toDFinsupp
    invFun := DFinsupp.toFinsupp
    map_add' := Finsupp.toDFinsupp_add }

Depends on / 依赖: DFinsupp, DFinsupp.toFinsupp, Finsupp, Finsupp.toDFinsupp, Finsupp.toDFinsupp_add, finsuppEquivDFinsupp, invFun, map_add, toDFinsupp, toDFinsupp_add, toFinsupp
-/
def finsuppAddEquivDFinsupp [DecidableEq ι] [AddZeroClass M] [forall m : M, Decidable (m != 0)] :
    (ι ->₀ M) ≃+ Π₀ _ : ι, M :=
  { finsuppEquivDFinsupp with
    toFun := Finsupp.toDFinsupp
    invFun := DFinsupp.toFinsupp
    map_add' := Finsupp.toDFinsupp_add }

variable (R)

/--
Definition of `finsuppLequivDFinsupp` / `finsuppLequivDFinsupp` 的定义

English:
definition finsuppLequivDFinsupp
  signature: [DecidableEq ι] [Semiring R] [AddCommMonoid M]
  body: { finsuppEquivDFinsupp with
    toFun := Finsupp.toDFinsupp
    invFun := DFinsupp.toFinsupp
    map_smul' := Finsupp.toDFinsupp_smul
    map_add' := Finsupp.toDFinsupp_add }

@[simp]

中文:
定义 finsuppLequivDFinsupp
  签名: [DecidableEq ι] [Semiring R] [AddCommMonoid M]
  定义体: { finsuppEquivDFinsupp with
    toFun := Finsupp.toDFinsupp
    invFun := DFinsupp.toFinsupp
    map_smul' := Finsupp.toDFinsupp_smul
    map_add' := Finsupp.toDFinsupp_add }

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.toFinsupp, Finsupp, Finsupp.toDFinsupp, Finsupp.toDFinsupp_add, Finsupp.toDFinsupp_smul, finsuppEquivDFinsupp, invFun, map_add, map_smul, toDFinsupp, toDFinsupp_add, toDFinsupp_smul, toFinsupp
-/
def finsuppLequivDFinsupp [DecidableEq ι] [Semiring R] [AddCommMonoid M]
    [forall m : M, Decidable (m != 0)] [Module R M] : (ι ->₀ M) ≃ₗ[R] Π₀ _ : ι, M :=
  { finsuppEquivDFinsupp with
    toFun := Finsupp.toDFinsupp
    invFun := DFinsupp.toFinsupp
    map_smul' := Finsupp.toDFinsupp_smul
    map_add' := Finsupp.toDFinsupp_add }

@[simp]
/--
theorem `finsuppLequivDFinsupp_apply_apply` / 定理 `finsuppLequivDFinsupp_apply_apply`

English:
theorem finsuppLequivDFinsupp_apply_apply
  statement: [DecidableEq ι] [Semiring R] [AddCommMonoid M]
  proof: rfl

@[simp]

中文:
定理 finsuppLequivDFinsupp_apply_apply
  结论: [DecidableEq ι] [Semiring R] [AddCommMonoid M]
  证明: rfl

@[simp]

Depends on / 依赖: Finsupp, Finsupp.toDFinsupp, toDFinsupp
-/
theorem finsuppLequivDFinsupp_apply_apply [DecidableEq ι] [Semiring R] [AddCommMonoid M]
    [forall m : M, Decidable (m != 0)] [Module R M] :
    (↑(finsuppLequivDFinsupp (M := M) R) : (ι ->₀ M) -> _) = Finsupp.toDFinsupp := rfl

@[simp]
/--
theorem `finsuppLequivDFinsupp_symm_apply` / 定理 `finsuppLequivDFinsupp_symm_apply`

English:
theorem finsuppLequivDFinsupp_symm_apply
  statement: [DecidableEq ι] [Semiring R] [AddCommMonoid M]
  proof: rfl

noncomputable section Sigma

中文:
定理 finsuppLequivDFinsupp_symm_apply
  结论: [DecidableEq ι] [Semiring R] [AddCommMonoid M]
  证明: rfl

noncomputable section Sigma

Depends on / 依赖: DFinsupp, DFinsupp.toFinsupp, toFinsupp
-/
theorem finsuppLequivDFinsupp_symm_apply [DecidableEq ι] [Semiring R] [AddCommMonoid M]
    [forall m : M, Decidable (m != 0)] [Module R M] :
    ↑(LinearEquiv.symm (finsuppLequivDFinsupp (ι := ι) (M := M) R)) = DFinsupp.toFinsupp :=
  rfl

noncomputable section Sigma

/-! ### Stronger versions of `Finsupp.split` -/

variable {η : ι -> Type*} {N : Type*} [Semiring R]

open Finsupp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sigmaFinsuppEquivDFinsupp` / `sigmaFinsuppEquivDFinsupp` 的定义

English:
definition sigmaFinsuppEquivDFinsupp
  signature: [Zero N]
  body: ⟨split f, Trunc.mk ⟨(splitSupport f : Finset ι).val, fun i => by
          rw [← Finset.mem_def]; rw [mem_splitSupport_iff_nonzero]
          exact (em _).symm⟩⟩
  invFun f := by
    haveI := Classical.decEq ι
    haveI := fun i => Classical.decEq (η i ->₀ N)
    refine
      onFinset (Finset.sigma 

中文:
定义 sigmaFinsuppEquivDFinsupp
  签名: [Zero N]
  定义体: ⟨split f, Trunc.mk ⟨(splitSupport f : Finset ι).val, fun i => by
          rw [← Finset.mem_def]; rw [mem_splitSupport_iff_nonzero]
          exact (em _).symm⟩⟩
  invFun f := by
    haveI := Classical.decEq ι
    haveI := fun i => Classical.decEq (η i ->₀ N)
    refine
      onFinset (Finset.sigma 

Depends on / 依赖: Classical, Classical.decEq, DFinsupp, DFinsupp.mem_support_toFun, Finset, Finset.mem_def, Finset.mem_sigma.mpr, Finset.sigma, Pi.zero_apply, Trunc.mk, coe_zero, f.support, invFun, mem_def, mem_sigma, mem_splitSupport_iff_nonzero, mem_support_iff, mem_support_iff.mpr, mem_support_toFun, not_true
-/
def sigmaFinsuppEquivDFinsupp [Zero N] : ((Σ i, η i) ->₀ N) ≃ Π₀ i, η i ->₀ N where
  toFun f := ⟨split f, Trunc.mk ⟨(splitSupport f : Finset ι).val, fun i => by
          rw [← Finset.mem_def]; rw [mem_splitSupport_iff_nonzero]
          exact (em _).symm⟩⟩
  invFun f := by
    haveI := Classical.decEq ι
    haveI := fun i => Classical.decEq (η i ->₀ N)
    refine
      onFinset (Finset.sigma f.support fun j => (f j).support) (fun ji => f ji.1 ji.2) fun g hg =>
        Finset.mem_sigma.mpr ⟨?_, mem_support_iff.mpr hg⟩
    simp only [Ne, DFinsupp.mem_support_toFun]
    intro h
    dsimp at hg
    rw [h] at hg
    simp only [coe_zero, Pi.zero_apply, not_true] at hg
  left_inv f := by ext; simp [split]
  right_inv f := by ext; simp [split]

@[simp]
/--
theorem `sigmaFinsuppEquivDFinsupp_apply` / 定理 `sigmaFinsuppEquivDFinsupp_apply`

English:
theorem sigmaFinsuppEquivDFinsupp_apply
  given: [Zero N] (f : (Σ i, η i) ->₀ N)
  proof: rfl

@[simp]

中文:
定理 sigmaFinsuppEquivDFinsupp_apply
  条件: [Zero N] (f : (Σ i, η i) ->₀ N)
  证明: rfl

@[simp]
-/
theorem sigmaFinsuppEquivDFinsupp_apply [Zero N] (f : (Σ i, η i) ->₀ N) :
    (sigmaFinsuppEquivDFinsupp f : forall i, η i ->₀ N) = Finsupp.split f :=
  rfl

@[simp]
/--
theorem `sigmaFinsuppEquivDFinsupp_symm_apply` / 定理 `sigmaFinsuppEquivDFinsupp_symm_apply`

English:
theorem sigmaFinsuppEquivDFinsupp_symm_apply
  given: [Zero N] (f : Π₀ i, η i ->₀ N) (s : Σ i, η i)
  proof: rfl

@[simp]

中文:
定理 sigmaFinsuppEquivDFinsupp_symm_apply
  条件: [Zero N] (f : Π₀ i, η i ->₀ N) (s : Σ i, η i)
  证明: rfl

@[simp]
-/
theorem sigmaFinsuppEquivDFinsupp_symm_apply [Zero N] (f : Π₀ i, η i ->₀ N) (s : Σ i, η i) :
    (sigmaFinsuppEquivDFinsupp.symm f : (Σ i, η i) ->₀ N) s = f s.1 s.2 :=
  rfl

@[simp]
/--
theorem `sigmaFinsuppEquivDFinsupp_support` / 定理 `sigmaFinsuppEquivDFinsupp_support`

English:
theorem sigmaFinsuppEquivDFinsupp_support
  statement: [DecidableEq ι] [Zero N]
  proof: by
  ext
  rw [DFinsupp.mem_support_toFun]
  exact (Finsupp.mem_splitSupport_iff_nonzero _ _).symm

@[simp]

中文:
定理 sigmaFinsuppEquivDFinsupp_support
  结论: [DecidableEq ι] [Zero N]
  证明: by
  ext
  rw [DFinsupp.mem_support_toFun]
  exact (Finsupp.mem_splitSupport_iff_nonzero _ _).symm

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.mem_support_toFun, Finsupp, Finsupp.mem_splitSupport_iff_nonzero, mem_splitSupport_iff_nonzero, mem_support_toFun
-/
theorem sigmaFinsuppEquivDFinsupp_support [DecidableEq ι] [Zero N]
    [forall (i : ι) (x : η i ->₀ N), Decidable (x != 0)] (f : (Σ i, η i) ->₀ N) :
    (sigmaFinsuppEquivDFinsupp f).support = Finsupp.splitSupport f := by
  ext
  rw [DFinsupp.mem_support_toFun]
  exact (Finsupp.mem_splitSupport_iff_nonzero _ _).symm

@[simp]
/--
theorem `sigmaFinsuppEquivDFinsupp_single` / 定理 `sigmaFinsuppEquivDFinsupp_single`

English:
theorem sigmaFinsuppEquivDFinsupp_single
  given: [DecidableEq ι] [Zero N] (a : Σ i, η i) (n : N)
  proof: by
  obtain ⟨i, a⟩ := a
  ext j b
  by_cases h : i = j
  · subst h
    classical simp [split_apply, Finsupp.single_apply]
  suffices Finsupp.single (⟨i, a⟩ : Σ i, η i) n ⟨j, b⟩ = 0 by simp [split_apply, dif_neg h, this]
  have H : (⟨i, a⟩ : Σ i, η i) != ⟨j, b⟩ := by simp [h]
  classical rw [Finsupp.

中文:
定理 sigmaFinsuppEquivDFinsupp_single
  条件: [DecidableEq ι] [Zero N] (a : Σ i, η i) (n : N)
  证明: by
  obtain ⟨i, a⟩ := a
  ext j b
  by_cases h : i = j
  · subst h
    classical simp [split_apply, Finsupp.single_apply]
  suffices Finsupp.single (⟨i, a⟩ : Σ i, η i) n ⟨j, b⟩ = 0 by simp [split_apply, dif_neg h, this]
  have H : (⟨i, a⟩ : Σ i, η i) != ⟨j, b⟩ := by simp [h]
  classical rw [Finsupp.

Depends on / 依赖: Finsupp, Finsupp.single, Finsupp.single_apply, classical, dif_neg, if_neg, single, single_apply, split_apply
-/
theorem sigmaFinsuppEquivDFinsupp_single [DecidableEq ι] [Zero N] (a : Σ i, η i) (n : N) :
    sigmaFinsuppEquivDFinsupp (Finsupp.single a n) =
      @DFinsupp.single _ (fun i => η i ->₀ N) _ _ a.1 (Finsupp.single a.2 n) := by
  obtain ⟨i, a⟩ := a
  ext j b
  by_cases h : i = j
  · subst h
    classical simp [split_apply, Finsupp.single_apply]
  suffices Finsupp.single (⟨i, a⟩ : Σ i, η i) n ⟨j, b⟩ = 0 by simp [split_apply, dif_neg h, this]
  have H : (⟨i, a⟩ : Σ i, η i) != ⟨j, b⟩ := by simp [h]
  classical rw [Finsupp.single_apply, if_neg H]

-- Without this Lean fails to find the `AddZeroClass` instance on `Π₀ i, (η i →₀ N)`.
attribute [-instance] Finsupp.instZero

@[simp]
/--
theorem `sigmaFinsuppEquivDFinsupp_add` / 定理 `sigmaFinsuppEquivDFinsupp_add`

English:
theorem sigmaFinsuppEquivDFinsupp_add
  given: [AddZeroClass N] (f g : (Σ i, η i) ->₀ N)
  proof: by
  ext
  rfl

中文:
定理 sigmaFinsuppEquivDFinsupp_add
  条件: [AddZeroClass N] (f g : (Σ i, η i) ->₀ N)
  证明: by
  ext
  rfl
-/
theorem sigmaFinsuppEquivDFinsupp_add [AddZeroClass N] (f g : (Σ i, η i) ->₀ N) :
    sigmaFinsuppEquivDFinsupp (f + g) =
      (sigmaFinsuppEquivDFinsupp f + sigmaFinsuppEquivDFinsupp g : Π₀ i : ι, η i ->₀ N) := by
  ext
  rfl

/-- `Finsupp.split` is an additive equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
@[simps]
/--
Definition of `sigmaFinsuppAddEquivDFinsupp` / `sigmaFinsuppAddEquivDFinsupp` 的定义

English:
definition sigmaFinsuppAddEquivDFinsupp
  signature: [AddZeroClass N]
  body: { sigmaFinsuppEquivDFinsupp with
    toFun := sigmaFinsuppEquivDFinsupp
    invFun := sigmaFinsuppEquivDFinsupp.symm
    map_add' := sigmaFinsuppEquivDFinsupp_add }

中文:
定义 sigmaFinsuppAddEquivDFinsupp
  签名: [AddZeroClass N]
  定义体: { sigmaFinsuppEquivDFinsupp with
    toFun := sigmaFinsuppEquivDFinsupp
    invFun := sigmaFinsuppEquivDFinsupp.symm
    map_add' := sigmaFinsuppEquivDFinsupp_add }

Depends on / 依赖: invFun, map_add, sigmaFinsuppEquivDFinsupp, sigmaFinsuppEquivDFinsupp.symm, sigmaFinsuppEquivDFinsupp_add
-/
def sigmaFinsuppAddEquivDFinsupp [AddZeroClass N] : ((Σ i, η i) ->₀ N) ≃+ Π₀ i, η i ->₀ N :=
  { sigmaFinsuppEquivDFinsupp with
    toFun := sigmaFinsuppEquivDFinsupp
    invFun := sigmaFinsuppEquivDFinsupp.symm
    map_add' := sigmaFinsuppEquivDFinsupp_add }

attribute [-instance] Finsupp.instAddZeroClass

@[simp]
/--
theorem `sigmaFinsuppEquivDFinsupp_smul` / 定理 `sigmaFinsuppEquivDFinsupp_smul`

English:
theorem sigmaFinsuppEquivDFinsupp_smul
  statement: {R} [Monoid R] [AddMonoid N] [DistribMulAction R N] (r : R)
  proof: by
  ext
  rfl

中文:
定理 sigmaFinsuppEquivDFinsupp_smul
  结论: {R} [Monoid R] [AddMonoid N] [DistribMulAction R N] (r : R)
  证明: by
  ext
  rfl
-/
theorem sigmaFinsuppEquivDFinsupp_smul {R} [Monoid R] [AddMonoid N] [DistribMulAction R N] (r : R)
    (f : (Σ i, η i) ->₀ N) :
    sigmaFinsuppEquivDFinsupp (r • f) = r • sigmaFinsuppEquivDFinsupp f := by
  ext
  rfl

attribute [-instance] Finsupp.instAddMonoid

/-- `Finsupp.split` is a linear equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
@[simps]
/--
Definition of `sigmaFinsuppLequivDFinsupp` / `sigmaFinsuppLequivDFinsupp` 的定义

English:
definition sigmaFinsuppLequivDFinsupp
  signature: [AddCommMonoid N] [Module R N]
  body: { sigmaFinsuppAddEquivDFinsupp with
    map_smul' := sigmaFinsuppEquivDFinsupp_smul }

中文:
定义 sigmaFinsuppLequivDFinsupp
  签名: [AddCommMonoid N] [Module R N]
  定义体: { sigmaFinsuppAddEquivDFinsupp with
    map_smul' := sigmaFinsuppEquivDFinsupp_smul }

Depends on / 依赖: map_smul, sigmaFinsuppAddEquivDFinsupp, sigmaFinsuppEquivDFinsupp_smul
-/
def sigmaFinsuppLequivDFinsupp [AddCommMonoid N] [Module R N] :
    ((Σ i, η i) ->₀ N) ≃ₗ[R] Π₀ i, η i ->₀ N :=
  { sigmaFinsuppAddEquivDFinsupp with
    map_smul' := sigmaFinsuppEquivDFinsupp_smul }

end Sigma

end Equivs
