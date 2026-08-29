/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.End
public import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# Isomorphism between `FreeAbelianGroup X` and `X →₀ ℤ`

In this file we construct the canonical isomorphism between `FreeAbelianGroup X` and `X →₀ ℤ`.
We use this to transport the notion of `support` from `Finsupp` to `FreeAbelianGroup`.

## Main declarations

- `FreeAbelianGroup.equivFinsupp`: group isomorphism between `FreeAbelianGroup X` and `X →₀ ℤ`
- `FreeAbelianGroup.coeff`: the multiplicity of `x : X` in `a : FreeAbelianGroup X`
- `FreeAbelianGroup.support`: the finset of `x : X` that occur in `a : FreeAbelianGroup X`
-/

@[expose] public section

assert_not_exists Cardinal Module.Basis

noncomputable section

variable {X : Type*}

/--
Definition of `FreeAbelianGroup.toFinsupp` / `FreeAbelianGroup.toFinsupp` 的定义

English:
definition FreeAbelianGroup.toFinsupp
  signature: : FreeAbelianGroup X ->+ X ->₀ Int
  body: FreeAbelianGroup.lift fun x => Finsupp.single x (1 : Int)

中文:
定义 自由交换群.toFinsupp
  签名: : 自由交换群 X ->+ X ->₀ 整数
  定义体: FreeAbelianGroup.lift fun x => Finsupp.single x (1 : Int)

Depends on / 依赖: Finsupp, Finsupp.single, FreeAbelianGroup, FreeAbelianGroup.lift, single
-/
def FreeAbelianGroup.toFinsupp : FreeAbelianGroup X ->+ X ->₀ Int :=
  FreeAbelianGroup.lift fun x => Finsupp.single x (1 : Int)

/--
Definition of `Finsupp.toFreeAbelianGroup` / `Finsupp.toFreeAbelianGroup` 的定义

English:
definition Finsupp.toFreeAbelianGroup
  signature: : (X ->₀ Int) ->+ FreeAbelianGroup X
  body: Finsupp.liftAddHom fun x => (smulAddHom Int (FreeAbelianGroup X)).flip (FreeAbelianGroup.of x)

中文:
定义 有限支撑.toFreeAbelianGroup
  签名: : (X ->₀ 整数) ->+ 自由交换群 X
  定义体: Finsupp.liftAddHom fun x => (smulAddHom Int (FreeAbelianGroup X)).flip (FreeAbelianGroup.of x)

Depends on / 依赖: Finsupp, Finsupp.liftAddHom, FreeAbelianGroup, FreeAbelianGroup.of, liftAddHom, smulAddHom
-/
def Finsupp.toFreeAbelianGroup : (X ->₀ Int) ->+ FreeAbelianGroup X :=
  Finsupp.liftAddHom fun x => (smulAddHom Int (FreeAbelianGroup X)).flip (FreeAbelianGroup.of x)

/--
lemma `FreeAbelianGroup.toFinsupp_of` / 引理 `FreeAbelianGroup.toFinsupp_of`

English:
lemma FreeAbelianGroup.toFinsupp_of
  given: (x : X)
  statement: toFinsupp (of x) = .single x 1
  proof: by
  simp [toFinsupp]

中文:
引理 自由交换群.toFinsupp_of
  条件: (x : X)
  结论: toFinsupp (of x) = .single x 1
  证明: by
  simp [toFinsupp]
-/
@[simp] lemma FreeAbelianGroup.toFinsupp_of (x : X) : toFinsupp (of x) = .single x 1 := by
  simp [toFinsupp]

/--
lemma `Finsupp.toFreeAbelianGroup_single` / 引理 `Finsupp.toFreeAbelianGroup_single`

English:
lemma Finsupp.toFreeAbelianGroup_single
  given: (x : X) (n : Int)
  proof: by simp [toFreeAbelianGroup]

中文:
引理 有限支撑.toFreeAbelianGroup_single
  条件: (x : X) (n : 整数)
  证明: by simp [toFreeAbelianGroup]
-/
@[simp] lemma Finsupp.toFreeAbelianGroup_single (x : X) (n : Int) :
    toFreeAbelianGroup (single x n) = n • .of x := by simp [toFreeAbelianGroup]

open Finsupp FreeAbelianGroup

@[simp]
/--
theorem `Finsupp.toFreeAbelianGroup_comp_singleAddHom` / 定理 `Finsupp.toFreeAbelianGroup_comp_singleAddHom`

English:
theorem Finsupp.toFreeAbelianGroup_comp_singleAddHom
  given: (x : X)
  proof: AddMonoidHom.ext toFreeAbelianGroup_single _

@[simp]

中文:
定理 有限支撑.toFreeAbelianGroup_comp_singleAddHom
  条件: (x : X)
  证明: AddMonoidHom.ext toFreeAbelianGroup_single _

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, toFreeAbelianGroup_single
-/
theorem Finsupp.toFreeAbelianGroup_comp_singleAddHom (x : X) :
    Finsupp.toFreeAbelianGroup.comp (Finsupp.singleAddHom x) =
      (smulAddHom Int (FreeAbelianGroup X)).flip (of x) :=
AddMonoidHom.ext toFreeAbelianGroup_single _

@[simp]
/--
theorem `FreeAbelianGroup.toFinsupp_comp_toFreeAbelianGroup` / 定理 `FreeAbelianGroup.toFinsupp_comp_toFreeAbelianGroup`

English:
theorem FreeAbelianGroup.toFinsupp_comp_toFreeAbelianGroup
  proof: by
  ext
  simp

@[simp]

中文:
定理 自由交换群.toFinsupp_comp_toFreeAbelianGroup
  证明: by
  ext
  simp

@[simp]
-/
theorem FreeAbelianGroup.toFinsupp_comp_toFreeAbelianGroup :
    toFinsupp.comp toFreeAbelianGroup = AddMonoidHom.id (X ->₀ Int) := by
  ext
  simp

@[simp]
/--
theorem `Finsupp.toFreeAbelianGroup_comp_toFinsupp` / 定理 `Finsupp.toFreeAbelianGroup_comp_toFinsupp`

English:
theorem Finsupp.toFreeAbelianGroup_comp_toFinsupp
  proof: by
  ext
  rw [toFreeAbelianGroup]; rw [toFinsupp]; rw [AddMonoidHom.comp_apply]; rw [lift_apply_of]; rw [liftAddHom_apply_single]; rw [AddMonoidHom.flip_apply]; rw [smulAddHom_apply]; rw [one_smul]; rw [AddMonoidHom.id_apply]

@[simp]

中文:
定理 有限支撑.toFreeAbelianGroup_comp_toFinsupp
  证明: by
  ext
  rw [toFreeAbelianGroup]; rw [toFinsupp]; rw [AddMonoidHom.comp_apply]; rw [lift_apply_of]; rw [liftAddHom_apply_single]; rw [AddMonoidHom.flip_apply]; rw [smulAddHom_apply]; rw [one_smul]; rw [AddMonoidHom.id_apply]

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.comp_apply, AddMonoidHom.flip_apply, AddMonoidHom.id_apply, comp_apply, flip_apply, id_apply, liftAddHom_apply_single, lift_apply_of, one_smul, smulAddHom_apply, toFinsupp, toFreeAbelianGroup
-/
theorem Finsupp.toFreeAbelianGroup_comp_toFinsupp :
    toFreeAbelianGroup.comp toFinsupp = AddMonoidHom.id (FreeAbelianGroup X) := by
  ext
  rw [toFreeAbelianGroup]; rw [toFinsupp]; rw [AddMonoidHom.comp_apply]; rw [lift_apply_of]; rw [liftAddHom_apply_single]; rw [AddMonoidHom.flip_apply]; rw [smulAddHom_apply]; rw [one_smul]; rw [AddMonoidHom.id_apply]

@[simp]
/--
theorem `Finsupp.toFreeAbelianGroup_toFinsupp` / 定理 `Finsupp.toFreeAbelianGroup_toFinsupp`

English:
theorem Finsupp.toFreeAbelianGroup_toFinsupp
  given: {X} (x : FreeAbelianGroup X)
  proof: by
  rw [← AddMonoidHom.comp_apply]; rw [Finsupp.toFreeAbelianGroup_comp_toFinsupp]; rw [AddMonoidHom.id_apply]

中文:
定理 有限支撑.toFreeAbelianGroup_toFinsupp
  条件: {X} (x : 自由交换群 X)
  证明: by
  rw [← AddMonoidHom.comp_apply]; rw [Finsupp.toFreeAbelianGroup_comp_toFinsupp]; rw [AddMonoidHom.id_apply]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.comp_apply, AddMonoidHom.id_apply, Finsupp, Finsupp.toFreeAbelianGroup_comp_toFinsupp, comp_apply, id_apply, toFreeAbelianGroup_comp_toFinsupp
-/
theorem Finsupp.toFreeAbelianGroup_toFinsupp {X} (x : FreeAbelianGroup X) :
    Finsupp.toFreeAbelianGroup (FreeAbelianGroup.toFinsupp x) = x := by
  rw [← AddMonoidHom.comp_apply]; rw [Finsupp.toFreeAbelianGroup_comp_toFinsupp]; rw [AddMonoidHom.id_apply]

namespace FreeAbelianGroup

open Finsupp

@[simp]
/--
theorem `toFinsupp_toFreeAbelianGroup` / 定理 `toFinsupp_toFreeAbelianGroup`

English:
theorem toFinsupp_toFreeAbelianGroup
  given: (f : X ->₀ Int)
  proof: by
  rw [← AddMonoidHom.comp_apply]; rw [toFinsupp_comp_toFreeAbelianGroup]; rw [AddMonoidHom.id_apply]

中文:
定理 toFinsupp_toFreeAbelianGroup
  条件: (f : X ->₀ 整数)
  证明: by
  rw [← AddMonoidHom.comp_apply]; rw [toFinsupp_comp_toFreeAbelianGroup]; rw [AddMonoidHom.id_apply]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.comp_apply, AddMonoidHom.id_apply, comp_apply, id_apply, toFinsupp_comp_toFreeAbelianGroup
-/
theorem toFinsupp_toFreeAbelianGroup (f : X ->₀ Int) :
    FreeAbelianGroup.toFinsupp (Finsupp.toFreeAbelianGroup f) = f := by
  rw [← AddMonoidHom.comp_apply]; rw [toFinsupp_comp_toFreeAbelianGroup]; rw [AddMonoidHom.id_apply]

variable (X)

/-- The additive equivalence between `FreeAbelianGroup X` and `(X →₀ ℤ)`. -/
@[simps!]
/--
Definition of `equivFinsupp` / `equivFinsupp` 的定义

English:
definition equivFinsupp
  signature: : FreeAbelianGroup X ≃+ (X ->₀ Int) where
  body: toFinsupp
  invFun := toFreeAbelianGroup
  left_inv := toFreeAbelianGroup_toFinsupp
  right_inv := toFinsupp_toFreeAbelianGroup
  map_add' := toFinsupp.map_add

中文:
定义 equivFinsupp
  签名: : 自由交换群 X ≃+ (X ->₀ 整数) where
  定义体: toFinsupp
  invFun := toFreeAbelianGroup
  left_inv := toFreeAbelianGroup_toFinsupp
  right_inv := toFinsupp_toFreeAbelianGroup
  map_add' := toFinsupp.map_add

Depends on / 依赖: toFinsupp
-/
def equivFinsupp : FreeAbelianGroup X ≃+ (X ->₀ Int) where
  toFun := toFinsupp
  invFun := toFreeAbelianGroup
  left_inv := toFreeAbelianGroup_toFinsupp
  right_inv := toFinsupp_toFreeAbelianGroup
  map_add' := toFinsupp.map_add

variable {X}

/--
Definition of `coeff` / `coeff` 的定义

English:
definition coeff
  signature: (x : X)
  body: (Finsupp.applyAddHom x).comp toFinsupp

中文:
定义 coeff
  签名: (x : X)
  定义体: (Finsupp.applyAddHom x).comp toFinsupp

Depends on / 依赖: Finsupp, Finsupp.applyAddHom, applyAddHom, toFinsupp
-/
def coeff (x : X) : FreeAbelianGroup X ->+ Int :=
  (Finsupp.applyAddHom x).comp toFinsupp

/--
Definition of `support` / `support` 的定义

English:
definition support
  signature: (a : FreeAbelianGroup X)
  body: a.toFinsupp.support

@[simp]

中文:
定义 support
  签名: (a : 自由交换群 X)
  定义体: a.toFinsupp.support

@[simp]

Depends on / 依赖: a.toFinsupp.support, support, toFinsupp
-/
def support (a : FreeAbelianGroup X) : Finset X :=
  a.toFinsupp.support

@[simp]
/--
theorem `mem_support_iff` / 定理 `mem_support_iff`

English:
theorem mem_support_iff
  given: (x : X) (a : FreeAbelianGroup X)
  statement: x in a.support ↔ coeff x a != 0
  proof: by
  rw [support]; rw [Finsupp.mem_support_iff]
  exact Iff.rfl

中文:
定理 mem_support_iff
  条件: (x : X) (a : 自由交换群 X)
  结论: x in a.support ↔ coeff x a != 0
  证明: by
  rw [support]; rw [Finsupp.mem_support_iff]
  exact Iff.rfl

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff, Iff.rfl, mem_support_iff, support
-/
theorem mem_support_iff (x : X) (a : FreeAbelianGroup X) : x in a.support ↔ coeff x a != 0 := by
  rw [support]; rw [Finsupp.mem_support_iff]
  exact Iff.rfl

/--
theorem `notMem_support_iff` / 定理 `notMem_support_iff`

English:
theorem notMem_support_iff
  given: (x : X) (a : FreeAbelianGroup X)
  statement: x ∉ a.support ↔ coeff x a = 0
  proof: by
  rw [support]; rw [Finsupp.notMem_support_iff]
  exact Iff.rfl

@[simp]

中文:
定理 notMem_support_iff
  条件: (x : X) (a : 自由交换群 X)
  结论: x ∉ a.support ↔ coeff x a = 0
  证明: by
  rw [support]; rw [Finsupp.notMem_support_iff]
  exact Iff.rfl

@[simp]

Depends on / 依赖: Finsupp, Finsupp.notMem_support_iff, Iff.rfl, notMem_support_iff, support
-/
theorem notMem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∉ a.support ↔ coeff x a = 0 := by
  rw [support]; rw [Finsupp.notMem_support_iff]
  exact Iff.rfl

@[simp]
/--
theorem `support_zero` / 定理 `support_zero`

English:
theorem support_zero
  statement: support (0 : FreeAbelianGroup X) = ∅
  proof: by
  simp only [support, Finsupp.support_zero, map_zero]

@[simp]

中文:
定理 support_zero
  结论: support (0 : 自由交换群 X) = ∅
  证明: by
  simp only [support, Finsupp.support_zero, map_zero]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.support_zero, FreeAbelianGroup, FreeAbelianGroup.equivFinsupp, equivFinsupp, map_zero, support, support_zero, twoUniqueSums_iff, twoUniqueSums_iff.mpr
-/
theorem support_zero : support (0 : FreeAbelianGroup X) = ∅ := by
  simp only [support, Finsupp.support_zero, map_zero]

@[simp]
/--
theorem `support_of` / 定理 `support_of`

English:
theorem support_of
  given: (x : X)
  statement: support (of x) = {x}
  proof: by
  rw [support]; rw [toFinsupp_of]; rw [Finsupp.support_single _ one_ne_zero]

@[simp]

中文:
定理 support_of
  条件: (x : X)
  结论: support (of x) = {x}
  证明: by
  rw [support]; rw [toFinsupp_of]; rw [Finsupp.support_single _ one_ne_zero]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.support_single, one_ne_zero, support, support_single, toFinsupp_of
-/
theorem support_of (x : X) : support (of x) = {x} := by
  rw [support]; rw [toFinsupp_of]; rw [Finsupp.support_single _ one_ne_zero]

@[simp]
/--
theorem `support_neg` / 定理 `support_neg`

English:
theorem support_neg
  given: (a : FreeAbelianGroup X)
  statement: support (-a) = support a
  proof: by
  simp only [support, map_neg, Finsupp.support_neg]

@[simp]

中文:
定理 support_neg
  条件: (a : 自由交换群 X)
  结论: support (-a) = support a
  证明: by
  simp only [support, map_neg, Finsupp.support_neg]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.support_neg, map_neg, support, support_neg
-/
theorem support_neg (a : FreeAbelianGroup X) : support (-a) = support a := by
  simp only [support, map_neg, Finsupp.support_neg]

@[simp]
/--
theorem `support_zsmul` / 定理 `support_zsmul`

English:
theorem support_zsmul
  given: (k : Int) (h : k != 0) (a : FreeAbelianGroup X)
  proof: by
  ext x
  simp [h]

@[simp]

中文:
定理 support_zsmul
  条件: (k : 整数) (h : k != 0) (a : 自由交换群 X)
  证明: by
  ext x
  simp [h]

@[simp]
-/
theorem support_zsmul (k : Int) (h : k != 0) (a : FreeAbelianGroup X) :
    support (k • a) = support a := by
  ext x
  simp [h]

@[simp]
/--
theorem `support_nsmul` / 定理 `support_nsmul`

English:
theorem support_nsmul
  given: (k : Nat) (h : k != 0) (a : FreeAbelianGroup X)
  proof: by
  apply support_zsmul k _ a
  exact mod_cast h

中文:
定理 support_nsmul
  条件: (k : 自然数) (h : k != 0) (a : 自由交换群 X)
  证明: by
  apply support_zsmul k _ a
  exact mod_cast h

Depends on / 依赖: mod_cast, support_zsmul
-/
theorem support_nsmul (k : Nat) (h : k != 0) (a : FreeAbelianGroup X) :
    support (k • a) = support a := by
  apply support_zsmul k _ a
  exact mod_cast h

open scoped Classical in
/--
theorem `support_add` / 定理 `support_add`

English:
theorem support_add
  given: (a b : FreeAbelianGroup X)
  statement: support (a + b) subseteq a.support union b.support
  proof: by
  simp only [support, map_add]
  apply Finsupp.support_add

中文:
定理 support_add
  条件: (a b : 自由交换群 X)
  结论: support (a + b) subseteq a.support union b.support
  证明: by
  simp only [support, map_add]
  apply Finsupp.support_add

Depends on / 依赖: Finsupp, Finsupp.support_add, map_add, support, support_add
-/
theorem support_add (a b : FreeAbelianGroup X) : support (a + b) subseteq a.support union b.support := by
  simp only [support, map_add]
  apply Finsupp.support_add

/--
theorem `support_eq_empty` / 定理 `support_eq_empty`

English:
theorem support_eq_empty
  given: {a : FreeAbelianGroup X}
  statement: a.support = ∅ ↔ a = 0
  proof: Finsupp.support_eq_empty.trans (equivFinsupp X).map_eq_zero_iff

中文:
定理 support_eq_empty
  条件: {a : 自由交换群 X}
  结论: a.support = ∅ ↔ a = 0
  证明: Finsupp.support_eq_empty.trans (equivFinsupp X).map_eq_zero_iff
-/
@[simp] theorem support_eq_empty {a : FreeAbelianGroup X} : a.support = ∅ ↔ a = 0 :=
  Finsupp.support_eq_empty.trans (equivFinsupp X).map_eq_zero_iff

/--
theorem `nonempty_support_iff` / 定理 `nonempty_support_iff`

English:
theorem nonempty_support_iff
  given: {a : FreeAbelianGroup X}
  proof: by
  contrapose!; exact support_eq_empty

中文:
定理 nonempty_support_iff
  条件: {a : 自由交换群 X}
  证明: by
  contrapose!; exact support_eq_empty
-/
@[simp] theorem nonempty_support_iff {a : FreeAbelianGroup X} :
    a.support.Nonempty ↔ a != 0 := by
  contrapose!; exact support_eq_empty

/--
theorem `card_support_eq_zero` / 定理 `card_support_eq_zero`

English:
theorem card_support_eq_zero
  given: {a : FreeAbelianGroup X}
  statement: a.support.card = 0 ↔ a = 0
  proof: by
  simp

中文:
定理 card_support_eq_zero
  条件: {a : 自由交换群 X}
  结论: a.support.card = 0 ↔ a = 0
  证明: by
  simp
-/
theorem card_support_eq_zero {a : FreeAbelianGroup X} : a.support.card = 0 ↔ a = 0 := by
  simp

/--
theorem `eq_sum_support_coeff_smul_of` / 定理 `eq_sum_support_coeff_smul_of`

English:
theorem eq_sum_support_coeff_smul_of
  given: (a : FreeAbelianGroup X)
  proof: by
  conv_lhs => rw [← toFreeAbelianGroup_toFinsupp a, ← sum_single a.toFinsupp]
  simp [sum, support, coeff]

中文:
定理 eq_sum_support_coeff_smul_of
  条件: (a : 自由交换群 X)
  证明: by
  conv_lhs => rw [← toFreeAbelianGroup_toFinsupp a, ← sum_single a.toFinsupp]
  simp [sum, support, coeff]

Depends on / 依赖: a.toFinsupp, conv_lhs, sum_single, support, toFinsupp, toFreeAbelianGroup_toFinsupp
-/
theorem eq_sum_support_coeff_smul_of (a : FreeAbelianGroup X) :
    a = ∑ x in a.support, coeff x a • of x := by
  conv_lhs => rw [← toFreeAbelianGroup_toFinsupp a, ← sum_single a.toFinsupp]
  simp [sum, support, coeff]

end FreeAbelianGroup
