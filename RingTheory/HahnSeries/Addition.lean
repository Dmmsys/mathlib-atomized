/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Support
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.RingTheory.HahnSeries.Basic
public import Mathlib.Tactic.FastInstance

/-!
# Additive properties of Hahn series

If `Γ` is ordered and `R` has zero, then `R⟦Γ⟧` consists of formal series over `Γ` with coefficients
in `R`, whose supports are partially well-ordered. With further structure on `R` and `Γ`, we can add
further structure on `R⟦Γ⟧`. When `R` has an addition operation, `R⟦Γ⟧` also has addition by adding
coefficients.

## Main Definitions
* If `R` is a (commutative) additive monoid or group, then so is `R⟦Γ⟧`.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

@[expose] public section


open Finset Function

noncomputable section

variable {Γ Γ' R S U V α : Type*}

namespace HahnSeries

section SMulZeroClass

variable [PartialOrder Γ] {V : Type*} [Zero V] [SMulZeroClass R V]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R V⟦Γ⟧
  body: ⟨fun r x =>
    { coeff := r • x.coeff
      isPWO_support' := x.isPWO_support.mono (Function.support_const_smul_subset ..) }⟩

中文:
实例 :
  签名: 标量乘法 R V⟦Γ⟧
  定义体: ⟨fun r x =>
    { coeff := r • x.coeff
      isPWO_support' := x.isPWO_support.mono (Function.support_const_smul_subset ..) }⟩

Depends on / 依赖: Function, Function.support_const_smul_subset, isPWO_support, support_const_smul_subset, x.coeff, x.isPWO_support.mono
-/
instance : SMul R V⟦Γ⟧ :=
  ⟨fun r x =>
    { coeff := r • x.coeff
      isPWO_support' := x.isPWO_support.mono (Function.support_const_smul_subset ..) }⟩

/--
theorem `support_smul_subset` / 定理 `support_smul_subset`

English:
theorem support_smul_subset
  given: (r : R) (x : HahnSeries Γ V)
  statement: (r • x).support subseteq x.support
  proof: Function.support_const_smul_subset ..

@[simp]

中文:
定理 support_smul_subset
  条件: (r : R) (x : Hahn级数 Γ V)
  结论: (r • x).support subseteq x.support
  证明: Function.support_const_smul_subset ..

@[simp]

Depends on / 依赖: Function, Function.support_const_smul_subset, support_const_smul_subset
-/
theorem support_smul_subset (r : R) (x : HahnSeries Γ V) : (r • x).support subseteq x.support :=
  Function.support_const_smul_subset ..

@[simp]
/--
theorem `coeff_smul'` / 定理 `coeff_smul'`

English:
theorem coeff_smul'
  given: (r : R) (x : V⟦Γ⟧)
  statement: (r • x).coeff = r • x.coeff
  proof: rfl

@[simp]

中文:
定理 coeff_smul'
  条件: (r : R) (x : V⟦Γ⟧)
  结论: (r • x).coeff = r • x.coeff
  证明: rfl

@[simp]
-/
theorem coeff_smul' (r : R) (x : V⟦Γ⟧) : (r • x).coeff = r • x.coeff :=
  rfl

@[simp]
/--
theorem `coeff_smul` / 定理 `coeff_smul`

English:
theorem coeff_smul
  given: {r : R} {x : V⟦Γ⟧} {a : Γ}
  statement: (r • x).coeff a = r • x.coeff a
  proof: rfl

中文:
定理 coeff_smul
  条件: {r : R} {x : V⟦Γ⟧} {a : Γ}
  结论: (r • x).coeff a = r • x.coeff a
  证明: rfl
-/
theorem coeff_smul {r : R} {x : V⟦Γ⟧} {a : Γ} : (r • x).coeff a = r • x.coeff a :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulZeroClass R V⟦Γ⟧
  body: by
    ext
    simp only [coeff_smul, coeff_zero, smul_zero]

中文:
实例 :
  签名: SMulZero类 R V⟦Γ⟧
  定义体: by
    ext
    simp only [coeff_smul, coeff_zero, smul_zero]

Depends on / 依赖: coeff_smul, coeff_zero, smul_zero
-/
instance : SMulZeroClass R V⟦Γ⟧ where
  smul_zero _ := by
    ext
    simp only [coeff_smul, coeff_zero, smul_zero]

/--
theorem `orderTop_smul_not_lt` / 定理 `orderTop_smul_not_lt`

English:
theorem orderTop_smul_not_lt
  given: (r : R) (x : V⟦Γ⟧)
  statement: ¬ (r • x).orderTop < x.orderTop
  proof: by
  by_cases hrx : r • x = 0
  · rw [hrx, orderTop_zero]
    exact not_top_lt
  · simp only [orderTop_of_ne_zero hrx, orderTop_of_ne_zero <| right_ne_zero_of_smul hrx,
      WithTop.coe_lt_coe]
    exact Set.IsWF.min_of_subset_not_lt_min (Function.support_smul_subset_right ..)

中文:
定理 orderTop_smul_not_lt
  条件: (r : R) (x : V⟦Γ⟧)
  结论: ¬ (r • x).orderTop < x.orderTop
  证明: by
  by_cases hrx : r • x = 0
  · rw [hrx, orderTop_zero]
    exact not_top_lt
  · simp only [orderTop_of_ne_zero hrx, orderTop_of_ne_zero <| right_ne_zero_of_smul hrx,
      WithTop.coe_lt_coe]
    exact Set.IsWF.min_of_subset_not_lt_min (Function.support_smul_subset_right ..)

Depends on / 依赖: Function, Function.support_smul_subset_right, Set.IsWF.min_of_subset_not_lt_min, WithTop, WithTop.coe_lt_coe, coe_lt_coe, min_of_subset_not_lt_min, not_top_lt, orderTop_of_ne_zero, orderTop_zero, right_ne_zero_of_smul, support_smul_subset_right
-/
theorem orderTop_smul_not_lt (r : R) (x : V⟦Γ⟧) : ¬ (r • x).orderTop < x.orderTop := by
  by_cases hrx : r • x = 0
  · rw [hrx, orderTop_zero]
    exact not_top_lt
  · simp only [orderTop_of_ne_zero hrx, orderTop_of_ne_zero <| right_ne_zero_of_smul hrx,
      WithTop.coe_lt_coe]
    exact Set.IsWF.min_of_subset_not_lt_min (Function.support_smul_subset_right ..)

/--
theorem `orderTop_le_orderTop_smul` / 定理 `orderTop_le_orderTop_smul`

English:
theorem orderTop_le_orderTop_smul
  given: {Γ} [LinearOrder Γ] (r : R) (x : V⟦Γ⟧)
  proof: le_of_not_gt orderTop_smul_not_lt r x

中文:
定理 orderTop_le_orderTop_smul
  条件: {Γ} [线性序 Γ] (r : R) (x : V⟦Γ⟧)
  证明: le_of_not_gt orderTop_smul_not_lt r x

Depends on / 依赖: le_of_not_gt, orderTop_smul_not_lt
-/
theorem orderTop_le_orderTop_smul {Γ} [LinearOrder Γ] (r : R) (x : V⟦Γ⟧) :
    x.orderTop <= (r • x).orderTop :=
le_of_not_gt orderTop_smul_not_lt r x

/--
theorem `order_smul_not_lt` / 定理 `order_smul_not_lt`

English:
theorem order_smul_not_lt
  given: [Zero Γ] (r : R) (x : V⟦Γ⟧) (h : r • x != 0)
  proof: by
  have hx : x != 0 := right_ne_zero_of_smul h
  simp_all only [order, dite_false]
  exact Set.IsWF.min_of_subset_not_lt_min (Function.support_smul_subset_right ..)

中文:
定理 order_smul_not_lt
  条件: [零 Γ] (r : R) (x : V⟦Γ⟧) (h : r • x != 0)
  证明: by
  have hx : x != 0 := right_ne_zero_of_smul h
  simp_all only [order, dite_false]
  exact Set.IsWF.min_of_subset_not_lt_min (Function.support_smul_subset_right ..)

Depends on / 依赖: Function, Function.support_smul_subset_right, Set.IsWF.min_of_subset_not_lt_min, dite_false, min_of_subset_not_lt_min, right_ne_zero_of_smul, support_smul_subset_right
-/
theorem order_smul_not_lt [Zero Γ] (r : R) (x : V⟦Γ⟧) (h : r • x != 0) :
    ¬ (r • x).order < x.order := by
  have hx : x != 0 := right_ne_zero_of_smul h
  simp_all only [order, dite_false]
  exact Set.IsWF.min_of_subset_not_lt_min (Function.support_smul_subset_right ..)

/--
theorem `le_order_smul` / 定理 `le_order_smul`

English:
theorem le_order_smul
  given: {Γ} [Zero Γ] [LinearOrder Γ] (r : R) (x : V⟦Γ⟧) (h : r • x != 0)
  proof: le_of_not_gt (order_smul_not_lt r x h)

中文:
定理 le_order_smul
  条件: {Γ} [零 Γ] [线性序 Γ] (r : R) (x : V⟦Γ⟧) (h : r • x != 0)
  证明: le_of_not_gt (order_smul_not_lt r x h)

Depends on / 依赖: le_of_not_gt, order_smul_not_lt
-/
theorem le_order_smul {Γ} [Zero Γ] [LinearOrder Γ] (r : R) (x : V⟦Γ⟧) (h : r • x != 0) :
    x.order <= (r • x).order :=
  le_of_not_gt (order_smul_not_lt r x h)

/--
theorem `truncLT_smul` / 定理 `truncLT_smul`

English:
theorem truncLT_smul
  given: [DecidableLT Γ] (c : Γ) (r : R) (x : V⟦Γ⟧)
  proof: by ext; simp

中文:
定理 truncLT_smul
  条件: [DecidableLT Γ] (c : Γ) (r : R) (x : V⟦Γ⟧)
  证明: by ext; simp
-/
theorem truncLT_smul [DecidableLT Γ] (c : Γ) (r : R) (x : V⟦Γ⟧) :
    truncLT c (r • x) = r • truncLT c x := by ext; simp

end SMulZeroClass

section Addition

variable [PartialOrder Γ]

section AddMonoid

variable [AddMonoid R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add R⟦Γ⟧
  body: { coeff := x.coeff + y.coeff
      isPWO_support' := (x.isPWO_support.union y.isPWO_support).mono (Function.support_add ..) }

中文:
实例 :
  签名: 加法 R⟦Γ⟧
  定义体: { coeff := x.coeff + y.coeff
      isPWO_support' := (x.isPWO_support.union y.isPWO_support).mono (Function.support_add ..) }

Depends on / 依赖: Function, Function.support_add, isPWO_support, support_add, x.coeff, x.isPWO_support.union, y.coeff, y.isPWO_support
-/
instance : Add R⟦Γ⟧ where
  add x y :=
    { coeff := x.coeff + y.coeff
      isPWO_support' := (x.isPWO_support.union y.isPWO_support).mono (Function.support_add ..) }

/--
theorem `support_add_subset` / 定理 `support_add_subset`

English:
theorem support_add_subset
  given: (x y : R⟦Γ⟧)
  statement: (x + y).support subseteq x.support union y.support
  proof: Function.support_add ..

@[simp]

中文:
定理 support_add_subset
  条件: (x y : R⟦Γ⟧)
  结论: (x + y).support subseteq x.support union y.support
  证明: Function.support_add ..

@[simp]

Depends on / 依赖: Function, Function.support_add, support_add
-/
theorem support_add_subset (x y : R⟦Γ⟧) : (x + y).support subseteq x.support union y.support :=
  Function.support_add ..

@[simp]
/--
theorem `coeff_add'` / 定理 `coeff_add'`

English:
theorem coeff_add'
  given: (x y : R⟦Γ⟧)
  statement: (x + y).coeff = x.coeff + y.coeff
  proof: rfl

中文:
定理 coeff_add'
  条件: (x y : R⟦Γ⟧)
  结论: (x + y).coeff = x.coeff + y.coeff
  证明: rfl
-/
theorem coeff_add' (x y : R⟦Γ⟧) : (x + y).coeff = x.coeff + y.coeff :=
  rfl

/--
theorem `coeff_add` / 定理 `coeff_add`

English:
theorem coeff_add
  given: {x y : R⟦Γ⟧} {a : Γ}
  statement: (x + y).coeff a = x.coeff a + y.coeff a
  proof: rfl

中文:
定理 coeff_add
  条件: {x y : R⟦Γ⟧} {a : Γ}
  结论: (x + y).coeff a = x.coeff a + y.coeff a
  证明: rfl
-/
theorem coeff_add {x y : R⟦Γ⟧} {a : Γ} : (x + y).coeff a = x.coeff a + y.coeff a :=
  rfl

/--
theorem `single_add` / 定理 `single_add`

English:
theorem single_add
  given: (a : Γ) (r s : R)
  statement: single a (r + s) = single a r + single a s
  proof: by
  classical
  ext : 1; exact Pi.single_add (f := fun _ => R) a r s

中文:
定理 single_add
  条件: (a : Γ) (r s : R)
  结论: single a (r + s) = single a r + single a s
  证明: by
  classical
  ext : 1; exact Pi.single_add (f := fun _ => R) a r s
-/
@[simp] theorem single_add (a : Γ) (r s : R) : single a (r + s) = single a r + single a s := by
  classical
  ext : 1; exact Pi.single_add (f := fun _ => R) a r s

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoid R⟦Γ⟧
  body: fast_instance%
  coeff_injective.addMonoid _
    coeff_zero' coeff_add' (fun _ _ => coeff_smul' _ _)

中文:
实例 :
  签名: 加法幺半群 R⟦Γ⟧
  定义体: fast_instance%
  coeff_injective.addMonoid _
    coeff_zero' coeff_add' (fun _ _ => coeff_smul' _ _)

Depends on / 依赖: fast_instance
-/
instance : AddMonoid R⟦Γ⟧ := fast_instance%
  coeff_injective.addMonoid _
    coeff_zero' coeff_add' (fun _ _ => coeff_smul' _ _)

/--
theorem `coeff_nsmul` / 定理 `coeff_nsmul`

English:
theorem coeff_nsmul
  given: {x : R⟦Γ⟧} {n : Nat}
  statement: (n • x).coeff = n • x.coeff
  proof: coeff_smul' _ _

@[simp]

中文:
定理 coeff_nsmul
  条件: {x : R⟦Γ⟧} {n : 自然数}
  结论: (n • x).coeff = n • x.coeff
  证明: coeff_smul' _ _

@[simp]

Depends on / 依赖: coeff_smul
-/
theorem coeff_nsmul {x : R⟦Γ⟧} {n : Nat} : (n • x).coeff = n • x.coeff := coeff_smul' _ _

@[simp]
/--
lemma `map_add` / 引理 `map_add`

English:
lemma map_add
  given: [AddMonoid S] (f : R ->+ S) {x y : R⟦Γ⟧}
  proof: by
  ext; simp

中文:
引理 map_add
  条件: [加法幺半群 S] (f : R ->+ S) {x y : R⟦Γ⟧}
  证明: by
  ext; simp
-/
protected lemma map_add [AddMonoid S] (f : R ->+ S) {x y : R⟦Γ⟧} :
    ((x + y).map f : S⟦Γ⟧) = x.map f + y.map f := by
  ext; simp
/--
`addOppositeEquiv` is an additive monoid isomorphism between
Hahn series over `Γ` with coefficients in the opposite additive monoid `Rᵃᵒᵖ`
and the additive opposite of Hahn series over `Γ` with coefficients `R`.
-/
@[simps -isSimp]
/--
Definition of `addOppositeEquiv` / `addOppositeEquiv` 的定义

English:
definition addOppositeEquiv
  signature: : Rᵃᵒᵖ⟦Γ⟧ ≃+ R⟦Γ⟧ᵃᵒᵖ where
  body: .op ⟨fun a => (x.coeff a).unop, by convert! x.isPWO_support; ext; simp⟩
  invFun x := ⟨fun a => .op (x.unop.coeff a), by convert! x.unop.isPWO_support; ext; simp⟩
  left_inv x := by simp
  right_inv x := by
    apply AddOpposite.unop_injective
    simp
  map_add' x y := by
    apply AddOpposite.unop_injective
    ext
    simp

@[simp]

中文:
定义 addOppositeEquiv
  签名: : Rᵃᵒᵖ⟦Γ⟧ ≃+ R⟦Γ⟧ᵃᵒᵖ where
  定义体: .op ⟨fun a => (x.coeff a).unop, by convert! x.isPWO_support; ext; simp⟩
  invFun x := ⟨fun a => .op (x.unop.coeff a), by convert! x.unop.isPWO_support; ext; simp⟩
  left_inv x := by simp
  right_inv x := by
    apply AddOpposite.unop_injective
    simp
  map_add' x y := by
    apply AddOpposite.unop_injective
    ext
    simp

@[simp]

Depends on / 依赖: convert, isPWO_support, x.coeff, x.isPWO_support
-/
def addOppositeEquiv : Rᵃᵒᵖ⟦Γ⟧ ≃+ R⟦Γ⟧ᵃᵒᵖ where
  toFun x := .op ⟨fun a => (x.coeff a).unop, by convert! x.isPWO_support; ext; simp⟩
  invFun x := ⟨fun a => .op (x.unop.coeff a), by convert! x.unop.isPWO_support; ext; simp⟩
  left_inv x := by simp
  right_inv x := by
    apply AddOpposite.unop_injective
    simp
  map_add' x y := by
    apply AddOpposite.unop_injective
    ext
    simp

@[simp]
/--
lemma `addOppositeEquiv_support` / 引理 `addOppositeEquiv_support`

English:
lemma addOppositeEquiv_support
  given: (x : Rᵃᵒᵖ⟦Γ⟧)
  proof: by
  ext
  simp [addOppositeEquiv_apply]

@[simp]

中文:
引理 addOppositeEquiv_support
  条件: (x : Rᵃᵒᵖ⟦Γ⟧)
  证明: by
  ext
  simp [addOppositeEquiv_apply]

@[simp]

Depends on / 依赖: addOppositeEquiv_apply
-/
lemma addOppositeEquiv_support (x : Rᵃᵒᵖ⟦Γ⟧) :
    (addOppositeEquiv x).unop.support = x.support := by
  ext
  simp [addOppositeEquiv_apply]

@[simp]
/--
lemma `addOppositeEquiv_symm_support` / 引理 `addOppositeEquiv_symm_support`

English:
lemma addOppositeEquiv_symm_support
  given: (x : R⟦Γ⟧ᵃᵒᵖ)
  proof: by
  rw [← addOppositeEquiv_support]; rw [AddEquiv.apply_symm_apply]

中文:
引理 addOppositeEquiv_symm_support
  条件: (x : R⟦Γ⟧ᵃᵒᵖ)
  证明: by
  rw [← addOppositeEquiv_support]; rw [AddEquiv.apply_symm_apply]

Depends on / 依赖: AddEquiv, AddEquiv.apply_symm_apply, addOppositeEquiv_support, apply_symm_apply
-/
lemma addOppositeEquiv_symm_support (x : R⟦Γ⟧ᵃᵒᵖ) :
    (addOppositeEquiv.symm x).support = x.unop.support := by
  rw [← addOppositeEquiv_support]; rw [AddEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `addOppositeEquiv_orderTop` / 引理 `addOppositeEquiv_orderTop`

English:
lemma addOppositeEquiv_orderTop
  given: (x : Rᵃᵒᵖ⟦Γ⟧)
  proof: by
  classical
  simp only [orderTop,
    addOppositeEquiv_support]
  simp only [addOppositeEquiv_apply, AddOpposite.unop_op, mk_eq_zero]
  simp_rw [HahnSeries.ext_iff, funext_iff]
  simp only [Pi.zero_apply, AddOpposite.unop_eq_zero_iff, coeff_zero]

@[simp]

中文:
引理 addOppositeEquiv_orderTop
  条件: (x : Rᵃᵒᵖ⟦Γ⟧)
  证明: by
  classical
  simp only [orderTop,
    addOppositeEquiv_support]
  simp only [addOppositeEquiv_apply, AddOpposite.unop_op, mk_eq_zero]
  simp_rw [HahnSeries.ext_iff, funext_iff]
  simp only [Pi.zero_apply, AddOpposite.unop_eq_zero_iff, coeff_zero]

@[simp]

Depends on / 依赖: AddOpposite, AddOpposite.unop_eq_zero_iff, AddOpposite.unop_op, HahnSeries, HahnSeries.ext_iff, Pi.zero_apply, addOppositeEquiv_apply, addOppositeEquiv_support, classical, coeff_zero, ext_iff, funext_iff, mk_eq_zero, orderTop, simp_rw, unop_eq_zero_iff, unop_op, zero_apply
-/
lemma addOppositeEquiv_orderTop (x : Rᵃᵒᵖ⟦Γ⟧) :
    (addOppositeEquiv x).unop.orderTop = x.orderTop := by
  classical
  simp only [orderTop,
    addOppositeEquiv_support]
  simp only [addOppositeEquiv_apply, AddOpposite.unop_op, mk_eq_zero]
  simp_rw [HahnSeries.ext_iff, funext_iff]
  simp only [Pi.zero_apply, AddOpposite.unop_eq_zero_iff, coeff_zero]

@[simp]
/--
lemma `addOppositeEquiv_symm_orderTop` / 引理 `addOppositeEquiv_symm_orderTop`

English:
lemma addOppositeEquiv_symm_orderTop
  given: (x : R⟦Γ⟧ᵃᵒᵖ)
  proof: by
  rw [← addOppositeEquiv_orderTop]; rw [AddEquiv.apply_symm_apply]

中文:
引理 addOppositeEquiv_symm_orderTop
  条件: (x : R⟦Γ⟧ᵃᵒᵖ)
  证明: by
  rw [← addOppositeEquiv_orderTop]; rw [AddEquiv.apply_symm_apply]

Depends on / 依赖: AddEquiv, AddEquiv.apply_symm_apply, addOppositeEquiv_orderTop, apply_symm_apply
-/
lemma addOppositeEquiv_symm_orderTop (x : R⟦Γ⟧ᵃᵒᵖ) :
    (addOppositeEquiv.symm x).orderTop = x.unop.orderTop := by
  rw [← addOppositeEquiv_orderTop]; rw [AddEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `addOppositeEquiv_leadingCoeff` / 引理 `addOppositeEquiv_leadingCoeff`

English:
lemma addOppositeEquiv_leadingCoeff
  given: (x : Rᵃᵒᵖ⟦Γ⟧)
  proof: by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  simp only [ne_eq, AddOpposite.unop_eq_zero_iff, EmbeddingLike.map_eq_zero_iff, hx,
    not_false_eq_true, leadingCoeff_of_ne_zero, addOppositeEquiv_orderTop]
  simp [addOppositeEquiv]

@[simp]

中文:
引理 addOppositeEquiv_leadingCoeff
  条件: (x : Rᵃᵒᵖ⟦Γ⟧)
  证明: by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  simp only [ne_eq, AddOpposite.unop_eq_zero_iff, EmbeddingLike.map_eq_zero_iff, hx,
    not_false_eq_true, leadingCoeff_of_ne_zero, addOppositeEquiv_orderTop]
  simp [addOppositeEquiv]

@[simp]

Depends on / 依赖: AddOpposite, AddOpposite.unop_eq_zero_iff, EmbeddingLike, EmbeddingLike.map_eq_zero_iff, addOppositeEquiv, addOppositeEquiv_orderTop, eq_or_ne, leadingCoeff_of_ne_zero, map_eq_zero_iff, ne_eq, not_false_eq_true, unop_eq_zero_iff
-/
lemma addOppositeEquiv_leadingCoeff (x : Rᵃᵒᵖ⟦Γ⟧) :
    (addOppositeEquiv x).unop.leadingCoeff = x.leadingCoeff.unop := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  simp only [ne_eq, AddOpposite.unop_eq_zero_iff, EmbeddingLike.map_eq_zero_iff, hx,
    not_false_eq_true, leadingCoeff_of_ne_zero, addOppositeEquiv_orderTop]
  simp [addOppositeEquiv]

@[simp]
/--
lemma `addOppositeEquiv_symm_leadingCoeff` / 引理 `addOppositeEquiv_symm_leadingCoeff`

English:
lemma addOppositeEquiv_symm_leadingCoeff
  given: (x : R⟦Γ⟧ᵃᵒᵖ)
  proof: by
  apply AddOpposite.unop_injective
  rw [← addOppositeEquiv_leadingCoeff]; rw [AddEquiv.apply_symm_apply]; rw [AddOpposite.unop_op]

中文:
引理 addOppositeEquiv_symm_leadingCoeff
  条件: (x : R⟦Γ⟧ᵃᵒᵖ)
  证明: by
  apply AddOpposite.unop_injective
  rw [← addOppositeEquiv_leadingCoeff]; rw [AddEquiv.apply_symm_apply]; rw [AddOpposite.unop_op]

Depends on / 依赖: AddEquiv, AddEquiv.apply_symm_apply, AddOpposite, AddOpposite.unop_injective, AddOpposite.unop_op, addOppositeEquiv_leadingCoeff, apply_symm_apply, unop_injective, unop_op
-/
lemma addOppositeEquiv_symm_leadingCoeff (x : R⟦Γ⟧ᵃᵒᵖ) :
    (addOppositeEquiv.symm x).leadingCoeff = .op x.unop.leadingCoeff := by
  apply AddOpposite.unop_injective
  rw [← addOppositeEquiv_leadingCoeff]; rw [AddEquiv.apply_symm_apply]; rw [AddOpposite.unop_op]

/--
theorem `min_le_min_add` / 定理 `min_le_min_add`

English:
theorem min_le_min_add
  statement: {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} (hx : x != 0)
  proof: by
  rw [← Set.IsWF.min_union]
  exact Set.IsWF.min_le_min_of_subset (support_add_subset (x := x) (y := y))

中文:
定理 min_le_min_add
  结论: {Γ} [线性序 Γ] {x y : R⟦Γ⟧} (hx : x != 0)
  证明: by
  rw [← Set.IsWF.min_union]
  exact Set.IsWF.min_le_min_of_subset (support_add_subset (x := x) (y := y))
-/
protected theorem min_le_min_add {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} (hx : x != 0)
    (hy : y != 0) (hxy : x + y != 0) :
    min (Set.IsWF.min x.isWF_support (support_nonempty_iff.2 hx))
      (Set.IsWF.min y.isWF_support (support_nonempty_iff.2 hy)) <=
      Set.IsWF.min (x + y).isWF_support (support_nonempty_iff.2 hxy) := by
  rw [← Set.IsWF.min_union]
  exact Set.IsWF.min_le_min_of_subset (support_add_subset (x := x) (y := y))

/--
theorem `min_orderTop_le_orderTop_add` / 定理 `min_orderTop_le_orderTop_add`

English:
theorem min_orderTop_le_orderTop_add
  given: {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
  proof: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  by_cases hxy : x + y = 0; · simp [hxy]
  rw [orderTop_of_ne_zero hx]; rw [orderTop_of_ne_zero hy]; rw [orderTop_of_ne_zero hxy]; rw [← WithTop.coe_min]; rw [WithTop.coe_le_coe]
  exact HahnSeries.min_le_min_add hx hy hxy

中文:
定理 min_orderTop_le_orderTop_add
  条件: {Γ} [线性序 Γ] {x y : R⟦Γ⟧}
  证明: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  by_cases hxy : x + y = 0; · simp [hxy]
  rw [orderTop_of_ne_zero hx]; rw [orderTop_of_ne_zero hy]; rw [orderTop_of_ne_zero hxy]; rw [← WithTop.coe_min]; rw [WithTop.coe_le_coe]
  exact HahnSeries.min_le_min_add hx hy hxy

Depends on / 依赖: HahnSeries, HahnSeries.min_le_min_add, WithTop, WithTop.coe_le_coe, WithTop.coe_min, coe_le_coe, coe_min, min_le_min_add, orderTop_of_ne_zero
-/
theorem min_orderTop_le_orderTop_add {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} :
    min x.orderTop y.orderTop <= (x + y).orderTop := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  by_cases hxy : x + y = 0; · simp [hxy]
  rw [orderTop_of_ne_zero hx]; rw [orderTop_of_ne_zero hy]; rw [orderTop_of_ne_zero hxy]; rw [← WithTop.coe_min]; rw [WithTop.coe_le_coe]
  exact HahnSeries.min_le_min_add hx hy hxy

/--
theorem `min_order_le_order_add` / 定理 `min_order_le_order_add`

English:
theorem min_order_le_order_add
  statement: {Γ} [Zero Γ] [LinearOrder Γ] {x y : R⟦Γ⟧}
  proof: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [order_of_ne hx]; rw [order_of_ne hy]; rw [order_of_ne hxy]
  exact HahnSeries.min_le_min_add hx hy hxy

中文:
定理 min_order_le_order_add
  结论: {Γ} [零 Γ] [线性序 Γ] {x y : R⟦Γ⟧}
  证明: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [order_of_ne hx]; rw [order_of_ne hy]; rw [order_of_ne hxy]
  exact HahnSeries.min_le_min_add hx hy hxy

Depends on / 依赖: HahnSeries, HahnSeries.min_le_min_add, min_le_min_add, order_of_ne
-/
theorem min_order_le_order_add {Γ} [Zero Γ] [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : x + y != 0) : min x.order y.order <= (x + y).order := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [order_of_ne hx]; rw [order_of_ne hy]; rw [order_of_ne hxy]
  exact HahnSeries.min_le_min_add hx hy hxy

/--
theorem `orderTop_add_eq_left` / 定理 `orderTop_add_eq_left`

English:
theorem orderTop_add_eq_left
  statement: {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
  proof: by
  have hx : x != 0 := orderTop_ne_top.1 hxy.ne_top
  let g : Γ := Set.IsWF.min x.isWF_support (support_nonempty_iff.2 hx)
  have hcxyne : (x + y).coeff g != 0 := by
    rw [coeff_add]; rw [coeff_eq_zero_of_lt_orderTop (lt_of_eq_of_lt (orderTop_of_ne_zero hx).symm hxy)]; rw [add_zero]
    exact coeff_orderTop_ne (orderTop_of_ne_zero hx)
  have hxyx : (x + y).orderTop <= x.orderTop := by
    rw [orderTop_of_ne_zero hx]
    exact orderTop_le_of_coeff_ne_zero hcxyne
  exact le_antisymm hxyx (le_of_eq_of_le (min_eq_left_of_lt hxy).symm min_orderTop_le_orderTop_add)

中文:
定理 orderTop_add_eq_left
  结论: {Γ} [线性序 Γ] {x y : R⟦Γ⟧}
  证明: by
  have hx : x != 0 := orderTop_ne_top.1 hxy.ne_top
  let g : Γ := Set.IsWF.min x.isWF_support (support_nonempty_iff.2 hx)
  have hcxyne : (x + y).coeff g != 0 := by
    rw [coeff_add]; rw [coeff_eq_zero_of_lt_orderTop (lt_of_eq_of_lt (orderTop_of_ne_zero hx).symm hxy)]; rw [add_zero]
    exact coeff_orderTop_ne (orderTop_of_ne_zero hx)
  have hxyx : (x + y).orderTop <= x.orderTop := by
    rw [orderTop_of_ne_zero hx]
    exact orderTop_le_of_coeff_ne_zero hcxyne
  exact le_antisymm hxyx (le_of_eq_of_le (min_eq_left_of_lt hxy).symm min_orderTop_le_orderTop_add)

Depends on / 依赖: Set.IsWF.min, add_zero, coeff_add, coeff_eq_zero_of_lt_orderTop, coeff_orderTop_ne, hcxyne, hxy.ne_top, isWF_support, le_antisymm, le_of_eq_of_le, lt_of_eq_of_lt, min_eq_left_of, ne_top, orderTop, orderTop_le_of_coeff_ne_zero, orderTop_ne_top, orderTop_of_ne_zero, support_nonempty_iff, x.isWF_support, x.orderTop
-/
theorem orderTop_add_eq_left {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : x.orderTop < y.orderTop) : (x + y).orderTop = x.orderTop := by
  have hx : x != 0 := orderTop_ne_top.1 hxy.ne_top
  let g : Γ := Set.IsWF.min x.isWF_support (support_nonempty_iff.2 hx)
  have hcxyne : (x + y).coeff g != 0 := by
    rw [coeff_add]; rw [coeff_eq_zero_of_lt_orderTop (lt_of_eq_of_lt (orderTop_of_ne_zero hx).symm hxy)]; rw [add_zero]
    exact coeff_orderTop_ne (orderTop_of_ne_zero hx)
  have hxyx : (x + y).orderTop <= x.orderTop := by
    rw [orderTop_of_ne_zero hx]
    exact orderTop_le_of_coeff_ne_zero hcxyne
  exact le_antisymm hxyx (le_of_eq_of_le (min_eq_left_of_lt hxy).symm min_orderTop_le_orderTop_add)

/--
theorem `orderTop_add_eq_right` / 定理 `orderTop_add_eq_right`

English:
theorem orderTop_add_eq_right
  statement: {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
  proof: by
  simpa [← map_add, ← AddOpposite.op_add, hxy] using orderTop_add_eq_left
    (x := addOppositeEquiv.symm (.op y))
    (y := addOppositeEquiv.symm (.op x))

中文:
定理 orderTop_add_eq_right
  结论: {Γ} [线性序 Γ] {x y : R⟦Γ⟧}
  证明: by
  simpa [← map_add, ← AddOpposite.op_add, hxy] using orderTop_add_eq_left
    (x := addOppositeEquiv.symm (.op y))
    (y := addOppositeEquiv.symm (.op x))

Depends on / 依赖: AddOpposite, AddOpposite.op_add, addOppositeEquiv, addOppositeEquiv.symm, map_add, op_add, orderTop_add_eq_left
-/
theorem orderTop_add_eq_right {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : y.orderTop < x.orderTop) : (x + y).orderTop = y.orderTop := by
  simpa [← map_add, ← AddOpposite.op_add, hxy] using orderTop_add_eq_left
    (x := addOppositeEquiv.symm (.op y))
    (y := addOppositeEquiv.symm (.op x))

/--
theorem `leadingCoeff_add_eq_left` / 定理 `leadingCoeff_add_eq_left`

English:
theorem leadingCoeff_add_eq_left
  statement: {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
  proof: by
  have hx : x != 0 := orderTop_ne_top.1 hxy.ne_top
  have ho : (x + y).orderTop = x.orderTop := orderTop_add_eq_left hxy
  by_cases h : x + y = 0
  · rw [h, orderTop_zero] at ho
    rw [h]; rw [orderTop_eq_top.mp ho.symm]
  · simp_rw [leadingCoeff_of_ne_zero h, leadingCoeff_of_ne_zero hx, ho, coeff_add]
    rw [coeff_eq_zero_of_lt_orderTop (x := y) (by simpa using hxy)]; rw [add_zero]

中文:
定理 leadingCoeff_add_eq_left
  结论: {Γ} [线性序 Γ] {x y : R⟦Γ⟧}
  证明: by
  have hx : x != 0 := orderTop_ne_top.1 hxy.ne_top
  have ho : (x + y).orderTop = x.orderTop := orderTop_add_eq_left hxy
  by_cases h : x + y = 0
  · rw [h, orderTop_zero] at ho
    rw [h]; rw [orderTop_eq_top.mp ho.symm]
  · simp_rw [leadingCoeff_of_ne_zero h, leadingCoeff_of_ne_zero hx, ho, coeff_add]
    rw [coeff_eq_zero_of_lt_orderTop (x := y) (by simpa using hxy)]; rw [add_zero]

Depends on / 依赖: add_zero, coeff_add, coeff_eq_zero_of_lt_orderTop, ho.symm, hxy.ne_top, leadingCoeff_of_ne_zero, ne_top, orderTop, orderTop_add_eq_left, orderTop_eq_top, orderTop_eq_top.mp, orderTop_ne_top, orderTop_zero, simp_rw, x.orderTop
-/
theorem leadingCoeff_add_eq_left {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : x.orderTop < y.orderTop) : (x + y).leadingCoeff = x.leadingCoeff := by
  have hx : x != 0 := orderTop_ne_top.1 hxy.ne_top
  have ho : (x + y).orderTop = x.orderTop := orderTop_add_eq_left hxy
  by_cases h : x + y = 0
  · rw [h, orderTop_zero] at ho
    rw [h]; rw [orderTop_eq_top.mp ho.symm]
  · simp_rw [leadingCoeff_of_ne_zero h, leadingCoeff_of_ne_zero hx, ho, coeff_add]
    rw [coeff_eq_zero_of_lt_orderTop (x := y) (by simpa using hxy)]; rw [add_zero]

/--
theorem `leadingCoeff_add_eq_right` / 定理 `leadingCoeff_add_eq_right`

English:
theorem leadingCoeff_add_eq_right
  statement: {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
  proof: by
  simpa [← map_add, ← AddOpposite.op_add, hxy] using leadingCoeff_add_eq_left
    (x := addOppositeEquiv.symm (.op y))
    (y := addOppositeEquiv.symm (.op x))

中文:
定理 leadingCoeff_add_eq_right
  结论: {Γ} [线性序 Γ] {x y : R⟦Γ⟧}
  证明: by
  simpa [← map_add, ← AddOpposite.op_add, hxy] using leadingCoeff_add_eq_left
    (x := addOppositeEquiv.symm (.op y))
    (y := addOppositeEquiv.symm (.op x))

Depends on / 依赖: AddOpposite, AddOpposite.op_add, addOppositeEquiv, addOppositeEquiv.symm, leadingCoeff_add_eq_left, map_add, op_add
-/
theorem leadingCoeff_add_eq_right {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : y.orderTop < x.orderTop) : (x + y).leadingCoeff = y.leadingCoeff := by
  simpa [← map_add, ← AddOpposite.op_add, hxy] using leadingCoeff_add_eq_left
    (x := addOppositeEquiv.symm (.op y))
    (y := addOppositeEquiv.symm (.op x))

/--
theorem `ne_zero_of_eq_add_single` / 定理 `ne_zero_of_eq_add_single`

English:
theorem ne_zero_of_eq_add_single
  statement: [Zero Γ] {x y : R⟦Γ⟧}
  proof: by
  by_contra h
  simp only [h, order_zero, leadingCoeff_zero, map_zero, add_zero] at hxy
  exact hy hxy.symm

中文:
定理 ne_zero_of_eq_add_single
  结论: [零 Γ] {x y : R⟦Γ⟧}
  证明: by
  by_contra h
  simp only [h, order_zero, leadingCoeff_zero, map_zero, add_zero] at hxy
  exact hy hxy.symm

Depends on / 依赖: add_zero, hxy.symm, leadingCoeff_zero, map_zero, order_zero
-/
theorem ne_zero_of_eq_add_single [Zero Γ] {x y : R⟦Γ⟧}
    (hxy : x = y + single x.order x.leadingCoeff) (hy : y != 0) : x != 0 := by
  by_contra h
  simp only [h, order_zero, leadingCoeff_zero, map_zero, add_zero] at hxy
  exact hy hxy.symm

/--
theorem `coeff_order_of_eq_add_single` / 定理 `coeff_order_of_eq_add_single`

English:
theorem coeff_order_of_eq_add_single
  statement: {R} [AddCancelCommMonoid R] [Zero Γ] {x y : R⟦Γ⟧}
  proof: by
  simpa [← leadingCoeff_eq] using congr(($hxy).coeff x.order)

中文:
定理 coeff_order_of_eq_add_single
  结论: {R} [加法消去交换幺半群 R] [零 Γ] {x y : R⟦Γ⟧}
  证明: by
  simpa [← leadingCoeff_eq] using congr(($hxy).coeff x.order)

Depends on / 依赖: leadingCoeff_eq, x.order
-/
theorem coeff_order_of_eq_add_single {R} [AddCancelCommMonoid R] [Zero Γ] {x y : R⟦Γ⟧}
    (hxy : x = y + single x.order x.leadingCoeff) : y.coeff x.order = 0 := by
  simpa [← leadingCoeff_eq] using congr(($hxy).coeff x.order)

/--
theorem `order_lt_order_of_eq_add_single` / 定理 `order_lt_order_of_eq_add_single`

English:
theorem order_lt_order_of_eq_add_single
  statement: {R} {Γ} [LinearOrder Γ] [Zero Γ] [AddCancelCommMonoid R]
  proof: by
  have : x.order != y.order := by
    intro h
have hyne : single y.order y.leadingCoeff != 0 := single_ne_zero leadingCoeff_ne_zero.mpr hy
    rw [leadingCoeff_eq]; rw [← h]; rw [coeff_order_of_eq_add_single hxy]; rw [single_eq_zero] at hyne
    exact hyne rfl
  refine lt_of_le_of_ne ?_ this
  simp only [order, ne_zero_of_eq_add_single hxy hy, ↓reduceDIte, hy]
  refine Set.IsWF.min_le_min_of_subset fun g hg => ?_
  obtain rfl | hgx := eq_or_ne g x.order
· simpa using coeff_order_eq_zero.not.2 ne_zero_of_eq_add_single hxy hy
  · have : x.coeff g = (y + (single x.order) x.leadingCoeff).coeff g := by rw [← hxy]
    rw [coeff_add]; rw [coeff_single_of_ne hgx]; rw [add_zero] at this
    simpa [this] using hg

中文:
定理 order_lt_order_of_eq_add_single
  结论: {R} {Γ} [线性序 Γ] [零 Γ] [加法消去交换幺半群 R]
  证明: by
  have : x.order != y.order := by
    intro h
have hyne : single y.order y.leadingCoeff != 0 := single_ne_zero leadingCoeff_ne_zero.mpr hy
    rw [leadingCoeff_eq]; rw [← h]; rw [coeff_order_of_eq_add_single hxy]; rw [single_eq_zero] at hyne
    exact hyne rfl
  refine lt_of_le_of_ne ?_ this
  simp only [order, ne_zero_of_eq_add_single hxy hy, ↓reduceDIte, hy]
  refine Set.IsWF.min_le_min_of_subset fun g hg => ?_
  obtain rfl | hgx := eq_or_ne g x.order
· simpa using coeff_order_eq_zero.not.2 ne_zero_of_eq_add_single hxy hy
  · have : x.coeff g = (y + (single x.order) x.leadingCoeff).coeff g := by rw [← hxy]
    rw [coeff_add]; rw [coeff_single_of_ne hgx]; rw [add_zero] at this
    simpa [this] using hg

Depends on / 依赖: Set.IsWF.min_le_min_of_subset, coeff_order_eq_zero, coeff_order_eq_zero.not, coeff_order_of_eq_add_single, eq_or_ne, leadingCoeff, leadingCoeff_eq, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, lt_of_le_of_ne, min_le_min_of_subset, ne_zero_of_eq_add_sin, ne_zero_of_eq_add_single, reduceDIte, single, single_eq_zero, single_ne_zero, x.order, y.leadingCoeff, y.order
-/
theorem order_lt_order_of_eq_add_single {R} {Γ} [LinearOrder Γ] [Zero Γ] [AddCancelCommMonoid R]
    {x y : R⟦Γ⟧} (hxy : x = y + single x.order x.leadingCoeff) (hy : y != 0) :
    x.order < y.order := by
  have : x.order != y.order := by
    intro h
have hyne : single y.order y.leadingCoeff != 0 := single_ne_zero leadingCoeff_ne_zero.mpr hy
    rw [leadingCoeff_eq]; rw [← h]; rw [coeff_order_of_eq_add_single hxy]; rw [single_eq_zero] at hyne
    exact hyne rfl
  refine lt_of_le_of_ne ?_ this
  simp only [order, ne_zero_of_eq_add_single hxy hy, ↓reduceDIte, hy]
  refine Set.IsWF.min_le_min_of_subset fun g hg => ?_
  obtain rfl | hgx := eq_or_ne g x.order
· simpa using coeff_order_eq_zero.not.2 ne_zero_of_eq_add_single hxy hy
  · have : x.coeff g = (y + (single x.order) x.leadingCoeff).coeff g := by rw [← hxy]
    rw [coeff_add]; rw [coeff_single_of_ne hgx]; rw [add_zero] at this
    simpa [this] using hg

/-- `single` as an additive monoid/group homomorphism -/
@[simps!]
/--
Definition of `single.addMonoidHom` / `single.addMonoidHom` 的定义

English:
definition single.addMonoidHom
  signature: (a : Γ)
  body: { single a with
    map_add' := single_add _ }

中文:
定义 single.addMonoidHom
  签名: (a : Γ)
  定义体: { single a with
    map_add' := single_add _ }

Depends on / 依赖: map_add, single, single_add
-/
def single.addMonoidHom (a : Γ) : R ->+ R⟦Γ⟧ :=
  { single a with
    map_add' := single_add _ }

/-- `coeff g` as an additive monoid/group homomorphism -/
@[simps]
/--
Definition of `coeff.addMonoidHom` / `coeff.addMonoidHom` 的定义

English:
definition coeff.addMonoidHom
  signature: (g : Γ)
  body: f.coeff g
  map_zero' := coeff_zero
  map_add' _ _ := coeff_add

中文:
定义 coeff.addMonoidHom
  签名: (g : Γ)
  定义体: f.coeff g
  map_zero' := coeff_zero
  map_add' _ _ := coeff_add

Depends on / 依赖: f.coeff
-/
def coeff.addMonoidHom (g : Γ) : R⟦Γ⟧ ->+ R where
  toFun f := f.coeff g
  map_zero' := coeff_zero
  map_add' _ _ := coeff_add

section Domain

variable [PartialOrder Γ']

/--
theorem `embDomain_add` / 定理 `embDomain_add`

English:
theorem embDomain_add
  given: (f : Γ ↪o Γ') (x y : R⟦Γ⟧)
  proof: by
  ext g
  by_cases hg : g in Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_of_notMem_range hg]

中文:
定理 embDomain_add
  条件: (f : Γ ↪o Γ') (x y : R⟦Γ⟧)
  证明: by
  ext g
  by_cases hg : g in Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_of_notMem_range hg]

Depends on / 依赖: Set.range, embDomain_of_notMem_range
-/
theorem embDomain_add (f : Γ ↪o Γ') (x y : R⟦Γ⟧) :
    embDomain f (x + y) = embDomain f x + embDomain f y := by
  ext g
  by_cases hg : g in Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_of_notMem_range hg]

end Domain

/--
theorem `truncLT_add` / 定理 `truncLT_add`

English:
theorem truncLT_add
  given: [DecidableLT Γ] (c : Γ) (x y : R⟦Γ⟧)
  proof: by
  ext i
  by_cases h : i < c <;> simp [h]

中文:
定理 truncLT_add
  条件: [DecidableLT Γ] (c : Γ) (x y : R⟦Γ⟧)
  证明: by
  ext i
  by_cases h : i < c <;> simp [h]
-/
theorem truncLT_add [DecidableLT Γ] (c : Γ) (x y : R⟦Γ⟧) :
    truncLT c (x + y) = truncLT c x + truncLT c y := by
  ext i
  by_cases h : i < c <;> simp [h]

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid R⟦Γ⟧
  body: by
    ext
    apply add_comm

@[simp]

中文:
实例 :
  签名: 加法交换幺半群 R⟦Γ⟧
  定义体: by
    ext
    apply add_comm

@[simp]

Depends on / 依赖: add_comm
-/
instance : AddCommMonoid R⟦Γ⟧ where
  add_comm x y := by
    ext
    apply add_comm

@[simp]
/--
theorem `coeff_sum` / 定理 `coeff_sum`

English:
theorem coeff_sum
  given: {s : Finset α} {x : α -> R⟦Γ⟧} (g : Γ)
  proof: cons_induction rfl (fun i s his hsum => by rw [sum_cons, sum_cons, coeff_add, hsum]) s

中文:
定理 coeff_sum
  条件: {s : 有限集 α} {x : α -> R⟦Γ⟧} (g : Γ)
  证明: cons_induction rfl (fun i s his hsum => by rw [sum_cons, sum_cons, coeff_add, hsum]) s

Depends on / 依赖: coeff_add, cons_induction, sum_cons
-/
theorem coeff_sum {s : Finset α} {x : α -> R⟦Γ⟧} (g : Γ) :
    (∑ i in s, x i).coeff g = ∑ i in s, (x i).coeff g :=
  cons_induction rfl (fun i s his hsum => by rw [sum_cons, sum_cons, coeff_add, hsum]) s

end AddCommMonoid

section NegZeroClass

variable [NegZeroClass R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg R⟦Γ⟧
  body: x.map (-ZeroHom.id _)

中文:
实例 :
  签名: 取负 R⟦Γ⟧
  定义体: x.map (-ZeroHom.id _)

Depends on / 依赖: ZeroHom, ZeroHom.id, x.map
-/
instance : Neg R⟦Γ⟧ where
  neg x := x.map (-ZeroHom.id _)

/--
theorem `support_neg_subset` / 定理 `support_neg_subset`

English:
theorem support_neg_subset
  given: (x : R⟦Γ⟧)
  statement: (-x).support subseteq x.support
  proof: support_map_subset ..

@[simp]

中文:
定理 support_neg_subset
  条件: (x : R⟦Γ⟧)
  结论: (-x).support subseteq x.support
  证明: support_map_subset ..

@[simp]

Depends on / 依赖: support_map_subset
-/
theorem support_neg_subset (x : R⟦Γ⟧) : (-x).support subseteq x.support :=
  support_map_subset ..

@[simp]
/--
theorem `coeff_neg'` / 定理 `coeff_neg'`

English:
theorem coeff_neg'
  given: (x : R⟦Γ⟧)
  statement: (-x).coeff = -x.coeff
  proof: rfl

中文:
定理 coeff_neg'
  条件: (x : R⟦Γ⟧)
  结论: (-x).coeff = -x.coeff
  证明: rfl
-/
theorem coeff_neg' (x : R⟦Γ⟧) : (-x).coeff = -x.coeff :=
  rfl

/--
theorem `coeff_neg` / 定理 `coeff_neg`

English:
theorem coeff_neg
  given: {x : R⟦Γ⟧} {a : Γ}
  statement: (-x).coeff a = -x.coeff a
  proof: rfl

中文:
定理 coeff_neg
  条件: {x : R⟦Γ⟧} {a : Γ}
  结论: (-x).coeff a = -x.coeff a
  证明: rfl
-/
theorem coeff_neg {x : R⟦Γ⟧} {a : Γ} : (-x).coeff a = -x.coeff a :=
  rfl

end NegZeroClass

section AddGroup

variable [AddGroup R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub R⟦Γ⟧
  body: { coeff := x.coeff - y.coeff
      isPWO_support' := (x.isPWO_support.union y.isPWO_support).mono (Function.support_sub ..) }

中文:
实例 :
  签名: 减法 R⟦Γ⟧
  定义体: { coeff := x.coeff - y.coeff
      isPWO_support' := (x.isPWO_support.union y.isPWO_support).mono (Function.support_sub ..) }

Depends on / 依赖: Function, Function.support_sub, isPWO_support, support_sub, x.coeff, x.isPWO_support.union, y.coeff, y.isPWO_support
-/
instance : Sub R⟦Γ⟧ where
  sub x y :=
    { coeff := x.coeff - y.coeff
      isPWO_support' := (x.isPWO_support.union y.isPWO_support).mono (Function.support_sub ..) }

/--
theorem `support_sub_subset` / 定理 `support_sub_subset`

English:
theorem support_sub_subset
  given: (x y : R⟦Γ⟧)
  statement: (x - y).support subseteq x.support union y.support
  proof: Function.support_sub ..

@[simp]

中文:
定理 support_sub_subset
  条件: (x y : R⟦Γ⟧)
  结论: (x - y).support subseteq x.support union y.support
  证明: Function.support_sub ..

@[simp]

Depends on / 依赖: Function, Function.support_sub, support_sub
-/
theorem support_sub_subset (x y : R⟦Γ⟧) : (x - y).support subseteq x.support union y.support :=
  Function.support_sub ..

@[simp]
/--
theorem `coeff_sub'` / 定理 `coeff_sub'`

English:
theorem coeff_sub'
  given: (x y : R⟦Γ⟧)
  statement: (x - y).coeff = x.coeff - y.coeff
  proof: rfl

中文:
定理 coeff_sub'
  条件: (x y : R⟦Γ⟧)
  结论: (x - y).coeff = x.coeff - y.coeff
  证明: rfl
-/
theorem coeff_sub' (x y : R⟦Γ⟧) : (x - y).coeff = x.coeff - y.coeff :=
  rfl

/--
theorem `coeff_sub` / 定理 `coeff_sub`

English:
theorem coeff_sub
  given: {x y : R⟦Γ⟧} {a : Γ}
  statement: (x - y).coeff a = x.coeff a - y.coeff a
  proof: rfl

中文:
定理 coeff_sub
  条件: {x y : R⟦Γ⟧} {a : Γ}
  结论: (x - y).coeff a = x.coeff a - y.coeff a
  证明: rfl
-/
theorem coeff_sub {x y : R⟦Γ⟧} {a : Γ} : (x - y).coeff a = x.coeff a - y.coeff a :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddGroup R⟦Γ⟧
  body: fast_instance%
  coeff_injective.addGroup _
    coeff_zero' coeff_add' coeff_neg' coeff_sub'
    (fun _ _ => coeff_smul' _ _) (fun _ _ => coeff_smul' _ _)

@[simp]

中文:
实例 :
  签名: 加法群 R⟦Γ⟧
  定义体: fast_instance%
  coeff_injective.addGroup _
    coeff_zero' coeff_add' coeff_neg' coeff_sub'
    (fun _ _ => coeff_smul' _ _) (fun _ _ => coeff_smul' _ _)

@[simp]

Depends on / 依赖: fast_instance
-/
instance : AddGroup R⟦Γ⟧ := fast_instance%
  coeff_injective.addGroup _
    coeff_zero' coeff_add' coeff_neg' coeff_sub'
    (fun _ _ => coeff_smul' _ _) (fun _ _ => coeff_smul' _ _)

@[simp]
/--
theorem `single_sub` / 定理 `single_sub`

English:
theorem single_sub
  given: (a : Γ) (r s : R)
  statement: single a (r - s) = single a r - single a s
  proof: map_sub (single.addMonoidHom a) _ _

@[simp]

中文:
定理 single_sub
  条件: (a : Γ) (r s : R)
  结论: single a (r - s) = single a r - single a s
  证明: map_sub (single.addMonoidHom a) _ _

@[simp]

Depends on / 依赖: addMonoidHom, map_sub, single, single.addMonoidHom
-/
theorem single_sub (a : Γ) (r s : R) : single a (r - s) = single a r - single a s :=
  map_sub (single.addMonoidHom a) _ _

@[simp]
/--
theorem `single_neg` / 定理 `single_neg`

English:
theorem single_neg
  given: (a : Γ) (r : R)
  statement: single a (-r) = -single a r
  proof: map_neg (single.addMonoidHom a) _

@[simp]

中文:
定理 single_neg
  条件: (a : Γ) (r : R)
  结论: single a (-r) = -single a r
  证明: map_neg (single.addMonoidHom a) _

@[simp]

Depends on / 依赖: addMonoidHom, map_neg, single, single.addMonoidHom
-/
theorem single_neg (a : Γ) (r : R) : single a (-r) = -single a r :=
  map_neg (single.addMonoidHom a) _

@[simp]
/--
theorem `support_neg` / 定理 `support_neg`

English:
theorem support_neg
  given: {x : R⟦Γ⟧}
  statement: (-x).support = x.support
  proof: by
  ext
  simp

@[simp]

中文:
定理 support_neg
  条件: {x : R⟦Γ⟧}
  结论: (-x).support = x.support
  证明: by
  ext
  simp

@[simp]
-/
theorem support_neg {x : R⟦Γ⟧} : (-x).support = x.support := by
  ext
  simp

@[simp]
/--
lemma `map_neg` / 引理 `map_neg`

English:
lemma map_neg
  given: [AddGroup S] (f : R ->+ S) {x : R⟦Γ⟧}
  proof: by
  ext; simp

@[simp]

中文:
引理 map_neg
  条件: [加法群 S] (f : R ->+ S) {x : R⟦Γ⟧}
  证明: by
  ext; simp

@[simp]
-/
protected lemma map_neg [AddGroup S] (f : R ->+ S) {x : R⟦Γ⟧} :
    ((-x).map f : S⟦Γ⟧) = -x.map f := by
  ext; simp

@[simp]
/--
theorem `orderTop_neg` / 定理 `orderTop_neg`

English:
theorem orderTop_neg
  given: {x : R⟦Γ⟧}
  statement: (-x).orderTop = x.orderTop
  proof: by
  classical simp only [orderTop, support_neg, neg_eq_zero]

@[simp]

中文:
定理 orderTop_neg
  条件: {x : R⟦Γ⟧}
  结论: (-x).orderTop = x.orderTop
  证明: by
  classical simp only [orderTop, support_neg, neg_eq_zero]

@[simp]

Depends on / 依赖: classical, neg_eq_zero, orderTop, support_neg
-/
theorem orderTop_neg {x : R⟦Γ⟧} : (-x).orderTop = x.orderTop := by
  classical simp only [orderTop, support_neg, neg_eq_zero]

@[simp]
/--
theorem `order_neg` / 定理 `order_neg`

English:
theorem order_neg
  given: [Zero Γ] {f : R⟦Γ⟧}
  statement: (-f).order = f.order
  proof: by
  classical
  by_cases hf : f = 0
  · simp only [hf, neg_zero]
  simp only [order, support_neg, neg_eq_zero]

中文:
定理 order_neg
  条件: [零 Γ] {f : R⟦Γ⟧}
  结论: (-f).order = f.order
  证明: by
  classical
  by_cases hf : f = 0
  · simp only [hf, neg_zero]
  simp only [order, support_neg, neg_eq_zero]

Depends on / 依赖: classical, neg_eq_zero, neg_zero, support_neg
-/
theorem order_neg [Zero Γ] {f : R⟦Γ⟧} : (-f).order = f.order := by
  classical
  by_cases hf : f = 0
  · simp only [hf, neg_zero]
  simp only [order, support_neg, neg_eq_zero]

/--
theorem `leadingCoeff_neg` / 定理 `leadingCoeff_neg`

English:
theorem leadingCoeff_neg
  given: {x : R⟦Γ⟧}
  statement: (-x).leadingCoeff = -x.leadingCoeff
  proof: by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [leadingCoeff_of_ne_zero, *]

@[simp]

中文:
定理 leadingCoeff_neg
  条件: {x : R⟦Γ⟧}
  结论: (-x).leadingCoeff = -x.leadingCoeff
  证明: by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [leadingCoeff_of_ne_zero, *]

@[simp]

Depends on / 依赖: eq_or_ne, leadingCoeff_of_ne_zero
-/
theorem leadingCoeff_neg {x : R⟦Γ⟧} : (-x).leadingCoeff = -x.leadingCoeff := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [leadingCoeff_of_ne_zero, *]

@[simp]
/--
lemma `map_sub` / 引理 `map_sub`

English:
lemma map_sub
  given: [AddGroup S] (f : R ->+ S) {x y : R⟦Γ⟧}
  proof: by
  ext; simp

中文:
引理 map_sub
  条件: [加法群 S] (f : R ->+ S) {x y : R⟦Γ⟧}
  证明: by
  ext; simp
-/
protected lemma map_sub [AddGroup S] (f : R ->+ S) {x y : R⟦Γ⟧} :
    ((x - y).map f : S⟦Γ⟧) = x.map f - y.map f := by
  ext; simp

/--
theorem `min_orderTop_le_orderTop_sub` / 定理 `min_orderTop_le_orderTop_sub`

English:
theorem min_orderTop_le_orderTop_sub
  given: {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
  proof: by
  rw [sub_eq_add_neg]; rw [← orderTop_neg (x := y)]
  exact min_orderTop_le_orderTop_add

中文:
定理 min_orderTop_le_orderTop_sub
  条件: {Γ} [线性序 Γ] {x y : R⟦Γ⟧}
  证明: by
  rw [sub_eq_add_neg]; rw [← orderTop_neg (x := y)]
  exact min_orderTop_le_orderTop_add

Depends on / 依赖: min_orderTop_le_orderTop_add, orderTop_neg, sub_eq_add_neg
-/
theorem min_orderTop_le_orderTop_sub {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} :
    min x.orderTop y.orderTop <= (x - y).orderTop := by
  rw [sub_eq_add_neg]; rw [← orderTop_neg (x := y)]
  exact min_orderTop_le_orderTop_add

/--
theorem `orderTop_sub` / 定理 `orderTop_sub`

English:
theorem orderTop_sub
  statement: {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
  proof: by
  rw [sub_eq_add_neg]
  rw [← orderTop_neg (x := y)] at hxy
  exact orderTop_add_eq_left hxy

中文:
定理 orderTop_sub
  结论: {Γ} [线性序 Γ] {x y : R⟦Γ⟧}
  证明: by
  rw [sub_eq_add_neg]
  rw [← orderTop_neg (x := y)] at hxy
  exact orderTop_add_eq_left hxy

Depends on / 依赖: orderTop_add_eq_left, orderTop_neg, sub_eq_add_neg
-/
theorem orderTop_sub {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : x.orderTop < y.orderTop) : (x - y).orderTop = x.orderTop := by
  rw [sub_eq_add_neg]
  rw [← orderTop_neg (x := y)] at hxy
  exact orderTop_add_eq_left hxy

/--
theorem `leadingCoeff_sub` / 定理 `leadingCoeff_sub`

English:
theorem leadingCoeff_sub
  statement: {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
  proof: by
  rw [sub_eq_add_neg]
  rw [← orderTop_neg (x := y)] at hxy
  exact leadingCoeff_add_eq_left hxy

中文:
定理 leadingCoeff_sub
  结论: {Γ} [线性序 Γ] {x y : R⟦Γ⟧}
  证明: by
  rw [sub_eq_add_neg]
  rw [← orderTop_neg (x := y)] at hxy
  exact leadingCoeff_add_eq_left hxy

Depends on / 依赖: leadingCoeff_add_eq_left, orderTop_neg, sub_eq_add_neg
-/
theorem leadingCoeff_sub {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : x.orderTop < y.orderTop) : (x - y).leadingCoeff = x.leadingCoeff := by
  rw [sub_eq_add_neg]
  rw [← orderTop_neg (x := y)] at hxy
  exact leadingCoeff_add_eq_left hxy

/--
theorem `orderTop_sub_ne` / 定理 `orderTop_sub_ne`

English:
theorem orderTop_sub_ne
  statement: {x y : R⟦Γ⟧} {g : Γ}
  proof: by
  refine orderTop_ne_of_coeff_eq_zero ?_
  have hx : x != 0 := fun h => by simp_all [orderTop_zero, WithTop.top_ne_coe]
  rw [orderTop_of_ne_zero hx]; rw [WithTop.coe_eq_coe] at hxg
  have hy : y != 0 := fun h => by simp_all [orderTop_zero, WithTop.top_ne_coe]
  rw [orderTop_of_ne_zero hy]; rw [WithTop.coe_eq_coe] at hyg
  simp only [leadingCoeff_of_ne_zero hx, leadingCoeff_of_ne_zero hy, untop_orderTop_of_ne_zero hx,
    untop_orderTop_of_ne_zero hy, hxg, hyg] at hxyc
  rwa [coeff_sub, sub_eq_zero]

中文:
定理 orderTop_sub_ne
  结论: {x y : R⟦Γ⟧} {g : Γ}
  证明: by
  refine orderTop_ne_of_coeff_eq_zero ?_
  have hx : x != 0 := fun h => by simp_all [orderTop_zero, WithTop.top_ne_coe]
  rw [orderTop_of_ne_zero hx]; rw [WithTop.coe_eq_coe] at hxg
  have hy : y != 0 := fun h => by simp_all [orderTop_zero, WithTop.top_ne_coe]
  rw [orderTop_of_ne_zero hy]; rw [WithTop.coe_eq_coe] at hyg
  simp only [leadingCoeff_of_ne_zero hx, leadingCoeff_of_ne_zero hy, untop_orderTop_of_ne_zero hx,
    untop_orderTop_of_ne_zero hy, hxg, hyg] at hxyc
  rwa [coeff_sub, sub_eq_zero]

Depends on / 依赖: WithTop, WithTop.coe_eq_coe, WithTop.top_ne_coe, coe_eq_coe, coeff_sub, leadingCoeff_of_ne_zero, orderTop_ne_of_coeff_eq_zero, orderTop_of_ne_zero, orderTop_zero, sub_eq_zero, top_ne_coe, untop_orderTop_of_ne_zero
-/
theorem orderTop_sub_ne {x y : R⟦Γ⟧} {g : Γ}
    (hxg : x.orderTop = g) (hyg : y.orderTop = g) (hxyc : x.leadingCoeff = y.leadingCoeff) :
    (x - y).orderTop != g := by
  refine orderTop_ne_of_coeff_eq_zero ?_
  have hx : x != 0 := fun h => by simp_all [orderTop_zero, WithTop.top_ne_coe]
  rw [orderTop_of_ne_zero hx]; rw [WithTop.coe_eq_coe] at hxg
  have hy : y != 0 := fun h => by simp_all [orderTop_zero, WithTop.top_ne_coe]
  rw [orderTop_of_ne_zero hy]; rw [WithTop.coe_eq_coe] at hyg
  simp only [leadingCoeff_of_ne_zero hx, leadingCoeff_of_ne_zero hy, untop_orderTop_of_ne_zero hx,
    untop_orderTop_of_ne_zero hy, hxg, hyg] at hxyc
  rwa [coeff_sub, sub_eq_zero]

/--
theorem `le_orderTop_of_leadingCoeff_eq` / 定理 `le_orderTop_of_leadingCoeff_eq`

English:
theorem le_orderTop_of_leadingCoeff_eq
  statement: {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} {g : Γ}
  proof: lt_of_le_of_ne (le_of_eq_of_le (by rw [hxg, hyg, inf_idem]) min_orderTop_le_orderTop_sub)
    (orderTop_sub_ne hxg hyg hxyc).symm

中文:
定理 le_orderTop_of_leadingCoeff_eq
  结论: {Γ} [线性序 Γ] {x y : R⟦Γ⟧} {g : Γ}
  证明: lt_of_le_of_ne (le_of_eq_of_le (by rw [hxg, hyg, inf_idem]) min_orderTop_le_orderTop_sub)
    (orderTop_sub_ne hxg hyg hxyc).symm

Depends on / 依赖: inf_idem, le_of_eq_of_le, lt_of_le_of_ne, min_orderTop_le_orderTop_sub, orderTop_sub_ne
-/
theorem le_orderTop_of_leadingCoeff_eq {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} {g : Γ}
    (hxg : x.orderTop = g) (hyg : y.orderTop = g) (hxyc : x.leadingCoeff = y.leadingCoeff) :
    g < (x - y).orderTop :=
  lt_of_le_of_ne (le_of_eq_of_le (by rw [hxg, hyg, inf_idem]) min_orderTop_le_orderTop_sub)
    (orderTop_sub_ne hxg hyg hxyc).symm

end AddGroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroup
  signature: R] : AddCommGroup R⟦Γ⟧ where

中文:
实例 [加法交换群
  签名: R] : 加法交换群 R⟦Γ⟧ where
-/
instance [AddCommGroup R] : AddCommGroup R⟦Γ⟧ where

end Addition

section DistribMulAction

variable [PartialOrder Γ] {V : Type*} [Monoid R] [AddMonoid V] [DistribMulAction R V]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribMulAction R V⟦Γ⟧
  body: by
    ext
    simp
  smul_zero _ := by
    ext
    simp
  smul_add _ _ _ := by
    ext
    simp [smul_add]
  mul_smul _ _ _ := by
    ext
    simp [mul_smul]

中文:
实例 :
  签名: 分配乘法作用 R V⟦Γ⟧
  定义体: by
    ext
    simp
  smul_zero _ := by
    ext
    simp
  smul_add _ _ _ := by
    ext
    simp [smul_add]
  mul_smul _ _ _ := by
    ext
    simp [mul_smul]

Depends on / 依赖: mul_smul, smul_add, smul_zero
-/
instance : DistribMulAction R V⟦Γ⟧ where
  one_smul _ := by
    ext
    simp
  smul_zero _ := by
    ext
    simp
  smul_add _ _ _ := by
    ext
    simp [smul_add]
  mul_smul _ _ _ := by
    ext
    simp [mul_smul]

variable {S : Type*} [Monoid S] [DistribMulAction S V]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R S] [IsScalarTower R S V] : IsScalarTower R S V⟦Γ⟧
  body: ⟨fun r s a => by
    ext
    simp⟩

中文:
实例 [标量乘法
  签名: R S] [标量塔 R S V] : 标量塔 R S V⟦Γ⟧
  定义体: ⟨fun r s a => by
    ext
    simp⟩
-/
instance [SMul R S] [IsScalarTower R S V] : IsScalarTower R S V⟦Γ⟧ :=
  ⟨fun r s a => by
    ext
    simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: R S V] : SMulCommClass R S V⟦Γ⟧
  body: ⟨fun r s a => by
    ext
    simp [smul_comm]⟩

中文:
实例 [标量交换类
  签名: R S V] : 标量交换类 R S V⟦Γ⟧
  定义体: ⟨fun r s a => by
    ext
    simp [smul_comm]⟩

Depends on / 依赖: smul_comm
-/
instance [SMulCommClass R S V] : SMulCommClass R S V⟦Γ⟧ :=
  ⟨fun r s a => by
    ext
    simp [smul_comm]⟩

end DistribMulAction

section Module

variable [PartialOrder Γ] [Semiring R] [AddCommMonoid V] [Module R V]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R V⟦Γ⟧
  body: by
    ext
    simp
  add_smul _ _ _ := by
    ext
    simp [add_smul]

中文:
实例 :
  签名: 模 R V⟦Γ⟧
  定义体: by
    ext
    simp
  add_smul _ _ _ := by
    ext
    simp [add_smul]

Depends on / 依赖: add_smul
-/
instance : Module R V⟦Γ⟧ where
  zero_smul _ := by
    ext
    simp
  add_smul _ _ _ := by
    ext
    simp [add_smul]

/-- `single` as a linear map -/
@[simps]
/--
Definition of `single.linearMap` / `single.linearMap` 的定义

English:
definition single.linearMap
  signature: (a : Γ)
  body: { single.addMonoidHom a with
    map_smul' := fun r s => by
      ext b
      by_cases h : b = a <;> simp [h] }

中文:
定义 single.linearMap
  签名: (a : Γ)
  定义体: { single.addMonoidHom a with
    map_smul' := fun r s => by
      ext b
      by_cases h : b = a <;> simp [h] }

Depends on / 依赖: addMonoidHom, map_smul, single, single.addMonoidHom
-/
def single.linearMap (a : Γ) : V ->ₗ[R] V⟦Γ⟧ :=
  { single.addMonoidHom a with
    map_smul' := fun r s => by
      ext b
      by_cases h : b = a <;> simp [h] }

/-- `coeff g` as a linear map -/
@[simps]
/--
Definition of `coeff.linearMap` / `coeff.linearMap` 的定义

English:
definition coeff.linearMap
  signature: (g : Γ)
  body: { coeff.addMonoidHom g with map_smul' := fun _ _ => rfl }

@[simp]

中文:
定义 coeff.linearMap
  签名: (g : Γ)
  定义体: { coeff.addMonoidHom g with map_smul' := fun _ _ => rfl }

@[simp]

Depends on / 依赖: addMonoidHom, coeff.addMonoidHom, map_smul
-/
def coeff.linearMap (g : Γ) : V⟦Γ⟧ ->ₗ[R] V :=
  { coeff.addMonoidHom g with map_smul' := fun _ _ => rfl }

@[simp]
/--
lemma `map_smul` / 引理 `map_smul`

English:
lemma map_smul
  given: [AddCommMonoid U] [Module R U] (f : U ->ₗ[R] V) {r : R} {x : U⟦Γ⟧}
  proof: by
  ext; simp

中文:
引理 map_smul
  条件: [加法交换幺半群 U] [模 R U] (f : U ->ₗ[R] V) {r : R} {x : U⟦Γ⟧}
  证明: by
  ext; simp
-/
protected lemma map_smul [AddCommMonoid U] [Module R U] (f : U ->ₗ[R] V) {r : R} {x : U⟦Γ⟧} :
    (r • x).map f = r • (x.map f : V⟦Γ⟧) := by
  ext; simp

section Finsupp

variable (R) in
/--
Definition of `ofFinsuppLinearMap` / `ofFinsuppLinearMap` 的定义

English:
definition ofFinsuppLinearMap
  signature: : (Γ ->₀ V) ->ₗ[R] V⟦Γ⟧ where
  body: ofFinsupp
  map_add' _ _ := by
    ext
    simp
  map_smul' _ _ := by
    ext
    simp

中文:
定义 ofFinsuppLinearMap
  签名: : (Γ ->₀ V) ->ₗ[R] V⟦Γ⟧ where
  定义体: ofFinsupp
  map_add' _ _ := by
    ext
    simp
  map_smul' _ _ := by
    ext
    simp

Depends on / 依赖: ofFinsupp
-/
def ofFinsuppLinearMap : (Γ ->₀ V) ->ₗ[R] V⟦Γ⟧ where
  toFun := ofFinsupp
  map_add' _ _ := by
    ext
    simp
  map_smul' _ _ := by
    ext
    simp

variable (R) in
@[simp]
/--
theorem `coeff_ofFinsuppLinearMap` / 定理 `coeff_ofFinsuppLinearMap`

English:
theorem coeff_ofFinsuppLinearMap
  given: (f : Γ ->₀ V) (a : Γ)
  proof: rfl

中文:
定理 coeff_ofFinsuppLinearMap
  条件: (f : Γ ->₀ V) (a : Γ)
  证明: rfl
-/
theorem coeff_ofFinsuppLinearMap (f : Γ ->₀ V) (a : Γ) :
    (ofFinsuppLinearMap R f).coeff a = f a := rfl

end Finsupp

section Domain

variable [PartialOrder Γ']

/--
theorem `embDomain_smul` / 定理 `embDomain_smul`

English:
theorem embDomain_smul
  given: (f : Γ ↪o Γ') (r : R) (x : R⟦Γ⟧)
  proof: by
  ext g
  by_cases hg : g in Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_of_notMem_range hg]

中文:
定理 embDomain_smul
  条件: (f : Γ ↪o Γ') (r : R) (x : R⟦Γ⟧)
  证明: by
  ext g
  by_cases hg : g in Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_of_notMem_range hg]

Depends on / 依赖: Set.range, embDomain_of_notMem_range
-/
theorem embDomain_smul (f : Γ ↪o Γ') (r : R) (x : R⟦Γ⟧) :
    embDomain f (r • x) = r • embDomain f x := by
  ext g
  by_cases hg : g in Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_of_notMem_range hg]

/-- Extending the domain of Hahn series is a linear map. -/
@[simps]
/--
Definition of `embDomainLinearMap` / `embDomainLinearMap` 的定义

English:
definition embDomainLinearMap
  signature: (f : Γ ↪o Γ')
  body: embDomain f
  map_add' := embDomain_add f
  map_smul' := embDomain_smul f

中文:
定义 embDomainLinearMap
  签名: (f : Γ ↪o Γ')
  定义体: embDomain f
  map_add' := embDomain_add f
  map_smul' := embDomain_smul f

Depends on / 依赖: embDomain
-/
def embDomainLinearMap (f : Γ ↪o Γ') : R⟦Γ⟧ ->ₗ[R] R⟦Γ'⟧ where
  toFun := embDomain f
  map_add' := embDomain_add f
  map_smul' := embDomain_smul f

end Domain

variable (R) in
/--
Definition of `truncLTLinearMap` / `truncLTLinearMap` 的定义

English:
definition truncLTLinearMap
  signature: [DecidableLT Γ] (c : Γ)
  body: truncLT c
  map_add' := truncLT_add c
  map_smul' := truncLT_smul c

中文:
定义 truncLTLinearMap
  签名: [DecidableLT Γ] (c : Γ)
  定义体: truncLT c
  map_add' := truncLT_add c
  map_smul' := truncLT_smul c

Depends on / 依赖: truncLT
-/
def truncLTLinearMap [DecidableLT Γ] (c : Γ) : V⟦Γ⟧ ->ₗ[R] V⟦Γ⟧ where
  toFun := truncLT c
  map_add' := truncLT_add c
  map_smul' := truncLT_smul c

variable (R) in
@[simp]
/--
theorem `coe_truncLTLinearMap` / 定理 `coe_truncLTLinearMap`

English:
theorem coe_truncLTLinearMap
  given: [DecidableLT Γ] (c : Γ)
  proof: by rfl

中文:
定理 coe_truncLTLinearMap
  条件: [DecidableLT Γ] (c : Γ)
  证明: by rfl
-/
theorem coe_truncLTLinearMap [DecidableLT Γ] (c : Γ) :
    (truncLTLinearMap R c : V⟦Γ⟧ -> V⟦Γ⟧) = truncLT c := by rfl

end Module

end HahnSeries
