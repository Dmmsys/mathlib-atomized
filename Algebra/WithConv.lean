/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.TransferInstance

/-! # Type synonym for linear map convolutive ring and intrinsic star

This files provides the type synonym `WithConv` which we will use in later files
to put the convolutive product on linear maps instance and the intrinsic star instance.
This is to ensure that we only have one multiplication, one unit, and one star.

This is given for any type `A` so that we can have `WithConv (A →ₗ[R] B)`,
`WithConv (A →L[R] B)`, `WithConv (Matrix m n R)`, etc.
-/

@[expose] public section

/--
Definition of `WithConv` / `WithConv` 的定义

English:
structure WithConv
  parameters: A
  (no additional axioms)

中文:
结构 WithConv
  参数: A
  (无附加公理)
-/
structure WithConv A where
  /-- Converts an element of `A` to `WithConv A`. -/ toConv ::
  /-- Converts an element of `WithConv A` back to `A`. -/ ofConv : A

namespace WithConv

open Lean.PrettyPrinter.Delaborator in
/-- This prevents `toConv x` being printed as `{ ofConv := x }` by `delabStructureInstance`. -/
@[app_delab toConv]
meta def delabToConv : Delab := delabApp

variable {R A B C : Type*}

/--
lemma `ofConv_toConv` / 引理 `ofConv_toConv`

English:
lemma ofConv_toConv
  given: (x : A)
  statement: ofConv (toConv x) = x
  proof: rfl

中文:
引理 ofConv_toConv
  条件: (x : A)
  结论: ofConv (toConv x) = x
  证明: rfl
-/
lemma ofConv_toConv (x : A) : ofConv (toConv x) = x := rfl
/--
lemma `toConv_ofConv` / 引理 `toConv_ofConv`

English:
lemma toConv_ofConv
  given: (x : WithConv A)
  statement: toConv (ofConv x) = x
  proof: rfl

中文:
引理 toConv_ofConv
  条件: (x : WithConv A)
  结论: toConv (ofConv x) = x
  证明: rfl
-/
@[simp] lemma toConv_ofConv (x : WithConv A) : toConv (ofConv x) = x := rfl

/--
lemma `ofConv_surjective` / 引理 `ofConv_surjective`

English:
lemma ofConv_surjective
  statement: Function.Surjective (@ofConv A)
  proof: Function.RightInverse.surjective ofConv_toConv

中文:
引理 ofConv_surjective
  结论: 函数.满射 (@ofConv A)
  证明: Function.RightInverse.surjective ofConv_toConv

Depends on / 依赖: Function, Function.RightInverse.surjective, RightInverse, ofConv_toConv, surjective
-/
lemma ofConv_surjective : Function.Surjective (@ofConv A) :=
  Function.RightInverse.surjective ofConv_toConv

/--
lemma `toConv_surjective` / 引理 `toConv_surjective`

English:
lemma toConv_surjective
  statement: Function.Surjective (@toConv A)
  proof: Function.RightInverse.surjective toConv_ofConv

中文:
引理 toConv_surjective
  结论: 函数.满射 (@toConv A)
  证明: Function.RightInverse.surjective toConv_ofConv

Depends on / 依赖: Function, Function.RightInverse.surjective, RightInverse, surjective, toConv_ofConv
-/
lemma toConv_surjective : Function.Surjective (@toConv A) :=
  Function.RightInverse.surjective toConv_ofConv

/--
lemma `ofConv_injective` / 引理 `ofConv_injective`

English:
lemma ofConv_injective
  statement: Function.Injective (@ofConv A)
  proof: Function.LeftInverse.injective toConv_ofConv

中文:
引理 ofConv_injective
  结论: 函数.单射 (@ofConv A)
  证明: Function.LeftInverse.injective toConv_ofConv

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, injective, toConv_ofConv
-/
lemma ofConv_injective : Function.Injective (@ofConv A) :=
  Function.LeftInverse.injective toConv_ofConv

/--
lemma `toConv_injective` / 引理 `toConv_injective`

English:
lemma toConv_injective
  statement: Function.Injective (@toConv A)
  proof: Function.LeftInverse.injective ofConv_toConv

中文:
引理 toConv_injective
  结论: 函数.单射 (@toConv A)
  证明: Function.LeftInverse.injective ofConv_toConv

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, injective, ofConv_toConv
-/
lemma toConv_injective : Function.Injective (@toConv A) :=
  Function.LeftInverse.injective ofConv_toConv

/--
lemma `ofConv_bijective` / 引理 `ofConv_bijective`

English:
lemma ofConv_bijective
  statement: Function.Bijective (@ofConv A)
  proof: ⟨ofConv_injective, ofConv_surjective⟩

中文:
引理 ofConv_bijective
  结论: 函数.双射 (@ofConv A)
  证明: ⟨ofConv_injective, ofConv_surjective⟩

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine.mpr, iff_of_isAffine, ofConv_injective, ofConv_surjective
-/
lemma ofConv_bijective : Function.Bijective (@ofConv A) := ⟨ofConv_injective, ofConv_surjective⟩
/--
lemma `toConv_bijective` / 引理 `toConv_bijective`

English:
lemma toConv_bijective
  statement: Function.Bijective (@toConv A)
  proof: ⟨toConv_injective, toConv_surjective⟩

中文:
引理 toConv_bijective
  结论: 函数.双射 (@toConv A)
  证明: ⟨toConv_injective, toConv_surjective⟩

Depends on / 依赖: toConv_injective, toConv_surjective
-/
lemma toConv_bijective : Function.Bijective (@toConv A) := ⟨toConv_injective, toConv_surjective⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CoeFun
  signature: A (fun _ => B -> C)] : CoeFun (WithConv A) (fun _ => B -> C) where coe f
  body: ⇑f.ofConv

中文:
实例 [CoeFun
  签名: A (fun _ => B -> C)] : CoeFun (WithConv A) (fun _ => B -> C) where coe f
  定义体: ⇑f.ofConv

Depends on / 依赖: f.ofConv, ofConv
-/
instance [CoeFun A (fun _ => B -> C)] : CoeFun (WithConv A) (fun _ => B -> C) where coe f := ⇑f.ofConv

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {x y : WithConv A}
  proof: ofConv_injective h

中文:
定理 ext
  结论: {x y : WithConv A}
  证明: ofConv_injective h
-/
@[ext] protected theorem ext {x y : WithConv A}
    (h : x.ofConv = y.ofConv) : x = y := ofConv_injective h

variable (A) in
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : WithConv A ≃ A where
  body: ofConv
  invFun := toConv
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 equiv
  签名: : WithConv A ≃ A where
  定义体: ofConv
  invFun := toConv
  left_inv _ := rfl
  right_inv _ := rfl
-/
protected def equiv : WithConv A ≃ A where
  toFun := ofConv
  invFun := toConv
  left_inv _ := rfl
  right_inv _ := rfl

/--
lemma `equiv_apply` / 引理 `equiv_apply`

English:
lemma equiv_apply
  given: (x : WithConv A)
  statement: WithConv.equiv A x = x.ofConv
  proof: rfl

中文:
引理 equiv_apply
  条件: (x : WithConv A)
  结论: WithConv.equiv A x = x.ofConv
  证明: rfl

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, pullback_fst
-/
@[simp] lemma equiv_apply (x : WithConv A) : WithConv.equiv A x = x.ofConv := rfl
/--
lemma `symm_equiv_apply` / 引理 `symm_equiv_apply`

English:
lemma symm_equiv_apply
  given: (x : A)
  statement: (WithConv.equiv A).symm x = toConv x
  proof: rfl

中文:
引理 symm_equiv_apply
  条件: (x : A)
  结论: (WithConv.equiv A).symm x = toConv x
  证明: rfl

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, pullback_snd
-/
@[simp] lemma symm_equiv_apply (x : A) : (WithConv.equiv A).symm x = toConv x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: A] : Nontrivial (WithConv A)
  body: (WithConv.equiv A).nontrivial

中文:
实例 [非平凡
  签名: A] : 非平凡 (WithConv A)
  定义体: (WithConv.equiv A).nontrivial

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, WithConv, WithConv.equiv, nontrivial, restrict
-/
instance [Nontrivial A] : Nontrivial (WithConv A) := (WithConv.equiv A).nontrivial
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: A] : Unique (WithConv A)
  body: (WithConv.equiv A).unique

中文:
实例 [唯一
  签名: A] : 唯一 (WithConv A)
  定义体: (WithConv.equiv A).unique

Depends on / 依赖: QuasiCompact, QuasiCompact.compactSpace_of_compactSpace, WithConv, WithConv.equiv, compactSpace_of_compactSpace, pullback, pullback.snd, unique
-/
instance [Unique A] : Unique (WithConv A) := (WithConv.equiv A).unique
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: A] : DecidableEq (WithConv A)
  body: (WithConv.equiv A).decidableEq

中文:
实例 [DecidableEq
  签名: A] : DecidableEq (WithConv A)
  定义体: (WithConv.equiv A).decidableEq

Depends on / 依赖: QuasiCompact, QuasiCompact.compactSpace_of_compactSpace, WithConv, WithConv.equiv, compactSpace_of_compactSpace, decidableEq, pullback, pullback.fst
-/
instance [DecidableEq A] : DecidableEq (WithConv A) := (WithConv.equiv A).decidableEq
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: A] : AddMonoid (WithConv A)
  body: (WithConv.equiv A).addMonoid

中文:
实例 [加法幺半群
  签名: A] : 加法幺半群 (WithConv A)
  定义体: (WithConv.equiv A).addMonoid

Depends on / 依赖: WithConv, WithConv.equiv, addMonoid
-/
instance [AddMonoid A] : AddMonoid (WithConv A) := (WithConv.equiv A).addMonoid
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: A] : AddCommMonoid (WithConv A)
  body: (WithConv.equiv A).addCommMonoid

中文:
实例 [加法交换幺半群
  签名: A] : 加法交换幺半群 (WithConv A)
  定义体: (WithConv.equiv A).addCommMonoid

Depends on / 依赖: WithConv, WithConv.equiv, addCommMonoid
-/
instance [AddCommMonoid A] : AddCommMonoid (WithConv A) := (WithConv.equiv A).addCommMonoid
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroup
  signature: A] : AddGroup (WithConv A)
  body: (WithConv.equiv A).addGroup

中文:
实例 [加法群
  签名: A] : 加法群 (WithConv A)
  定义体: (WithConv.equiv A).addGroup

Depends on / 依赖: WithConv, WithConv.equiv, addGroup
-/
instance [AddGroup A] : AddGroup (WithConv A) := (WithConv.equiv A).addGroup
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroup
  signature: A] : AddCommGroup (WithConv A)
  body: (WithConv.equiv A).addCommGroup

中文:
实例 [加法交换群
  签名: A] : 加法交换群 (WithConv A)
  定义体: (WithConv.equiv A).addCommGroup

Depends on / 依赖: WithConv, WithConv.equiv, addCommGroup
-/
instance [AddCommGroup A] : AddCommGroup (WithConv A) := (WithConv.equiv A).addCommGroup
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: R] [MulAction R A] : MulAction R (WithConv A)
  body: fast_instance% (WithConv.equiv A).mulAction R

中文:
实例 [幺半群
  签名: R] [乘法作用 R A] : 乘法作用 R (WithConv A)
  定义体: fast_instance% (WithConv.equiv A).mulAction R
-/
@[to_additive] instance [Monoid R] [MulAction R A] : MulAction R (WithConv A) :=
  fast_instance% (WithConv.equiv A).mulAction R
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: R] [AddCommMonoid A] [DistribMulAction R A] : DistribMulAction R (WithConv A)
  body: fast_instance% (WithConv.equiv A).distribMulAction R

中文:
实例 [幺半群
  签名: R] [加法交换幺半群 A] [分配乘法作用 R A] : 分配乘法作用 R (WithConv A)
  定义体: fast_instance% (WithConv.equiv A).distribMulAction R

Depends on / 依赖: WithConv, WithConv.equiv, distribMulAction, fast_instance
-/
instance [Monoid R] [AddCommMonoid A] [DistribMulAction R A] : DistribMulAction R (WithConv A) :=
  fast_instance% (WithConv.equiv A).distribMulAction R
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [AddCommMonoid A] [Module R A] : Module R (WithConv A)
  body: fast_instance% (WithConv.equiv A).module R

中文:
实例 [半环
  签名: R] [加法交换幺半群 A] [模 R A] : 模 R (WithConv A)
  定义体: fast_instance% (WithConv.equiv A).module R

Depends on / 依赖: WithConv, WithConv.equiv, fast_instance, module
-/
instance [Semiring R] [AddCommMonoid A] [Module R A] : Module R (WithConv A) :=
  fast_instance% (WithConv.equiv A).module R

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (f : A ≃ B)
  body: (WithConv.equiv A).trans (f.trans (WithConv.equiv B).symm)

中文:
定义 congr
  签名: (f : A ≃ B)
  定义体: (WithConv.equiv A).trans (f.trans (WithConv.equiv B).symm)
-/
protected def congr (f : A ≃ B) : WithConv A ≃ WithConv B :=
  (WithConv.equiv A).trans (f.trans (WithConv.equiv B).symm)

/--
lemma `congr_apply` / 引理 `congr_apply`

English:
lemma congr_apply
  given: (f : A ≃ B) (x : WithConv A)
  proof: rfl

中文:
引理 congr_apply
  条件: (f : A ≃ B) (x : WithConv A)
  证明: rfl
-/
@[simp] lemma congr_apply (f : A ≃ B) (x : WithConv A) :
    WithConv.congr f x = toConv (f x.ofConv) := rfl
/--
lemma `symm_congr` / 引理 `symm_congr`

English:
lemma symm_congr
  given: (f : A ≃ B)
  statement: (WithConv.congr f).symm = WithConv.congr f.symm
  proof: rfl

中文:
引理 symm_congr
  条件: (f : A ≃ B)
  结论: (WithConv.congr f).symm = WithConv.congr f.symm
  证明: rfl
-/
@[simp] lemma symm_congr (f : A ≃ B) : (WithConv.congr f).symm = WithConv.congr f.symm := rfl
/--
lemma `symm_congr_apply` / 引理 `symm_congr_apply`

English:
lemma symm_congr_apply
  given: (f : A ≃ B) (x : WithConv B)
  proof: by simp

中文:
引理 symm_congr_apply
  条件: (f : A ≃ B) (x : WithConv B)
  证明: by simp
-/
lemma symm_congr_apply (f : A ≃ B) (x : WithConv B) :
    (WithConv.congr f).symm x = toConv (f.symm x.ofConv) := by simp

section AddGroup
variable [AddGroup A]

/--
lemma `toConv_sub` / 引理 `toConv_sub`

English:
lemma toConv_sub
  given: (x y : A)
  statement: toConv (x - y) = toConv x - toConv y
  proof: rfl

中文:
引理 toConv_sub
  条件: (x y : A)
  结论: toConv (x - y) = toConv x - toConv y
  证明: rfl

Depends on / 依赖: MorphismProperty, MorphismProperty.comp_mem, comp_mem
-/
@[simp] lemma toConv_sub (x y : A) : toConv (x - y) = toConv x - toConv y := rfl
/--
lemma `ofConv_sub` / 引理 `ofConv_sub`

English:
lemma ofConv_sub
  given: (x y : WithConv A)
  statement: ofConv (x - y) = ofConv x - ofConv y
  proof: rfl

中文:
引理 ofConv_sub
  条件: (x y : WithConv A)
  结论: ofConv (x - y) = ofConv x - ofConv y
  证明: rfl

Depends on / 依赖: HasAffineProperty, HasAffineProperty.eq_targetAffineLocally, HasRingHomProperty, HasRingHomProperty.eq_affineLocally, IsFinite, LocallyQuasiFinite, QuasiFinite, RingHom, RingHom.QuasiFinite.propertyIsLocal, eq_affineLocally, eq_targetAffineLocally, of_finite, propertyIsLocal, targetAffineLocally_affineAnd_eq_affineLocally, targetAffineLocally_affineAnd_le
-/
@[simp] lemma ofConv_sub (x y : WithConv A) : ofConv (x - y) = ofConv x - ofConv y := rfl
/--
lemma `ofConv_neg` / 引理 `ofConv_neg`

English:
lemma ofConv_neg
  given: (x : WithConv A)
  statement: ofConv (-x) = -ofConv x
  proof: rfl

中文:
引理 ofConv_neg
  条件: (x : WithConv A)
  结论: ofConv (-x) = -ofConv x
  证明: rfl

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.of_isOpenImmersion, IsImmersion, LocallyQuasiFinite, QuasiFinite, RingHom, RingHom.QuasiFinite.holdsForLocalizationAway.containsIdentities, coborderRange, containsIdentities, f.coborderRange, f.liftCoborder_, holdsForLocalizationAway, infer_instance, of_isOpenImmersion
-/
@[simp] lemma ofConv_neg (x : WithConv A) : ofConv (-x) = -ofConv x := rfl
/--
lemma `toConv_neg` / 引理 `toConv_neg`

English:
lemma toConv_neg
  given: (x : A)
  statement: toConv (-x) = -toConv x
  proof: rfl

中文:
引理 toConv_neg
  条件: (x : A)
  结论: toConv (-x) = -toConv x
  证明: rfl
-/
@[simp] lemma toConv_neg (x : A) : toConv (-x) = -toConv x := rfl

end AddGroup

/--
lemma `ofConv_smul` / 引理 `ofConv_smul`

English:
lemma ofConv_smul
  given: [Monoid R] [MulAction R A] (c : R) (x : WithConv A)
  proof: rfl

中文:
引理 ofConv_smul
  条件: [幺半群 R] [乘法作用 R A] (c : R) (x : WithConv A)
  证明: rfl
-/
@[simp] lemma ofConv_smul [Monoid R] [MulAction R A] (c : R) (x : WithConv A) :
    ofConv (c • x) = c • ofConv x := rfl
/--
lemma `toConv_smul` / 引理 `toConv_smul`

English:
lemma toConv_smul
  given: [Monoid R] [MulAction R A] (c : R) (x : A)
  proof: rfl

中文:
引理 toConv_smul
  条件: [幺半群 R] [乘法作用 R A] (c : R) (x : A)
  证明: rfl
-/
@[simp] lemma toConv_smul [Monoid R] [MulAction R A] (c : R) (x : A) :
    toConv (c • x) = c • toConv x := rfl

section
variable [AddMonoid A]

/--
lemma `ofConv_zero` / 引理 `ofConv_zero`

English:
lemma ofConv_zero
  statement: ofConv (0 : WithConv A) = 0
  proof: rfl

中文:
引理 ofConv_zero
  结论: ofConv (0 : WithConv A) = 0
  证明: rfl
-/
@[simp] lemma ofConv_zero : ofConv (0 : WithConv A) = 0 := rfl
/--
lemma `toConv_zero` / 引理 `toConv_zero`

English:
lemma toConv_zero
  statement: toConv (0 : A) = 0
  proof: rfl

中文:
引理 toConv_zero
  结论: toConv (0 : A) = 0
  证明: rfl

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, pullback_fst
-/
@[simp] lemma toConv_zero : toConv (0 : A) = 0 := rfl
/--
lemma `ofConv_add` / 引理 `ofConv_add`

English:
lemma ofConv_add
  given: (x y : WithConv A)
  statement: ofConv (x + y) = ofConv x + ofConv y
  proof: rfl

中文:
引理 ofConv_add
  条件: (x y : WithConv A)
  结论: ofConv (x + y) = ofConv x + ofConv y
  证明: rfl

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, pullback_snd
-/
@[simp] lemma ofConv_add (x y : WithConv A) : ofConv (x + y) = ofConv x + ofConv y := rfl
/--
lemma `toConv_add` / 引理 `toConv_add`

English:
lemma toConv_add
  given: (x y : A)
  statement: toConv (x + y) = toConv x + toConv y
  proof: rfl

中文:
引理 toConv_add
  条件: (x y : A)
  结论: toConv (x + y) = toConv x + toConv y
  证明: rfl

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, restrict
-/
@[simp] lemma toConv_add (x y : A) : toConv (x + y) = toConv x + toConv y := rfl
/--
lemma `ofConv_eq_zero` / 引理 `ofConv_eq_zero`

English:
lemma ofConv_eq_zero
  given: {x : WithConv A}
  statement: ofConv x = 0 ↔ x = 0
  proof: ofConv_injective.eq_iff

中文:
引理 ofConv_eq_zero
  条件: {x : WithConv A}
  结论: ofConv x = 0 ↔ x = 0
  证明: ofConv_injective.eq_iff

Depends on / 依赖: Scheme, Scheme.Hom.resLE, infer_instance
-/
@[simp] lemma ofConv_eq_zero {x : WithConv A} : ofConv x = 0 ↔ x = 0 := ofConv_injective.eq_iff
/--
lemma `toConv_eq_zero` / 引理 `toConv_eq_zero`

English:
lemma toConv_eq_zero
  given: {x : A}
  statement: toConv x = 0 ↔ x = 0
  proof: toConv_injective.eq_iff

中文:
引理 toConv_eq_zero
  条件: {x : A}
  结论: toConv x = 0 ↔ x = 0
  证明: toConv_injective.eq_iff
-/
@[simp] lemma toConv_eq_zero {x : A} : toConv x = 0 ↔ x = 0 := toConv_injective.eq_iff

variable (A) in
/--
Definition of `addEquiv` / `addEquiv` 的定义

English:
definition addEquiv
  signature: : WithConv A ≃+ A where
  body: WithConv.equiv A
  map_add' := by simp

中文:
定义 addEquiv
  签名: : WithConv A ≃+ A where
  定义体: WithConv.equiv A
  map_add' := by simp
-/
@[simps!] protected def addEquiv : WithConv A ≃+ A where
  __ := WithConv.equiv A
  map_add' := by simp

/--
theorem `toEquiv_addEquiv` / 定理 `toEquiv_addEquiv`

English:
theorem toEquiv_addEquiv
  statement: (WithConv.addEquiv A : WithConv A ≃ A) = WithConv.equiv A
  proof: rfl

中文:
定理 toEquiv_addEquiv
  结论: (WithConv.addEquiv A : WithConv A ≃ A) = WithConv.equiv A
  证明: rfl
-/
@[simp] theorem toEquiv_addEquiv : (WithConv.addEquiv A : WithConv A ≃ A) = WithConv.equiv A := rfl

end

variable [AddCommMonoid A]

variable (R A) in
/--
Definition of `linearEquiv` / `linearEquiv` 的定义

English:
definition linearEquiv
  signature: [Semiring R] [Module R A]
  body: WithConv.addEquiv A
  map_smul' := by simp

中文:
定义 linearEquiv
  签名: [半环 R] [模 R A]
  定义体: WithConv.addEquiv A
  map_smul' := by simp
-/
protected def linearEquiv [Semiring R] [Module R A] : WithConv A ≃ₗ[R] A where
  __ := WithConv.addEquiv A
  map_smul' := by simp

/--
lemma `linearEquiv_apply` / 引理 `linearEquiv_apply`

English:
lemma linearEquiv_apply
  statement: [Semiring R] [Module R A]
  proof: rfl

中文:
引理 linearEquiv_apply
  结论: [半环 R] [模 R A]
  证明: rfl
-/
@[simp] lemma linearEquiv_apply [Semiring R] [Module R A]
    (a : WithConv A) : WithConv.linearEquiv R A a = ofConv a := rfl
/--
lemma `symm_linearEquiv_apply` / 引理 `symm_linearEquiv_apply`

English:
lemma symm_linearEquiv_apply
  statement: [Semiring R] [Module R A]
  proof: rfl

中文:
引理 symm_linearEquiv_apply
  结论: [半环 R] [模 R A]
  证明: rfl
-/
@[simp] lemma symm_linearEquiv_apply [Semiring R] [Module R A]
    (a : A) : (WithConv.linearEquiv R A).symm a = toConv a := rfl
/--
lemma `toAddEquiv_linearEquiv` / 引理 `toAddEquiv_linearEquiv`

English:
lemma toAddEquiv_linearEquiv
  given: [Semiring R] [Module R A]
  proof: rfl

中文:
引理 toAddEquiv_linearEquiv
  条件: [半环 R] [模 R A]
  证明: rfl
-/
@[simp] lemma toAddEquiv_linearEquiv [Semiring R] [Module R A] :
    (WithConv.linearEquiv R A).toAddEquiv = WithConv.addEquiv A := rfl

/--
lemma `ofConv_sum` / 引理 `ofConv_sum`

English:
lemma ofConv_sum
  given: {ι : Type*} (s : Finset ι) (f : ι -> WithConv A)
  proof: map_sum (WithConv.addEquiv _) _ _

中文:
引理 ofConv_sum
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> WithConv A)
  证明: map_sum (WithConv.addEquiv _) _ _

Depends on / 依赖: of_locallyQuasiFinite, pullback, pullback.snd
-/
@[simp] lemma ofConv_sum {ι : Type*} (s : Finset ι) (f : ι -> WithConv A) :
    (∑ i in s, f i).ofConv = ∑ i in s, (f i).ofConv := map_sum (WithConv.addEquiv _) _ _
/--
lemma `toConv_sum` / 引理 `toConv_sum`

English:
lemma toConv_sum
  given: {ι : Type*} (s : Finset ι) (f : ι -> A)
  proof: map_sum (WithConv.addEquiv _).symm _ _

中文:
引理 toConv_sum
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> A)
  证明: map_sum (WithConv.addEquiv _).symm _ _
-/
@[simp] lemma toConv_sum {ι : Type*} (s : Finset ι) (f : ι -> A) :
    toConv (∑ i in s, f i) = ∑ i in s, toConv (f i) := map_sum (WithConv.addEquiv _).symm _ _
/--
lemma `ofConv_listSum` / 引理 `ofConv_listSum`

English:
lemma ofConv_listSum
  given: (l : List (WithConv A))
  proof: map_list_sum (WithConv.addEquiv _) _

中文:
引理 ofConv_listSum
  条件: (l : 列表 (WithConv A))
  证明: map_list_sum (WithConv.addEquiv _) _

Depends on / 依赖: IsClosedImmersion, IsPreimmersion, LocallyQuasiFinite, f.fiberToSpecResidueField, fiberToSpecResidueField, infer_instance, isClosed_discrete, of_fiberToSpecResidueField, of_isPreimmersion, pullback, pullback.snd
-/
@[simp] lemma ofConv_listSum (l : List (WithConv A)) :
    l.sum.ofConv = (l.map ofConv).sum := map_list_sum (WithConv.addEquiv _) _
/--
lemma `toConv_listSum` / 引理 `toConv_listSum`

English:
lemma toConv_listSum
  given: (l : List A)
  proof: map_list_sum (WithConv.addEquiv _).symm _

中文:
引理 toConv_listSum
  条件: (l : 列表 A)
  证明: map_list_sum (WithConv.addEquiv _).symm _
-/
@[simp] lemma toConv_listSum (l : List A) :
    toConv l.sum = (l.map toConv).sum := map_list_sum (WithConv.addEquiv _).symm _
/--
lemma `ofConv_multisetSum` / 引理 `ofConv_multisetSum`

English:
lemma ofConv_multisetSum
  given: (s : Multiset (WithConv A))
  proof: map_multiset_sum (WithConv.addEquiv _) _

中文:
引理 ofConv_multisetSum
  条件: (s : Multiset (WithConv A))
  证明: map_multiset_sum (WithConv.addEquiv _) _
-/
@[simp] lemma ofConv_multisetSum (s : Multiset (WithConv A)) :
    s.sum.ofConv = (s.map ofConv).sum := map_multiset_sum (WithConv.addEquiv _) _
/--
lemma `toConv_multisetSum` / 引理 `toConv_multisetSum`

English:
lemma toConv_multisetSum
  given: (s : Multiset A)
  proof: map_multiset_sum (WithConv.addEquiv _).symm _

中文:
引理 toConv_multisetSum
  条件: (s : Multiset A)
  证明: map_multiset_sum (WithConv.addEquiv _).symm _

Depends on / 依赖: LocallyOfFiniteType
-/
@[simp] lemma toConv_multisetSum (s : Multiset A) :
    toConv s.sum = (s.map toConv).sum := map_multiset_sum (WithConv.addEquiv _).symm _

section
variable [Semiring R] [Module R A] [AddCommMonoid B] [Module R B]

/--
Definition of `congrLinearEquiv` / `congrLinearEquiv` 的定义

English:
definition congrLinearEquiv
  signature: (f : A ≃ₗ[R] B)
  body: (WithConv.linearEquiv R A).trans (f.trans (WithConv.linearEquiv R B).symm)

中文:
定义 congrLinearEquiv
  签名: (f : A ≃ₗ[R] B)
  定义体: (WithConv.linearEquiv R A).trans (f.trans (WithConv.linearEquiv R B).symm)

Depends on / 依赖: WithConv, WithConv.linearEquiv, f.trans, linearEquiv
-/
def congrLinearEquiv (f : A ≃ₗ[R] B) : WithConv A ≃ₗ[R] WithConv B :=
  (WithConv.linearEquiv R A).trans (f.trans (WithConv.linearEquiv R B).symm)

/--
lemma `congrLinearEquiv_apply` / 引理 `congrLinearEquiv_apply`

English:
lemma congrLinearEquiv_apply
  given: (f : A ≃ₗ[R] B) (x : WithConv A)
  proof: rfl

中文:
引理 congrLinearEquiv_apply
  条件: (f : A ≃ₗ[R] B) (x : WithConv A)
  证明: rfl
-/
@[simp] lemma congrLinearEquiv_apply (f : A ≃ₗ[R] B) (x : WithConv A) :
    congrLinearEquiv f x = toConv (f x.ofConv) := rfl
/--
lemma `symm_congrLinearEquiv` / 引理 `symm_congrLinearEquiv`

English:
lemma symm_congrLinearEquiv
  given: (f : A ≃ₗ[R] B)
  proof: rfl

中文:
引理 symm_congrLinearEquiv
  条件: (f : A ≃ₗ[R] B)
  证明: rfl
-/
@[simp] lemma symm_congrLinearEquiv (f : A ≃ₗ[R] B) :
    (congrLinearEquiv f).symm = congrLinearEquiv f.symm := rfl
/--
lemma `symm_congrLinearEquiv_apply` / 引理 `symm_congrLinearEquiv_apply`

English:
lemma symm_congrLinearEquiv_apply
  given: (f : A ≃ₗ[R] B) (x : WithConv B)
  proof: by simp

中文:
引理 symm_congrLinearEquiv_apply
  条件: (f : A ≃ₗ[R] B) (x : WithConv B)
  证明: by simp

Depends on / 依赖: WithConv, WithConv.congr, congrLinearEquiv, f.toEquiv, theorem, toEquiv, toEquiv_congrLinearEquiv
-/
lemma symm_congrLinearEquiv_apply (f : A ≃ₗ[R] B) (x : WithConv B) :
    (congrLinearEquiv f).symm x = toConv (f.symm x.ofConv) := by simp
/--
theorem `toEquiv_congrLinearEquiv` / 定理 `toEquiv_congrLinearEquiv`

English:
theorem toEquiv_congrLinearEquiv
  given: (f : A ≃ₗ[R] B)
  proof: rfl

中文:
定理 toEquiv_congrLinearEquiv
  条件: (f : A ≃ₗ[R] B)
  证明: rfl
-/
@[simp] theorem toEquiv_congrLinearEquiv (f : A ≃ₗ[R] B) :
    (congrLinearEquiv f).toEquiv = WithConv.congr f.toEquiv := rfl

end

end WithConv
