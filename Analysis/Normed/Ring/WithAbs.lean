/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Analysis.Normed.Ring.TransferInstance
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# `WithAbs` type synonym

`WithAbs v` is a copy of the semiring `R` with the same underlying ring structure, but assigned
`v`-dependent instances (such as `NormedRing`) where `v` is an absolute value on `R`.

## Main definitions
- `WithAbs` : type synonym for a semiring which depends on an absolute value. This is
  a function that takes an absolute value on a semiring and returns the semiring. This can be used
  to assign and infer instances on a semiring that depend on absolute values.
- `WithAbs.equiv v` : The canonical ring equivalence between `WithAbs v` and `R`.
-/

@[expose] public section

open Topology

variable {R : Type*} {S : Type*} [Semiring S] [PartialOrder S]

/--
Definition of `WithAbs` / `WithAbs` 的定义

English:
structure WithAbs
  parameters: [Semiring R] (v : AbsoluteValue R S)
  axioms and operations (2):
    - toAbs((v)) : :
    - ofAbs : R

中文:
结构 WithAbs
  参数: [Semiring R] (v : AbsoluteValue R S)
  公理与运算 (2 个):
    - toAbs((v)) : :
    - ofAbs : R
-/
structure WithAbs [Semiring R] (v : AbsoluteValue R S) where
  /-- Converts an element of `R` to an element of `WithAbs v`. -/
  toAbs (v) ::
  /-- Converts an element of `WithAbs v` to an element of `R`. -/
  ofAbs : R

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `toAbs p x` being printed as `{ ofAbs := x }` by `delabStructureInstance`. -/
@[app_delab WithAbs.toAbs]
meta def WithAbs.delabToAbs : Delab := delabApp

end Notation

namespace WithAbs

section Semiring

variable [Semiring R] (v : AbsoluteValue R S)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semiring (WithAbs v)
  body: fast_instance% Equiv.semiring { toFun := ofAbs, invFun := toAbs v }

中文:
实例 :
  签名: Semiring (WithAbs v)
  定义体: fast_instance% Equiv.semiring { toFun := ofAbs, invFun := toAbs v }

Depends on / 依赖: Equiv.semiring, fast_instance, invFun, semiring
-/
instance : Semiring (WithAbs v) :=
  fast_instance% Equiv.semiring { toFun := ofAbs, invFun := toAbs v }

/--
lemma `ofAbs_toAbs` / 引理 `ofAbs_toAbs`

English:
lemma ofAbs_toAbs
  given: (x : R)
  statement: ofAbs (toAbs v x) = x
  proof: rfl

中文:
引理 ofAbs_toAbs
  条件: (x : R)
  结论: ofAbs (toAbs v x) = x
  证明: rfl
-/
lemma ofAbs_toAbs (x : R) : ofAbs (toAbs v x) = x := rfl
/--
lemma `toAbs_ofAbs` / 引理 `toAbs_ofAbs`

English:
lemma toAbs_ofAbs
  given: (x : WithAbs v)
  statement: toAbs v (ofAbs x) = x
  proof: rfl

中文:
引理 toAbs_ofAbs
  条件: (x : WithAbs v)
  结论: toAbs v (ofAbs x) = x
  证明: rfl
-/
@[simp] lemma toAbs_ofAbs (x : WithAbs v) : toAbs v (ofAbs x) = x := rfl

/--
lemma `ofAbs_surjective` / 引理 `ofAbs_surjective`

English:
lemma ofAbs_surjective
  statement: Function.Surjective (ofAbs (v := v))
  proof: Function.RightInverse.surjective ofAbs_toAbs _

中文:
引理 ofAbs_surjective
  结论: Function.Surjective (ofAbs (v := v))
  证明: Function.RightInverse.surjective ofAbs_toAbs _
-/
lemma ofAbs_surjective : Function.Surjective (ofAbs (v := v)) :=
Function.RightInverse.surjective ofAbs_toAbs _

/--
lemma `toAbs_surjective` / 引理 `toAbs_surjective`

English:
lemma toAbs_surjective
  statement: Function.Surjective (toAbs v)
  proof: Function.RightInverse.surjective toAbs_ofAbs _

中文:
引理 toAbs_surjective
  结论: Function.Surjective (toAbs v)
  证明: Function.RightInverse.surjective toAbs_ofAbs _

Depends on / 依赖: Function, Function.RightInverse.surjective, RightInverse, surjective, toAbs_ofAbs
-/
lemma toAbs_surjective : Function.Surjective (toAbs v) :=
Function.RightInverse.surjective toAbs_ofAbs _

/--
lemma `ofAbs_injective` / 引理 `ofAbs_injective`

English:
lemma ofAbs_injective
  statement: Function.Injective (ofAbs (v := v))
  proof: Function.LeftInverse.injective toAbs_ofAbs _

中文:
引理 ofAbs_injective
  结论: Function.Injective (ofAbs (v := v))
  证明: Function.LeftInverse.injective toAbs_ofAbs _
-/
lemma ofAbs_injective : Function.Injective (ofAbs (v := v)) :=
Function.LeftInverse.injective toAbs_ofAbs _

/--
lemma `toAbs_injective` / 引理 `toAbs_injective`

English:
lemma toAbs_injective
  statement: Function.Injective (toAbs v)
  proof: Function.LeftInverse.injective ofAbs_toAbs _

中文:
引理 toAbs_injective
  结论: Function.Injective (toAbs v)
  证明: Function.LeftInverse.injective ofAbs_toAbs _

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, injective, ofAbs_toAbs
-/
lemma toAbs_injective : Function.Injective (toAbs v) :=
Function.LeftInverse.injective ofAbs_toAbs _

/--
lemma `ofAbs_bijective` / 引理 `ofAbs_bijective`

English:
lemma ofAbs_bijective
  statement: Function.Bijective (ofAbs (v := v))
  proof: ⟨ofAbs_injective v, ofAbs_surjective v⟩

中文:
引理 ofAbs_bijective
  结论: Function.Bijective (ofAbs (v := v))
  证明: ⟨ofAbs_injective v, ofAbs_surjective v⟩
-/
lemma ofAbs_bijective : Function.Bijective (ofAbs (v := v)) :=
  ⟨ofAbs_injective v, ofAbs_surjective v⟩

/--
lemma `toAbs_bijective` / 引理 `toAbs_bijective`

English:
lemma toAbs_bijective
  statement: Function.Bijective (toAbs v)
  proof: ⟨toAbs_injective v, toAbs_surjective v⟩

中文:
引理 toAbs_bijective
  结论: Function.Bijective (toAbs v)
  证明: ⟨toAbs_injective v, toAbs_surjective v⟩

Depends on / 依赖: toAbs_injective, toAbs_surjective
-/
lemma toAbs_bijective : Function.Bijective (toAbs v) :=
  ⟨toAbs_injective v, toAbs_surjective v⟩

/--
lemma `toAbs_zero` / 引理 `toAbs_zero`

English:
lemma toAbs_zero
  statement: toAbs v (0 : R) = 0
  proof: rfl

中文:
引理 toAbs_zero
  结论: toAbs v (0 : R) = 0
  证明: rfl
-/
@[simp] lemma toAbs_zero : toAbs v (0 : R) = 0 := rfl
/--
lemma `ofAbs_zero` / 引理 `ofAbs_zero`

English:
lemma ofAbs_zero
  statement: ofAbs (0 : WithAbs v) = 0
  proof: rfl

中文:
引理 ofAbs_zero
  结论: ofAbs (0 : WithAbs v) = 0
  证明: rfl
-/
@[simp] lemma ofAbs_zero : ofAbs (0 : WithAbs v) = 0 := rfl

/--
lemma `toAbs_one` / 引理 `toAbs_one`

English:
lemma toAbs_one
  statement: toAbs v (1 : R) = 1
  proof: rfl

中文:
引理 toAbs_one
  结论: toAbs v (1 : R) = 1
  证明: rfl
-/
@[simp] lemma toAbs_one : toAbs v (1 : R) = 1 := rfl
/--
lemma `ofAbs_one` / 引理 `ofAbs_one`

English:
lemma ofAbs_one
  statement: ofAbs (1 : WithAbs v) = 1
  proof: rfl

中文:
引理 ofAbs_one
  结论: ofAbs (1 : WithAbs v) = 1
  证明: rfl
-/
@[simp] lemma ofAbs_one : ofAbs (1 : WithAbs v) = 1 := rfl

/--
lemma `toAbs_add` / 引理 `toAbs_add`

English:
lemma toAbs_add
  given: (x y : R)
  statement: toAbs v (x + y) = toAbs v x + toAbs v y
  proof: rfl

中文:
引理 toAbs_add
  条件: (x y : R)
  结论: toAbs v (x + y) = toAbs v x + toAbs v y
  证明: rfl
-/
@[simp] lemma toAbs_add (x y : R) : toAbs v (x + y) = toAbs v x + toAbs v y := rfl
/--
lemma `ofAbs_add` / 引理 `ofAbs_add`

English:
lemma ofAbs_add
  given: (x y : WithAbs v)
  statement: ofAbs (x + y) = ofAbs x + ofAbs y
  proof: rfl

中文:
引理 ofAbs_add
  条件: (x y : WithAbs v)
  结论: ofAbs (x + y) = ofAbs x + ofAbs y
  证明: rfl
-/
@[simp] lemma ofAbs_add (x y : WithAbs v) : ofAbs (x + y) = ofAbs x + ofAbs y := rfl

/--
lemma `toAbs_mul` / 引理 `toAbs_mul`

English:
lemma toAbs_mul
  given: (x y : R)
  statement: toAbs v (x * y) = toAbs v x * toAbs v y
  proof: rfl

中文:
引理 toAbs_mul
  条件: (x y : R)
  结论: toAbs v (x * y) = toAbs v x * toAbs v y
  证明: rfl
-/
@[simp] lemma toAbs_mul (x y : R) : toAbs v (x * y) = toAbs v x * toAbs v y := rfl
/--
lemma `ofAbs_mul` / 引理 `ofAbs_mul`

English:
lemma ofAbs_mul
  given: (x y : WithAbs v)
  statement: ofAbs (x * y) = ofAbs x * ofAbs y
  proof: rfl

中文:
引理 ofAbs_mul
  条件: (x y : WithAbs v)
  结论: ofAbs (x * y) = ofAbs x * ofAbs y
  证明: rfl
-/
@[simp] lemma ofAbs_mul (x y : WithAbs v) : ofAbs (x * y) = ofAbs x * ofAbs y := rfl

/--
lemma `toAbs_eq_zero` / 引理 `toAbs_eq_zero`

English:
lemma toAbs_eq_zero
  given: {x : R}
  statement: toAbs v x = 0 ↔ x = 0
  proof: (toAbs_injective v).eq_iff

中文:
引理 toAbs_eq_zero
  条件: {x : R}
  结论: toAbs v x = 0 ↔ x = 0
  证明: (toAbs_injective v).eq_iff
-/
@[simp] lemma toAbs_eq_zero {x : R} : toAbs v x = 0 ↔ x = 0 := (toAbs_injective v).eq_iff
/--
lemma `ofAbs_eq_zero` / 引理 `ofAbs_eq_zero`

English:
lemma ofAbs_eq_zero
  given: {x : WithAbs v}
  statement: ofAbs x = 0 ↔ x = 0
  proof: (ofAbs_injective v).eq_iff

中文:
引理 ofAbs_eq_zero
  条件: {x : WithAbs v}
  结论: ofAbs x = 0 ↔ x = 0
  证明: (ofAbs_injective v).eq_iff
-/
@[simp] lemma ofAbs_eq_zero {x : WithAbs v} : ofAbs x = 0 ↔ x = 0 := (ofAbs_injective v).eq_iff

/--
lemma `toAbs_pow` / 引理 `toAbs_pow`

English:
lemma toAbs_pow
  given: (x : R) (n : Nat)
  statement: toAbs v (x ^ n) = toAbs v x ^ n
  proof: rfl

中文:
引理 toAbs_pow
  条件: (x : R) (n : 自然数)
  结论: toAbs v (x ^ n) = toAbs v x ^ n
  证明: rfl
-/
@[simp] lemma toAbs_pow (x : R) (n : Nat) : toAbs v (x ^ n) = toAbs v x ^ n := rfl
/--
lemma `ofAbs_pow` / 引理 `ofAbs_pow`

English:
lemma ofAbs_pow
  given: (x : WithAbs v) (n : Nat)
  statement: ofAbs (x ^ n) = ofAbs x ^ n
  proof: rfl

中文:
引理 ofAbs_pow
  条件: (x : WithAbs v) (n : 自然数)
  结论: ofAbs (x ^ n) = ofAbs x ^ n
  证明: rfl
-/
@[simp] lemma ofAbs_pow (x : WithAbs v) (n : Nat) : ofAbs (x ^ n) = ofAbs x ^ n := rfl

/-- The canonical (semiring) equivalence between `WithAbs v` and `R`. -/
@[simps apply symm_apply]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : WithAbs v ≃+* R where
  body: ofAbs
  invFun := toAbs v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

中文:
定义 equiv
  签名: : WithAbs v ≃+* R where
  定义体: ofAbs
  invFun := toAbs v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
-/
def equiv : WithAbs v ≃+* R where
  toFun := ofAbs
  invFun := toAbs v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nontrivial (WithAbs v)
  body: (equiv v).nontrivial

中文:
实例 [Nontrivial
  签名: R] : Nontrivial (WithAbs v)
  定义体: (equiv v).nontrivial

Depends on / 依赖: nontrivial
-/
instance [Nontrivial R] : Nontrivial (WithAbs v) := (equiv v).nontrivial
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: R] : Unique (WithAbs v)
  body: (equiv v).unique

中文:
实例 [Unique
  签名: R] : Unique (WithAbs v)
  定义体: (equiv v).unique

Depends on / 依赖: unique
-/
instance [Unique R] : Unique (WithAbs v) := (equiv v).unique
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (WithAbs v)
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited (WithAbs v)
  定义体: ⟨0⟩
-/
instance : Inhabited (WithAbs v) := ⟨0⟩

variable {T U : Type*} [Semiring T] [Semiring U] (w : AbsoluteValue T S) (u : AbsoluteValue U S)
  (f : R ->+* T) (g : T ->+* U)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : WithAbs v ->+* WithAbs w
  body: (equiv w).symm.toRingHom.comp (f.comp (equiv v).toRingHom)

中文:
定义 map
  签名: : WithAbs v ->+* WithAbs w
  定义体: (equiv w).symm.toRingHom.comp (f.comp (equiv v).toRingHom)

Depends on / 依赖: f.comp, symm.toRingHom.comp, toRingHom
-/
def map : WithAbs v ->+* WithAbs w := (equiv w).symm.toRingHom.comp (f.comp (equiv v).toRingHom)

/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: WithAbs.map v v (RingHom.id R) = RingHom.id (WithAbs v)
  proof: rfl

中文:
定理 map_id
  结论: WithAbs.map v v (RingHom.id R) = RingHom.id (WithAbs v)
  证明: rfl
-/
@[simp] theorem map_id : WithAbs.map v v (RingHom.id R) = RingHom.id (WithAbs v) := rfl
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: map v u (g.comp f) = (map w u g).comp (map v w f)
  proof: rfl

中文:
定理 map_comp
  结论: map v u (g.comp f) = (map w u g).comp (map v w f)
  证明: rfl
-/
theorem map_comp : map v u (g.comp f) = (map w u g).comp (map v w f) := rfl
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: (x : WithAbs v)
  statement: map v w f x = toAbs w (f x.ofAbs)
  proof: rfl

中文:
定理 map_apply
  条件: (x : WithAbs v)
  结论: map v w f x = toAbs w (f x.ofAbs)
  证明: rfl
-/
@[simp] theorem map_apply (x : WithAbs v) : map v w f x = toAbs w (f x.ofAbs) := rfl

variable (f : R ≃+* T) (g : T ≃+* U)

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: : WithAbs v ≃+* WithAbs w where
  body: map v w f.toRingHom
  invFun := map w v f.symm.toRingHom
  left_inv x := by simp
  right_inv x := by simp

@[simp]

中文:
定义 congr
  签名: : WithAbs v ≃+* WithAbs w where
  定义体: map v w f.toRingHom
  invFun := map w v f.symm.toRingHom
  left_inv x := by simp
  right_inv x := by simp

@[simp]

Depends on / 依赖: f.toRingHom, toRingHom
-/
def congr : WithAbs v ≃+* WithAbs w where
  __ := map v w f.toRingHom
  invFun := map w v f.symm.toRingHom
  left_inv x := by simp
  right_inv x := by simp

@[simp]
/--
theorem `congr_refl` / 定理 `congr_refl`

English:
theorem congr_refl
  statement: congr v v (RingEquiv.refl R) = RingEquiv.refl (WithAbs v)
  proof: rfl

中文:
定理 congr_refl
  结论: congr v v (RingEquiv.refl R) = RingEquiv.refl (WithAbs v)
  证明: rfl
-/
theorem congr_refl : congr v v (RingEquiv.refl R) = RingEquiv.refl (WithAbs v) := rfl
/--
theorem `congr_trans` / 定理 `congr_trans`

English:
theorem congr_trans
  statement: congr v u (f.trans g) = (congr v w f).trans (congr w u g)
  proof: rfl

中文:
定理 congr_trans
  结论: congr v u (f.trans g) = (congr v w f).trans (congr w u g)
  证明: rfl
-/
theorem congr_trans : congr v u (f.trans g) = (congr v w f).trans (congr w u g) := rfl
/--
theorem `congr_symm` / 定理 `congr_symm`

English:
theorem congr_symm
  statement: (congr v w f).symm = congr w v f.symm
  proof: rfl

中文:
定理 congr_symm
  结论: (congr v w f).symm = congr w v f.symm
  证明: rfl
-/
theorem congr_symm : (congr v w f).symm = congr w v f.symm := rfl
/--
theorem `congr_apply` / 定理 `congr_apply`

English:
theorem congr_apply
  given: (x : WithAbs v)
  statement: congr v w f x = toAbs w (f x.ofAbs)
  proof: rfl

中文:
定理 congr_apply
  条件: (x : WithAbs v)
  结论: congr v w f x = toAbs w (f x.ofAbs)
  证明: rfl
-/
@[simp] theorem congr_apply (x : WithAbs v) : congr v w f x = toAbs w (f x.ofAbs) := rfl
/--
theorem `congr_symm_apply` / 定理 `congr_symm_apply`

English:
theorem congr_symm_apply
  given: (x : WithAbs w)
  proof: rfl

中文:
定理 congr_symm_apply
  条件: (x : WithAbs w)
  证明: rfl
-/
@[simp] theorem congr_symm_apply (x : WithAbs w) :
    (congr v w f).symm x = toAbs v (f.symm x.ofAbs) := rfl

/-- The canonical (semiring) equivalence between `WithAbs v` and `WithAbs w`, for any two
absolute values `v` and `w` on `R`. -/
@[deprecated "Use `WithAbs.congr` instead." (since := "2026-03-02")]
/--
Definition of `equivWithAbs` / `equivWithAbs` 的定义

English:
definition equivWithAbs
  signature: (v w : AbsoluteValue R S)
  body: congr v w (.refl R)

@[deprecated "Use `WithAbs.congr_symm` instead." (since := "2026-03-02")]

中文:
定义 equivWithAbs
  签名: (v w : AbsoluteValue R S)
  定义体: congr v w (.refl R)

@[deprecated "Use `WithAbs.congr_symm` instead." (since := "2026-03-02")]
-/
def equivWithAbs (v w : AbsoluteValue R S) : WithAbs v ≃+* WithAbs w :=
    congr v w (.refl R)

@[deprecated "Use `WithAbs.congr_symm` instead." (since := "2026-03-02")]
/--
theorem `equivWithAbs_symm` / 定理 `equivWithAbs_symm`

English:
theorem equivWithAbs_symm
  given: (v w : AbsoluteValue R S)
  proof: congr_symm _ _ _

@[deprecated "Use `simp`." (since := "2026-03-02")]

中文:
定理 equivWithAbs_symm
  条件: (v w : AbsoluteValue R S)
  证明: congr_symm _ _ _

@[deprecated "Use `simp`." (since := "2026-03-02")]

Depends on / 依赖: congr_symm
-/
theorem equivWithAbs_symm (v w : AbsoluteValue R S) :
    (congr v w (.refl R)).symm = (congr w v (RingEquiv.refl R).symm) :=
  congr_symm _ _ _

@[deprecated "Use `simp`." (since := "2026-03-02")]
/--
theorem `equiv_equivWithAbs_symm_apply` / 定理 `equiv_equivWithAbs_symm_apply`

English:
theorem equiv_equivWithAbs_symm_apply
  given: {v w : AbsoluteValue R S} {x : WithAbs w}
  proof: by simp

@[deprecated "Use `simp`." (since := "2026-03-02")]

中文:
定理 equiv_equivWithAbs_symm_apply
  条件: {v w : AbsoluteValue R S} {x : WithAbs w}
  证明: by simp

@[deprecated "Use `simp`." (since := "2026-03-02")]
-/
theorem equiv_equivWithAbs_symm_apply {v w : AbsoluteValue R S} {x : WithAbs w} :
    equiv v ((congr v w (.refl R)).symm x) = equiv w x := by simp

@[deprecated "Use `simp`." (since := "2026-03-02")]
/--
theorem `equivWithAbs_equiv_symm_apply` / 定理 `equivWithAbs_equiv_symm_apply`

English:
theorem equivWithAbs_equiv_symm_apply
  given: {v w : AbsoluteValue R S} {x : R}
  proof: by simp

@[deprecated "Use `simp`." (since := "2026-03-02")]

中文:
定理 equivWithAbs_equiv_symm_apply
  条件: {v w : AbsoluteValue R S} {x : R}
  证明: by simp

@[deprecated "Use `simp`." (since := "2026-03-02")]
-/
theorem equivWithAbs_equiv_symm_apply {v w : AbsoluteValue R S} {x : R} :
    congr v w (.refl R) ((equiv v).symm x) = (equiv w).symm x := by simp

@[deprecated "Use `simp`." (since := "2026-03-02")]
/--
theorem `equivWithAbs_symm_equiv_symm_apply` / 定理 `equivWithAbs_symm_equiv_symm_apply`

English:
theorem equivWithAbs_symm_equiv_symm_apply
  given: {v w : AbsoluteValue R S} {x : R}
  proof: by simp

中文:
定理 equivWithAbs_symm_equiv_symm_apply
  条件: {v w : AbsoluteValue R S} {x : R}
  证明: by simp
-/
theorem equivWithAbs_symm_equiv_symm_apply {v w : AbsoluteValue R S} {x : R} :
    (congr v w (.refl R)).symm ((equiv w).symm x) = (equiv v).symm x := by simp

end Semiring

section CommSemiring

variable [CommSemiring R] (v : AbsoluteValue R S)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommSemiring (WithAbs v)
  body: fast_instance% (equiv v).commSemiring

中文:
实例 :
  签名: CommSemiring (WithAbs v)
  定义体: fast_instance% (equiv v).commSemiring

Depends on / 依赖: commSemiring, fast_instance
-/
instance : CommSemiring (WithAbs v) := fast_instance% (equiv v).commSemiring

end CommSemiring

section Ring

variable [Ring R]

instance (v : AbsoluteValue R S) : Ring (WithAbs v) := fast_instance% (equiv v).ring

/--
Instance `normedRing` / 实例 `normedRing`

English:
instance normedRing
  signature: (v : AbsoluteValue R Real)
  body: letI := v.toNormedRing
  fast_instance% (equiv v).normedRing

中文:
实例 normedRing
  签名: (v : AbsoluteValue R 实数)
  定义体: letI := v.toNormedRing
  fast_instance% (equiv v).normedRing

Depends on / 依赖: fast_instance, normedRing, toNormedRing, v.toNormedRing
-/
noncomputable instance normedRing (v : AbsoluteValue R Real) : NormedRing (WithAbs v) :=
  letI := v.toNormedRing
  fast_instance% (equiv v).normedRing

/--
lemma `norm_eq_apply_ofAbs` / 引理 `norm_eq_apply_ofAbs`

English:
lemma norm_eq_apply_ofAbs
  given: (v : AbsoluteValue R Real) (x : WithAbs v)
  statement: ‖x‖ = v x.ofAbs
  proof: rfl

中文:
引理 norm_eq_apply_ofAbs
  条件: (v : AbsoluteValue R 实数) (x : WithAbs v)
  结论: ‖x‖ = v x.ofAbs
  证明: rfl
-/
lemma norm_eq_apply_ofAbs (v : AbsoluteValue R Real) (x : WithAbs v) : ‖x‖ = v x.ofAbs := rfl
/--
lemma `norm_toAbs_eq` / 引理 `norm_toAbs_eq`

English:
lemma norm_toAbs_eq
  given: (v : AbsoluteValue R Real) (x : R)
  statement: ‖toAbs v x‖ = v x
  proof: rfl

@[deprecated (since := "2026-03-02")] alias norm_eq_abv := norm_eq_apply_ofAbs
@[deprecated (since := "2026-03-02")] alias norm_eq_abv' := norm_toAbs_eq

中文:
引理 norm_toAbs_eq
  条件: (v : AbsoluteValue R 实数) (x : R)
  结论: ‖toAbs v x‖ = v x
  证明: rfl

@[deprecated (since := "2026-03-02")] alias norm_eq_abv := norm_eq_apply_ofAbs
@[deprecated (since := "2026-03-02")] alias norm_eq_abv' := norm_toAbs_eq
-/
lemma norm_toAbs_eq (v : AbsoluteValue R Real) (x : R) : ‖toAbs v x‖ = v x := rfl

@[deprecated (since := "2026-03-02")] alias norm_eq_abv := norm_eq_apply_ofAbs
@[deprecated (since := "2026-03-02")] alias norm_eq_abv' := norm_toAbs_eq

variable (v : AbsoluteValue R S)

/--
lemma `toAbs_sub` / 引理 `toAbs_sub`

English:
lemma toAbs_sub
  given: (x y : R)
  statement: toAbs v (x - y) = toAbs v x - toAbs v y
  proof: rfl

中文:
引理 toAbs_sub
  条件: (x y : R)
  结论: toAbs v (x - y) = toAbs v x - toAbs v y
  证明: rfl
-/
@[simp] lemma toAbs_sub (x y : R) : toAbs v (x - y) = toAbs v x - toAbs v y := rfl
/--
lemma `ofAbs_sub` / 引理 `ofAbs_sub`

English:
lemma ofAbs_sub
  given: (x y : WithAbs v)
  statement: ofAbs (x - y) = ofAbs x - ofAbs y
  proof: rfl

中文:
引理 ofAbs_sub
  条件: (x y : WithAbs v)
  结论: ofAbs (x - y) = ofAbs x - ofAbs y
  证明: rfl
-/
@[simp] lemma ofAbs_sub (x y : WithAbs v) : ofAbs (x - y) = ofAbs x - ofAbs y := rfl

/--
lemma `toAbs_neg` / 引理 `toAbs_neg`

English:
lemma toAbs_neg
  given: (x : R)
  statement: toAbs v (-x) = - toAbs v x
  proof: rfl

中文:
引理 toAbs_neg
  条件: (x : R)
  结论: toAbs v (-x) = - toAbs v x
  证明: rfl
-/
@[simp] lemma toAbs_neg (x : R) : toAbs v (-x) = - toAbs v x := rfl
/--
lemma `ofAbs_neg` / 引理 `ofAbs_neg`

English:
lemma ofAbs_neg
  given: (x : WithAbs v)
  statement: ofAbs (-x) = - ofAbs x
  proof: rfl

中文:
引理 ofAbs_neg
  条件: (x : WithAbs v)
  结论: ofAbs (-x) = - ofAbs x
  证明: rfl
-/
@[simp] lemma ofAbs_neg (x : WithAbs v) : ofAbs (-x) = - ofAbs x := rfl

end Ring

section CommRing

variable [CommRing R] (v : AbsoluteValue R S)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (WithAbs v)
  body: fast_instance% (equiv v).commRing

中文:
实例 :
  签名: CommRing (WithAbs v)
  定义体: fast_instance% (equiv v).commRing

Depends on / 依赖: commRing, fast_instance
-/
instance : CommRing (WithAbs v) := fast_instance% (equiv v).commRing

end CommRing

section Module

variable {R T : Type*} [Semiring R] (v : AbsoluteValue R S)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R T] : SMul (WithAbs v) T where
  body: ofAbs x • t

中文:
实例 [SMul
  签名: R T] : SMul (WithAbs v) T where
  定义体: ofAbs x • t
-/
instance [SMul R T] : SMul (WithAbs v) T where
  smul x t := ofAbs x • t

/--
theorem `smul_left_def` / 定理 `smul_left_def`

English:
theorem smul_left_def
  given: [SMul R T] (x : WithAbs v) (t : T)
  proof: rfl

中文:
定理 smul_left_def
  条件: [SMul R T] (x : WithAbs v) (t : T)
  证明: rfl
-/
theorem smul_left_def [SMul R T] (x : WithAbs v) (t : T) :
    x • t = ofAbs x • t := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R T] [FaithfulSMul R T] : FaithfulSMul (WithAbs v) T where
  body: ofAbs_injective v FaithfulSMul.eq_of_smul_eq_smul h

中文:
实例 [SMul
  签名: R T] [FaithfulSMul R T] : FaithfulSMul (WithAbs v) T where
  定义体: ofAbs_injective v FaithfulSMul.eq_of_smul_eq_smul h

Depends on / 依赖: FaithfulSMul, FaithfulSMul.eq_of_smul_eq_smul, eq_of_smul_eq_smul, ofAbs_injective
-/
instance [SMul R T] [FaithfulSMul R T] : FaithfulSMul (WithAbs v) T where
eq_of_smul_eq_smul h := ofAbs_injective v FaithfulSMul.eq_of_smul_eq_smul h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: T R] : SMul T (WithAbs v)
  body: Equiv.smul T { toFun := ofAbs, invFun := toAbs v }

中文:
实例 [SMul
  签名: T R] : SMul T (WithAbs v)
  定义体: Equiv.smul T { toFun := ofAbs, invFun := toAbs v }

Depends on / 依赖: Equiv.smul, invFun
-/
instance [SMul T R] : SMul T (WithAbs v) := Equiv.smul T { toFun := ofAbs, invFun := toAbs v }

/--
theorem `smul_right_def` / 定理 `smul_right_def`

English:
theorem smul_right_def
  given: [SMul T R] (t : T) (x : WithAbs v)
  proof: rfl

中文:
定理 smul_right_def
  条件: [SMul T R] (t : T) (x : WithAbs v)
  证明: rfl
-/
theorem smul_right_def [SMul T R] (t : T) (x : WithAbs v) :
    t • x = toAbs v (t • x.ofAbs) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: T R] [FaithfulSMul T R] : FaithfulSMul T (WithAbs v) where
  body: by
    simp only [smul_right_def, toAbs.injEq] at h
    exact FaithfulSMul.eq_of_smul_eq_smul fun _ => h (toAbs v _)

中文:
实例 [SMul
  签名: T R] [FaithfulSMul T R] : FaithfulSMul T (WithAbs v) where
  定义体: by
    simp only [smul_right_def, toAbs.injEq] at h
    exact FaithfulSMul.eq_of_smul_eq_smul fun _ => h (toAbs v _)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.eq_of_smul_eq_smul, eq_of_smul_eq_smul, smul_right_def, toAbs.injEq
-/
instance [SMul T R] [FaithfulSMul T R] : FaithfulSMul T (WithAbs v) where
  eq_of_smul_eq_smul h := by
    simp only [smul_right_def, toAbs.injEq] at h
    exact FaithfulSMul.eq_of_smul_eq_smul fun _ => h (toAbs v _)

instance {P : Type*} [SMul T P] [SMul R T] [SMul R P] [IsScalarTower R T P] :
    IsScalarTower (WithAbs v) T P where
  smul_assoc := by simp [smul_left_def]

instance {P : Type*} [SMul P R] [SMul T R] [SMul P T]
    [IsScalarTower P T R] : IsScalarTower P T (WithAbs v) := (equiv v).isScalarTower P T

instance {P : Type*} [SMul P R] [SMul P T] [SMul R T]
    [IsScalarTower P R T] : IsScalarTower P (WithAbs v) T where
  smul_assoc := by simp [smul_right_def, smul_left_def]

/--
Instance `moduleLeft` / 实例 `moduleLeft`

English:
instance moduleLeft
  signature: [AddCommMonoid T] [Module R T]
  body: fast_instance% .compHom T (equiv v).toRingHom

@[deprecated (since := "2026-03-02")] alias instModule_left := moduleLeft

中文:
实例 moduleLeft
  签名: [AddCommMonoid T] [Module R T]
  定义体: fast_instance% .compHom T (equiv v).toRingHom

@[deprecated (since := "2026-03-02")] alias instModule_left := moduleLeft

Depends on / 依赖: compHom, fast_instance, toRingHom
-/
instance moduleLeft [AddCommMonoid T] [Module R T] : Module (WithAbs v) T :=
  fast_instance% .compHom T (equiv v).toRingHom

@[deprecated (since := "2026-03-02")] alias instModule_left := moduleLeft

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: T] [Module T R] : Module T (WithAbs v)
  body: fast_instance% (equiv v).module T

@[deprecated (since := "2026-03-02")] alias instModule_right := instModule

中文:
实例 [Semiring
  签名: T] [Module T R] : Module T (WithAbs v)
  定义体: fast_instance% (equiv v).module T

@[deprecated (since := "2026-03-02")] alias instModule_right := instModule

Depends on / 依赖: fast_instance, module
-/
instance [Semiring T] [Module T R] : Module T (WithAbs v) :=
  fast_instance% (equiv v).module T

@[deprecated (since := "2026-03-02")] alias instModule_right := instModule

variable [Semiring T] [Module R T] (v : AbsoluteValue T S)

variable (R) in
/--
Definition of `linearEquiv` / `linearEquiv` 的定义

English:
definition linearEquiv
  signature: : WithAbs v ≃ₗ[R] T
  body: (equiv v).linearEquiv R

中文:
定义 linearEquiv
  签名: : WithAbs v ≃ₗ[R] T
  定义体: (equiv v).linearEquiv R

Depends on / 依赖: linearEquiv
-/
def linearEquiv : WithAbs v ≃ₗ[R] T := (equiv v).linearEquiv R

variable {v}

/--
theorem `linearEquiv_apply` / 定理 `linearEquiv_apply`

English:
theorem linearEquiv_apply
  given: (x : WithAbs v)
  statement: linearEquiv R v x = x.ofAbs
  proof: rfl

中文:
定理 linearEquiv_apply
  条件: (x : WithAbs v)
  结论: linearEquiv R v x = x.ofAbs
  证明: rfl
-/
@[simp] theorem linearEquiv_apply (x : WithAbs v) : linearEquiv R v x = x.ofAbs := rfl
/--
theorem `linearEquiv_symm_apply` / 定理 `linearEquiv_symm_apply`

English:
theorem linearEquiv_symm_apply
  given: (x : T)
  statement: (linearEquiv R v).symm x = toAbs v x
  proof: rfl

中文:
定理 linearEquiv_symm_apply
  条件: (x : T)
  结论: (linearEquiv R v).symm x = toAbs v x
  证明: rfl
-/
@[simp] theorem linearEquiv_symm_apply (x : T) : (linearEquiv R v).symm x = toAbs v x := rfl

end Module

section algebra

variable {R T : Type*} [CommSemiring R] [Semiring T] [Algebra R T]

variable (T) in
/--
Instance `algebraLeft` / 实例 `algebraLeft`

English:
instance algebraLeft
  signature: (v : AbsoluteValue R S)
  body: fast_instance% .compHom T (equiv v).toRingHom

中文:
实例 algebraLeft
  签名: (v : AbsoluteValue R S)
  定义体: fast_instance% .compHom T (equiv v).toRingHom

Depends on / 依赖: compHom, fast_instance, toRingHom
-/
instance algebraLeft (v : AbsoluteValue R S) : Algebra (WithAbs v) T :=
  fast_instance% .compHom T (equiv v).toRingHom

/--
theorem `algebraMap_left_apply` / 定理 `algebraMap_left_apply`

English:
theorem algebraMap_left_apply
  given: {v : AbsoluteValue R S} (x : WithAbs v)
  proof: rfl

中文:
定理 algebraMap_left_apply
  条件: {v : AbsoluteValue R S} (x : WithAbs v)
  证明: rfl
-/
theorem algebraMap_left_apply {v : AbsoluteValue R S} (x : WithAbs v) :
    algebraMap (WithAbs v) T x = algebraMap R T x.ofAbs := rfl

/--
theorem `algebraMap_left_injective` / 定理 `algebraMap_left_injective`

English:
theorem algebraMap_left_injective
  statement: (v : AbsoluteValue R S)
  proof: h.comp (ofAbs_injective v)

中文:
定理 algebraMap_left_injective
  结论: (v : AbsoluteValue R S)
  证明: h.comp (ofAbs_injective v)

Depends on / 依赖: h.comp, ofAbs_injective
-/
theorem algebraMap_left_injective (v : AbsoluteValue R S)
    (h : Function.Injective (algebraMap R T)) :
    Function.Injective (algebraMap (WithAbs v) T) :=
  h.comp (ofAbs_injective v)

instance (v : AbsoluteValue T S) : Algebra R (WithAbs v) :=
  fast_instance% (equiv v).algebra R

/--
theorem `algebraMap_right_apply` / 定理 `algebraMap_right_apply`

English:
theorem algebraMap_right_apply
  given: {v : AbsoluteValue T S} (x : R)
  proof: rfl

中文:
定理 algebraMap_right_apply
  条件: {v : AbsoluteValue T S} (x : R)
  证明: rfl
-/
theorem algebraMap_right_apply {v : AbsoluteValue T S} (x : R) :
    algebraMap R (WithAbs v) x = toAbs v (algebraMap R T x) := rfl

/--
theorem `algebraMap_right_injective` / 定理 `algebraMap_right_injective`

English:
theorem algebraMap_right_injective
  statement: (v : AbsoluteValue T S)
  proof: (toAbs_injective v).comp h

中文:
定理 algebraMap_right_injective
  结论: (v : AbsoluteValue T S)
  证明: (toAbs_injective v).comp h

Depends on / 依赖: toAbs_injective
-/
theorem algebraMap_right_injective (v : AbsoluteValue T S)
    (h : Function.Injective (algebraMap R T)) : Function.Injective (algebraMap R (WithAbs v)) :=
  (toAbs_injective v).comp h

/--
theorem `ofAbs_algebraMap` / 定理 `ofAbs_algebraMap`

English:
theorem ofAbs_algebraMap
  given: (v : AbsoluteValue R S) (w : AbsoluteValue T S) (x : WithAbs v)
  proof: rfl

@[deprecated (since := "2026-03-02")] alias instAlgebra_left := algebraLeft
@[deprecated (since := "2026-03-02")] alias instAlgebra_right := instAlgebra

中文:
定理 ofAbs_algebraMap
  条件: (v : AbsoluteValue R S) (w : AbsoluteValue T S) (x : WithAbs v)
  证明: rfl

@[deprecated (since := "2026-03-02")] alias instAlgebra_left := algebraLeft
@[deprecated (since := "2026-03-02")] alias instAlgebra_right := instAlgebra
-/
theorem ofAbs_algebraMap (v : AbsoluteValue R S) (w : AbsoluteValue T S) (x : WithAbs v) :
    (algebraMap (WithAbs v) (WithAbs w) x).ofAbs = algebraMap R T x.ofAbs := rfl

@[deprecated (since := "2026-03-02")] alias instAlgebra_left := algebraLeft
@[deprecated (since := "2026-03-02")] alias instAlgebra_right := instAlgebra

variable (R) in
/--
Definition of `algEquiv` / `algEquiv` 的定义

English:
definition algEquiv
  signature: (v : AbsoluteValue T S)
  body: (equiv v).algEquiv R

中文:
定义 algEquiv
  签名: (v : AbsoluteValue T S)
  定义体: (equiv v).algEquiv R

Depends on / 依赖: algEquiv
-/
def algEquiv (v : AbsoluteValue T S) : (WithAbs v) ≃ₐ[R] T := (equiv v).algEquiv R

/--
theorem `algEquiv_apply` / 定理 `algEquiv_apply`

English:
theorem algEquiv_apply
  given: (v : AbsoluteValue T S) (x : WithAbs v)
  proof: rfl

中文:
定理 algEquiv_apply
  条件: (v : AbsoluteValue T S) (x : WithAbs v)
  证明: rfl
-/
@[simp] theorem algEquiv_apply (v : AbsoluteValue T S) (x : WithAbs v) :
    algEquiv R v x = x.ofAbs := rfl
/--
theorem `algEquiv_symm_apply` / 定理 `algEquiv_symm_apply`

English:
theorem algEquiv_symm_apply
  given: (v : AbsoluteValue T S) (x : T)
  proof: rfl

中文:
定理 algEquiv_symm_apply
  条件: (v : AbsoluteValue T S) (x : T)
  证明: rfl
-/
@[simp] theorem algEquiv_symm_apply (v : AbsoluteValue T S) (x : T) :
    (algEquiv R v).symm x = toAbs v x := rfl

end algebra

end WithAbs

namespace AbsoluteValue

variable {K L S : Type*} [CommRing K] [IsSimpleRing K] [CommRing L] [Algebra K L] [PartialOrder S]
  [Nontrivial L] [Semiring S]

/--
Definition of `LiesOver` / `LiesOver` 的定义

English:
class LiesOver
  parameters: (w : AbsoluteValue L S) (v : AbsoluteValue K S)
  axioms and operations (1):
    - comp_eq((w) (v)) : w.comp (algebraMap K L).injective = v

中文:
类 LiesOver
  参数: (w : AbsoluteValue L S) (v : AbsoluteValue K S)
  公理与运算 (1 个):
    - comp_eq((w) (v)) : w.comp (algebraMap K L).injective = v
-/
class LiesOver (w : AbsoluteValue L S) (v : AbsoluteValue K S) : Prop where
  comp_eq (w) (v) : w.comp (algebraMap K L).injective = v

end AbsoluteValue
