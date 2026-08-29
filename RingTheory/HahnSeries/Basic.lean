/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Order.WellFoundedSet

/-!
# Hahn Series

If `Γ` is ordered and `R` has zero, then the type `HahnSeries Γ R`, which we denote as `R⟦Γ⟧`,
consists of formal series over `Γ` with coefficients in `R`, whose supports are partially
well-ordered. With further structure on `R` and `Γ`, we can add further structure on `R⟦Γ⟧`, with
the most studied case being when `Γ` is a linearly ordered abelian group and `R` is a field, in
which case `R⟦Γ⟧` is a valued field, with value group `Γ`.

These generalize Laurent series (with value group `ℤ`), and Laurent series are implemented that way
in the file `Mathlib/RingTheory/LaurentSeries.lean`.

## Main Definitions

* If `Γ` is ordered and `R` has zero, then `R⟦Γ⟧` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are partially well-ordered.
* `support x` is the subset of `Γ` whose coefficients are nonzero.
* `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
* `orderTop x` is a minimal element of `WithTop Γ` where `x` has a nonzero
  coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
* `order x` is a minimal element of `Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is zero
  when `x = 0`.
* `map` takes each coefficient of a Hahn series to its target under a zero-preserving map.
* `embDomain` preserves coefficients, but embeds the index set `Γ` in a larger poset.

## References

- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

@[expose] public section


open Finset Function

noncomputable section

/-- If `Γ` is linearly ordered and `R` has zero, then `R⟦Γ⟧` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded. -/
@[ext]
/--
Definition of `HahnSeries` / `HahnSeries` 的定义

English:
structure HahnSeries
  parameters: (Γ : Type*) (R : Type*) [PartialOrder Γ] [Zero R]
  axioms and operations (2):
    - coeff : Γ -> R
    - isPWO_support' : (Function.support coeff).IsPWO

中文:
结构 Hahn级数
  参数: (Γ : 类型) (R : 类型) [偏序 Γ] [零 R]
  公理与运算 (2 个):
    - coeff : Γ -> R
    - isPWO_support' : (函数.support coeff).IsPWO
-/
structure HahnSeries (Γ : Type*) (R : Type*) [PartialOrder Γ] [Zero R] where
  /-- The coefficient function of a Hahn Series. -/
  coeff : Γ -> R
  isPWO_support' : (Function.support coeff).IsPWO

variable {Γ Γ' R S : Type*}

namespace HahnSeries

@[inherit_doc HahnSeries]
scoped syntax:max (priority := high) term noWs "⟦" term "⟧" : term

macro_rules | `($R⟦$M⟧) => `(HahnSeries $M $R)

/-- Unexpander for `HahnSeries`. -/
@[scoped app_unexpander HahnSeries]
meta def unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $M $R) => `($R⟦$M⟧)
  | _ => throw ()

section Zero

variable [PartialOrder Γ] [Zero R]

/--
theorem `coeff_injective` / 定理 `coeff_injective`

English:
theorem coeff_injective
  statement: Injective (coeff : R⟦Γ⟧ -> Γ -> R)
  proof: fun _ _ => HahnSeries.ext

@[simp]

中文:
定理 coeff_injective
  结论: 单射 (coeff : R⟦Γ⟧ -> Γ -> R)
  证明: fun _ _ => HahnSeries.ext

@[simp]

Depends on / 依赖: HahnSeries, HahnSeries.ext
-/
theorem coeff_injective : Injective (coeff : R⟦Γ⟧ -> Γ -> R) :=
  fun _ _ => HahnSeries.ext

@[simp]
/--
theorem `coeff_inj` / 定理 `coeff_inj`

English:
theorem coeff_inj
  given: {x y : R⟦Γ⟧}
  statement: x.coeff = y.coeff ↔ x = y
  proof: coeff_injective.eq_iff

中文:
定理 coeff_inj
  条件: {x y : R⟦Γ⟧}
  结论: x.coeff = y.coeff ↔ x = y
  证明: coeff_injective.eq_iff

Depends on / 依赖: coeff_injective, coeff_injective.eq_iff, eq_iff
-/
theorem coeff_inj {x y : R⟦Γ⟧} : x.coeff = y.coeff ↔ x = y :=
  coeff_injective.eq_iff

/-- The support of a Hahn series is just the set of indices whose coefficients are nonzero.
  Notably, it is well-founded. -/
nonrec def support (x : R⟦Γ⟧) : Set Γ :=
  support x.coeff

@[simp]
/--
theorem `support_mk` / 定理 `support_mk`

English:
theorem support_mk
  given: (f : Γ -> R) (h)
  statement: support ⟨f, h⟩ = Function.support f
  proof: rfl

@[simp]

中文:
定理 support_mk
  条件: (f : Γ -> R) (h)
  结论: support ⟨f, h⟩ = 函数.support f
  证明: rfl

@[simp]
-/
theorem support_mk (f : Γ -> R) (h) : support ⟨f, h⟩ = Function.support f :=
  rfl

@[simp]
/--
theorem `isPWO_support` / 定理 `isPWO_support`

English:
theorem isPWO_support
  given: (x : R⟦Γ⟧)
  statement: x.support.IsPWO
  proof: x.isPWO_support'

@[simp]

中文:
定理 isPWO_support
  条件: (x : R⟦Γ⟧)
  结论: x.support.IsPWO
  证明: x.isPWO_support'

@[simp]

Depends on / 依赖: isPWO_support, x.isPWO_support
-/
theorem isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO :=
  x.isPWO_support'

@[simp]
/--
theorem `isWF_support` / 定理 `isWF_support`

English:
theorem isWF_support
  given: (x : R⟦Γ⟧)
  statement: x.support.IsWF
  proof: x.isPWO_support.isWF

@[simp]

中文:
定理 isWF_support
  条件: (x : R⟦Γ⟧)
  结论: x.support.IsWF
  证明: x.isPWO_support.isWF

@[simp]

Depends on / 依赖: isPWO_support, x.isPWO_support.isWF
-/
theorem isWF_support (x : R⟦Γ⟧) : x.support.IsWF :=
  x.isPWO_support.isWF

@[simp]
/--
theorem `mem_support` / 定理 `mem_support`

English:
theorem mem_support
  given: (x : R⟦Γ⟧) (a : Γ)
  statement: a in x.support ↔ x.coeff a != 0
  proof: .rfl

中文:
定理 mem_support
  条件: (x : R⟦Γ⟧) (a : Γ)
  结论: a in x.support ↔ x.coeff a != 0
  证明: .rfl
-/
theorem mem_support (x : R⟦Γ⟧) (a : Γ) : a in x.support ↔ x.coeff a != 0 :=
  .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero R⟦Γ⟧
  body: ⟨{ coeff := 0
      isPWO_support' := by simp }⟩

中文:
实例 :
  签名: 零 R⟦Γ⟧
  定义体: ⟨{ coeff := 0
      isPWO_support' := by simp }⟩

Depends on / 依赖: isPWO_support
-/
instance : Zero R⟦Γ⟧ :=
  ⟨{ coeff := 0
      isPWO_support' := by simp }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited R⟦Γ⟧
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 R⟦Γ⟧
  定义体: ⟨0⟩
-/
instance : Inhabited R⟦Γ⟧ :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: R] : Subsingleton R⟦Γ⟧
  body: ⟨fun _ _ => HahnSeries.ext (by subsingleton)⟩

中文:
实例 [子单例
  签名: R] : 子单例 R⟦Γ⟧
  定义体: ⟨fun _ _ => HahnSeries.ext (by subsingleton)⟩

Depends on / 依赖: HahnSeries, HahnSeries.ext, subsingleton
-/
instance [Subsingleton R] : Subsingleton R⟦Γ⟧ :=
  ⟨fun _ _ => HahnSeries.ext (by subsingleton)⟩

/--
theorem `coeff_zero'` / 定理 `coeff_zero'`

English:
theorem coeff_zero'
  statement: (0 : R⟦Γ⟧).coeff = 0
  proof: rfl

@[simp]

中文:
定理 coeff_zero'
  结论: (0 : R⟦Γ⟧).coeff = 0
  证明: rfl

@[simp]
-/
theorem coeff_zero' : (0 : R⟦Γ⟧).coeff = 0 :=
  rfl

@[simp]
/--
theorem `coeff_zero` / 定理 `coeff_zero`

English:
theorem coeff_zero
  given: {a : Γ}
  statement: (0 : R⟦Γ⟧).coeff a = 0
  proof: rfl

@[simp]

中文:
定理 coeff_zero
  条件: {a : Γ}
  结论: (0 : R⟦Γ⟧).coeff a = 0
  证明: rfl

@[simp]
-/
theorem coeff_zero {a : Γ} : (0 : R⟦Γ⟧).coeff a = 0 :=
  rfl

@[simp]
/--
theorem `coeff_fun_eq_zero_iff` / 定理 `coeff_fun_eq_zero_iff`

English:
theorem coeff_fun_eq_zero_iff
  given: {x : R⟦Γ⟧}
  statement: x.coeff = 0 ↔ x = 0
  proof: coeff_injective.eq_iff' rfl

中文:
定理 coeff_fun_eq_zero_iff
  条件: {x : R⟦Γ⟧}
  结论: x.coeff = 0 ↔ x = 0
  证明: coeff_injective.eq_iff' rfl

Depends on / 依赖: coeff_injective, coeff_injective.eq_iff, eq_iff
-/
theorem coeff_fun_eq_zero_iff {x : R⟦Γ⟧} : x.coeff = 0 ↔ x = 0 :=
  coeff_injective.eq_iff' rfl

/--
theorem `ne_zero_of_coeff_ne_zero` / 定理 `ne_zero_of_coeff_ne_zero`

English:
theorem ne_zero_of_coeff_ne_zero
  given: {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0)
  statement: x != 0
  proof: mt (fun x0 => (x0.symm ▸ coeff_zero : x.coeff g = 0)) h

@[simp]

中文:
定理 ne_zero_of_coeff_ne_zero
  条件: {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0)
  结论: x != 0
  证明: mt (fun x0 => (x0.symm ▸ coeff_zero : x.coeff g = 0)) h

@[simp]

Depends on / 依赖: coeff_zero, x.coeff, x0.symm
-/
theorem ne_zero_of_coeff_ne_zero {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0) : x != 0 :=
  mt (fun x0 => (x0.symm ▸ coeff_zero : x.coeff g = 0)) h

@[simp]
/--
theorem `support_zero` / 定理 `support_zero`

English:
theorem support_zero
  statement: support (0 : R⟦Γ⟧) = ∅
  proof: Function.support_zero

@[simp]
nonrec theorem support_nonempty_iff {x : R⟦Γ⟧} : x.support.Nonempty ↔ x != 0 := by
  rw [support]; rw [support_nonempty_iff]; rw [Ne]; rw [coeff_fun_eq_zero_iff]

@[simp]

中文:
定理 support_zero
  结论: support (0 : R⟦Γ⟧) = ∅
  证明: Function.support_zero

@[simp]
nonrec theorem support_nonempty_iff {x : R⟦Γ⟧} : x.support.Nonempty ↔ x != 0 := by
  rw [support]; rw [support_nonempty_iff]; rw [Ne]; rw [coeff_fun_eq_zero_iff]

@[simp]

Depends on / 依赖: Function, Function.support_zero, support_zero, useful
-/
theorem support_zero : support (0 : R⟦Γ⟧) = ∅ :=
  Function.support_zero

@[simp]
nonrec theorem support_nonempty_iff {x : R⟦Γ⟧} : x.support.Nonempty ↔ x != 0 := by
  rw [support]; rw [support_nonempty_iff]; rw [Ne]; rw [coeff_fun_eq_zero_iff]

@[simp]
/--
theorem `support_eq_empty_iff` / 定理 `support_eq_empty_iff`

English:
theorem support_eq_empty_iff
  given: {x : R⟦Γ⟧}
  statement: x.support = ∅ ↔ x = 0
  proof: Function.support_eq_empty_iff.trans coeff_fun_eq_zero_iff

中文:
定理 support_eq_empty_iff
  条件: {x : R⟦Γ⟧}
  结论: x.support = ∅ ↔ x = 0
  证明: Function.support_eq_empty_iff.trans coeff_fun_eq_zero_iff

Depends on / 依赖: CSLift, CSLift.lift, CSLiftVal, Function, Function.support_eq_empty_iff.trans, coeff_fun_eq_zero_iff, support_eq_empty_iff
-/
theorem support_eq_empty_iff {x : R⟦Γ⟧} : x.support = ∅ ↔ x = 0 :=
  Function.support_eq_empty_iff.trans coeff_fun_eq_zero_iff

/-- The map of Hahn series induced by applying a zero-preserving map to each coefficient. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: [Zero S] (x : R⟦Γ⟧) {F : Type*} [FunLike F R S] [ZeroHomClass F R S] (f : F)
  body: f (x.coeff g)
isPWO_support' := x.isPWO_support.mono Function.support_comp_subset (ZeroHomClass.map_zero f) _

@[simp]

中文:
定义 map
  签名: [零 S] (x : R⟦Γ⟧) {F : 类型} [函数状 F R S] [保零态射类 F R S] (f : F)
  定义体: f (x.coeff g)
isPWO_support' := x.isPWO_support.mono Function.support_comp_subset (ZeroHomClass.map_zero f) _

@[simp]

Depends on / 依赖: x.coeff
-/
def map [Zero S] (x : R⟦Γ⟧) {F : Type*} [FunLike F R S] [ZeroHomClass F R S] (f : F) : S⟦Γ⟧ where
  coeff g := f (x.coeff g)
isPWO_support' := x.isPWO_support.mono Function.support_comp_subset (ZeroHomClass.map_zero f) _

@[simp]
/--
lemma `map_zero` / 引理 `map_zero`

English:
lemma map_zero
  given: [Zero S] (f : ZeroHom R S)
  statement: (0 : R⟦Γ⟧).map f = 0
  proof: by
  ext; simp

中文:
引理 map_zero
  条件: [零 S] (f : 保零态射 R S)
  结论: (0 : R⟦Γ⟧).map f = 0
  证明: by
  ext; simp
-/
protected lemma map_zero [Zero S] (f : ZeroHom R S) : (0 : R⟦Γ⟧).map f = 0 := by
  ext; simp

/--
theorem `support_map_subset` / 定理 `support_map_subset`

English:
theorem support_map_subset
  given: [Zero S] (x : R⟦Γ⟧) (f : ZeroHom R S)
  proof: Function.support_comp_subset (ZeroHomClass.map_zero f) _

中文:
定理 support_map_subset
  条件: [零 S] (x : R⟦Γ⟧) (f : 保零态射 R S)
  证明: Function.support_comp_subset (ZeroHomClass.map_zero f) _

Depends on / 依赖: Function, Function.support_comp_subset, ZeroHomClass, ZeroHomClass.map_zero, map_zero, support_comp_subset
-/
theorem support_map_subset [Zero S] (x : R⟦Γ⟧) (f : ZeroHom R S) :
    (x.map f).support subseteq x.support :=
  Function.support_comp_subset (ZeroHomClass.map_zero f) _

/--
Definition of `ofIterate` / `ofIterate` 的定义

English:
definition ofIterate
  signature: [PartialOrder Γ'] (x : R⟦Γ'⟧⟦Γ⟧)
  body: fun g => coeff (coeff x g.1) g.2
  isPWO_support' := by
    refine Set.PartiallyWellOrderedOn.subsetProdLex ?_ ?_
    · refine Set.IsPWO.mono x.isPWO_support' ?_
      simp_rw [Set.image_subset_iff, support_subset_iff, Set.mem_preimage, Function.mem_support]
      exact fun _ => ne_zero_of_coeff_ne_

中文:
定义 ofIterate
  签名: [偏序 Γ'] (x : R⟦Γ'⟧⟦Γ⟧)
  定义体: fun g => coeff (coeff x g.1) g.2
  isPWO_support' := by
    refine Set.PartiallyWellOrderedOn.subsetProdLex ?_ ?_
    · refine Set.IsPWO.mono x.isPWO_support' ?_
      simp_rw [Set.image_subset_iff, support_subset_iff, Set.mem_preimage, Function.mem_support]
      exact fun _ => ne_zero_of_coeff_ne_
-/
def ofIterate [PartialOrder Γ'] (x : R⟦Γ'⟧⟦Γ⟧) : R⟦Γ ×ₗ Γ'⟧ where
  coeff := fun g => coeff (coeff x g.1) g.2
  isPWO_support' := by
    refine Set.PartiallyWellOrderedOn.subsetProdLex ?_ ?_
    · refine Set.IsPWO.mono x.isPWO_support' ?_
      simp_rw [Set.image_subset_iff, support_subset_iff, Set.mem_preimage, Function.mem_support]
      exact fun _ => ne_zero_of_coeff_ne_zero
    · exact fun a => by simpa [Function.mem_support, ne_eq] using! (x.coeff a).isPWO_support'

@[simp]
/--
lemma `mk_eq_zero` / 引理 `mk_eq_zero`

English:
lemma mk_eq_zero
  given: (f : Γ -> R) (h)
  statement: HahnSeries.mk f h = 0 ↔ f = 0
  proof: by
  simp_rw [HahnSeries.ext_iff, funext_iff, coeff_zero, Pi.zero_apply]

中文:
引理 mk_eq_zero
  条件: (f : Γ -> R) (h)
  结论: Hahn级数.mk f h = 0 ↔ f = 0
  证明: by
  simp_rw [HahnSeries.ext_iff, funext_iff, coeff_zero, Pi.zero_apply]

Depends on / 依赖: HahnSeries, HahnSeries.ext_iff, Pi.zero_apply, coeff_zero, ext_iff, funext_iff, simp_rw, zero_apply
-/
lemma mk_eq_zero (f : Γ -> R) (h) : HahnSeries.mk f h = 0 ↔ f = 0 := by
  simp_rw [HahnSeries.ext_iff, funext_iff, coeff_zero, Pi.zero_apply]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toIterate` / `toIterate` 的定义

English:
definition toIterate
  signature: [PartialOrder Γ'] (x : R⟦Γ ×ₗ Γ'⟧)
  body: fun g => {
    coeff := fun g' => coeff x (g, g')
    isPWO_support' := Set.PartiallyWellOrderedOn.fiberProdLex x.isPWO_support' g
  }
  isPWO_support' := by
    have h₁ : (Function.support fun g => HahnSeries.mk (fun g' => x.coeff (g, g'))
        (Set.PartiallyWellOrderedOn.fiberProdLex x.isPWO_su

中文:
定义 toIterate
  签名: [偏序 Γ'] (x : R⟦Γ ×ₗ Γ'⟧)
  定义体: fun g => {
    coeff := fun g' => coeff x (g, g')
    isPWO_support' := Set.PartiallyWellOrderedOn.fiberProdLex x.isPWO_support' g
  }
  isPWO_support' := by
    have h₁ : (Function.support fun g => HahnSeries.mk (fun g' => x.coeff (g, g'))
        (Set.PartiallyWellOrderedOn.fiberProdLex x.isPWO_su
-/
def toIterate [PartialOrder Γ'] (x : R⟦Γ ×ₗ Γ'⟧) : R⟦Γ'⟧⟦Γ⟧ where
  coeff := fun g => {
    coeff := fun g' => coeff x (g, g')
    isPWO_support' := Set.PartiallyWellOrderedOn.fiberProdLex x.isPWO_support' g
  }
  isPWO_support' := by
    have h₁ : (Function.support fun g => HahnSeries.mk (fun g' => x.coeff (g, g'))
        (Set.PartiallyWellOrderedOn.fiberProdLex x.isPWO_support' g)) = Function.support
        fun g g' => x.coeff (g, g') := by
      simp only [Function.support, ne_eq, mk_eq_zero]
    rw [h₁]; rw [Function.support_fun_curry x.coeff]
    exact Set.PartiallyWellOrderedOn.imageProdLex x.isPWO_support'

/-- The equivalence between iterated Hahn series and Hahn series on the lex product. -/
@[simps]
/--
Definition of `iterateEquiv` / `iterateEquiv` 的定义

English:
definition iterateEquiv
  signature: [PartialOrder Γ']
  body: ofIterate
  invFun := toIterate
  left_inv := congrFun rfl
  right_inv := congrFun rfl

中文:
定义 iterateEquiv
  签名: [偏序 Γ']
  定义体: ofIterate
  invFun := toIterate
  left_inv := congrFun rfl
  right_inv := congrFun rfl

Depends on / 依赖: ofIterate
-/
def iterateEquiv [PartialOrder Γ'] : R⟦Γ'⟧⟦Γ⟧ ≃ R⟦Γ ×ₗ Γ'⟧ where
  toFun := ofIterate
  invFun := toIterate
  left_inv := congrFun rfl
  right_inv := congrFun rfl

open scoped Classical in
/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (a : Γ)
  body: { coeff := Pi.single a r
      isPWO_support' := (Set.isPWO_singleton a).mono Pi.support_single_subset }
  map_zero' := HahnSeries.ext (Pi.single_zero _)

中文:
定义 single
  签名: (a : Γ)
  定义体: { coeff := Pi.single a r
      isPWO_support' := (Set.isPWO_singleton a).mono Pi.support_single_subset }
  map_zero' := HahnSeries.ext (Pi.single_zero _)

Depends on / 依赖: HahnSeries, HahnSeries.ext, Pi.single, Pi.single_zero, Pi.support_single_subset, Set.isPWO_singleton, isPWO_singleton, isPWO_support, map_zero, single, single_zero, support_single_subset, toRingCompare, x.toRingCompare
-/
def single (a : Γ) : ZeroHom R R⟦Γ⟧ where
  toFun r :=
    { coeff := Pi.single a r
      isPWO_support' := (Set.isPWO_singleton a).mono Pi.support_single_subset }
  map_zero' := HahnSeries.ext (Pi.single_zero _)

variable {a b : Γ} {r : R}

@[simp]
/--
theorem `coeff_single_same` / 定理 `coeff_single_same`

English:
theorem coeff_single_same
  given: (a : Γ) (r : R)
  statement: (single a r).coeff a = r
  proof: by
  classical exact Pi.single_eq_same (M := fun _ => R) a r

@[simp]

中文:
定理 coeff_single_same
  条件: (a : Γ) (r : R)
  结论: (single a r).coeff a = r
  证明: by
  classical exact Pi.single_eq_same (M := fun _ => R) a r

@[simp]

Depends on / 依赖: Pi.single_eq_same, classical, single_eq_same
-/
theorem coeff_single_same (a : Γ) (r : R) : (single a r).coeff a = r := by
  classical exact Pi.single_eq_same (M := fun _ => R) a r

@[simp]
/--
theorem `coeff_single_of_ne` / 定理 `coeff_single_of_ne`

English:
theorem coeff_single_of_ne
  given: (h : b != a)
  statement: (single a r).coeff b = 0
  proof: by
  classical exact Pi.single_eq_of_ne (M := fun _ => R) h r

中文:
定理 coeff_single_of_ne
  条件: (h : b != a)
  结论: (single a r).coeff b = 0
  证明: by
  classical exact Pi.single_eq_of_ne (M := fun _ => R) h r

Depends on / 依赖: Pi.single_eq_of_ne, classical, single_eq_of_ne
-/
theorem coeff_single_of_ne (h : b != a) : (single a r).coeff b = 0 := by
  classical exact Pi.single_eq_of_ne (M := fun _ => R) h r

open scoped Classical in
/--
theorem `coeff_single` / 定理 `coeff_single`

English:
theorem coeff_single
  statement: (single a r).coeff b = if b = a then r else 0
  proof: by
  split_ifs with h <;> simp [h]

@[simp]

中文:
定理 coeff_single
  结论: (single a r).coeff b = if b = a then r else 0
  证明: by
  split_ifs with h <;> simp [h]

@[simp]

Depends on / 依赖: split_ifs
-/
theorem coeff_single : (single a r).coeff b = if b = a then r else 0 := by
  split_ifs with h <;> simp [h]

@[simp]
/--
theorem `support_single_of_ne` / 定理 `support_single_of_ne`

English:
theorem support_single_of_ne
  given: (h : r != 0)
  statement: support (single a r) = {a}
  proof: by
  classical exact Pi.support_single_of_ne h

中文:
定理 support_single_of_ne
  条件: (h : r != 0)
  结论: support (single a r) = {a}
  证明: by
  classical exact Pi.support_single_of_ne h

Depends on / 依赖: Pi.support_single_of_ne, classical, support_single_of_ne
-/
theorem support_single_of_ne (h : r != 0) : support (single a r) = {a} := by
  classical exact Pi.support_single_of_ne h

/--
theorem `support_single_subset` / 定理 `support_single_subset`

English:
theorem support_single_subset
  statement: support (single a r) subseteq {a}
  proof: by
  classical exact Pi.support_single_subset

中文:
定理 support_single_subset
  结论: support (single a r) subseteq {a}
  证明: by
  classical exact Pi.support_single_subset

Depends on / 依赖: Pi.support_single_subset, classical, support_single_subset
-/
theorem support_single_subset : support (single a r) subseteq {a} := by
  classical exact Pi.support_single_subset

/--
theorem `eq_of_mem_support_single` / 定理 `eq_of_mem_support_single`

English:
theorem eq_of_mem_support_single
  given: {b : Γ} (h : b in support (single a r))
  statement: b = a
  proof: support_single_subset h

中文:
定理 eq_of_mem_support_single
  条件: {b : Γ} (h : b in support (single a r))
  结论: b = a
  证明: support_single_subset h

Depends on / 依赖: support_single_subset
-/
theorem eq_of_mem_support_single {b : Γ} (h : b in support (single a r)) : b = a :=
  support_single_subset h

/--
theorem `single_eq_zero` / 定理 `single_eq_zero`

English:
theorem single_eq_zero
  statement: single a (0 : R) = 0
  proof: (single a).map_zero

中文:
定理 single_eq_zero
  结论: single a (0 : R) = 0
  证明: (single a).map_zero

Depends on / 依赖: map_zero, single
-/
theorem single_eq_zero : single a (0 : R) = 0 :=
  (single a).map_zero

/--
theorem `single_injective` / 定理 `single_injective`

English:
theorem single_injective
  given: (a : Γ)
  statement: Function.Injective (single a : R -> R⟦Γ⟧)
  proof: fun r s rs => by rw [← coeff_single_same a r, ← coeff_single_same a s, rs]

中文:
定理 single_injective
  条件: (a : Γ)
  结论: 函数.单射 (single a : R -> R⟦Γ⟧)
  证明: fun r s rs => by rw [← coeff_single_same a r, ← coeff_single_same a s, rs]

Depends on / 依赖: coeff_single_same
-/
theorem single_injective (a : Γ) : Function.Injective (single a : R -> R⟦Γ⟧) :=
  fun r s rs => by rw [← coeff_single_same a r, ← coeff_single_same a s, rs]

/--
theorem `single_ne_zero` / 定理 `single_ne_zero`

English:
theorem single_ne_zero
  given: (h : r != 0)
  statement: single a r != 0
  proof: fun con =>
  h (single_injective a (con.trans single_eq_zero.symm))

@[simp]

中文:
定理 single_ne_zero
  条件: (h : r != 0)
  结论: single a r != 0
  证明: fun con =>
  h (single_injective a (con.trans single_eq_zero.symm))

@[simp]
-/
theorem single_ne_zero (h : r != 0) : single a r != 0 := fun con =>
  h (single_injective a (con.trans single_eq_zero.symm))

@[simp]
/--
theorem `single_eq_zero_iff` / 定理 `single_eq_zero_iff`

English:
theorem single_eq_zero_iff
  given: {a : Γ} {r : R}
  statement: single a r = 0 ↔ r = 0
  proof: map_eq_zero_iff _ single_injective a

@[simp]

中文:
定理 single_eq_zero_iff
  条件: {a : Γ} {r : R}
  结论: single a r = 0 ↔ r = 0
  证明: map_eq_zero_iff _ single_injective a

@[simp]

Depends on / 依赖: map_eq_zero_iff, single_injective
-/
theorem single_eq_zero_iff {a : Γ} {r : R} : single a r = 0 ↔ r = 0 :=
map_eq_zero_iff _ single_injective a

@[simp]
/--
lemma `map_single` / 引理 `map_single`

English:
lemma map_single
  given: [Zero S] (f : ZeroHom R S)
  statement: (single a r).map f = single a (f r)
  proof: by
  ext g
  by_cases h : g = a <;> simp [h]

中文:
引理 map_single
  条件: [零 S] (f : 保零态射 R S)
  结论: (single a r).map f = single a (f r)
  证明: by
  ext g
  by_cases h : g = a <;> simp [h]
-/
protected lemma map_single [Zero S] (f : ZeroHom R S) : (single a r).map f = single a (f r) := by
  ext g
  by_cases h : g = a <;> simp [h]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: Γ] [Nontrivial R] : Nontrivial R⟦Γ⟧
  body: ⟨by
    obtain ⟨r, s, rs⟩ := exists_pair_ne R
    inhabit Γ
    refine ⟨single default r, single default s, fun con => rs ?_⟩
    rw [← coeff_single_same (default : Γ) r]; rw [con]; rw [coeff_single_same]⟩

中文:
实例 [非空
  签名: Γ] [非平凡 R] : 非平凡 R⟦Γ⟧
  定义体: ⟨by
    obtain ⟨r, s, rs⟩ := exists_pair_ne R
    inhabit Γ
    refine ⟨single default r, single default s, fun con => rs ?_⟩
    rw [← coeff_single_same (default : Γ) r]; rw [con]; rw [coeff_single_same]⟩

Depends on / 依赖: coeff_single_same, exists_pair_ne, inhabit, single
-/
instance [Nonempty Γ] [Nontrivial R] : Nontrivial R⟦Γ⟧ :=
  ⟨by
    obtain ⟨r, s, rs⟩ := exists_pair_ne R
    inhabit Γ
    refine ⟨single default r, single default s, fun con => rs ?_⟩
    rw [← coeff_single_same (default : Γ) r]; rw [con]; rw [coeff_single_same]⟩

section Order
variable {x : R⟦Γ⟧}

open scoped Classical in
/--
Definition of `orderTop` / `orderTop` 的定义

English:
definition orderTop
  signature: (x : R⟦Γ⟧)
  body: if h : x = 0 then ⊤ else x.isWF_support.min (support_nonempty_iff.2 h)

@[simp]

中文:
定义 orderTop
  签名: (x : R⟦Γ⟧)
  定义体: if h : x = 0 then ⊤ else x.isWF_support.min (support_nonempty_iff.2 h)

@[simp]

Depends on / 依赖: isWF_support, support_nonempty_iff, x.isWF_support.min
-/
def orderTop (x : R⟦Γ⟧) : WithTop Γ :=
  if h : x = 0 then ⊤ else x.isWF_support.min (support_nonempty_iff.2 h)

@[simp]
/--
theorem `orderTop_zero` / 定理 `orderTop_zero`

English:
theorem orderTop_zero
  statement: orderTop (0 : R⟦Γ⟧) = ⊤
  proof: dif_pos rfl

@[simp]

中文:
定理 orderTop_zero
  结论: orderTop (0 : R⟦Γ⟧) = ⊤
  证明: dif_pos rfl

@[simp]

Depends on / 依赖: dif_pos
-/
theorem orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤ :=
  dif_pos rfl

@[simp]
/--
theorem `orderTop_of_subsingleton` / 定理 `orderTop_of_subsingleton`

English:
theorem orderTop_of_subsingleton
  given: [Subsingleton R]
  statement: x.orderTop = ⊤
  proof: (Subsingleton.eq_zero x) ▸ orderTop_zero

中文:
定理 orderTop_of_subsingleton
  条件: [子单例 R]
  结论: x.orderTop = ⊤
  证明: (Subsingleton.eq_zero x) ▸ orderTop_zero

Depends on / 依赖: Subsingleton, Subsingleton.eq_zero, eq_zero, orderTop_zero
-/
theorem orderTop_of_subsingleton [Subsingleton R] : x.orderTop = ⊤ :=
  (Subsingleton.eq_zero x) ▸ orderTop_zero

/--
theorem `orderTop_of_ne_zero` / 定理 `orderTop_of_ne_zero`

English:
theorem orderTop_of_ne_zero
  given: (hx : x != 0)
  proof: dif_neg hx

中文:
定理 orderTop_of_ne_zero
  条件: (hx : x != 0)
  证明: dif_neg hx

Depends on / 依赖: dif_neg
-/
theorem orderTop_of_ne_zero (hx : x != 0) :
    orderTop x = x.isWF_support.min (support_nonempty_iff.2 hx) :=
  dif_neg hx

/--
lemma `orderTop_eq_top` / 引理 `orderTop_eq_top`

English:
lemma orderTop_eq_top
  statement: orderTop x = ⊤ ↔ x = 0
  proof: by simp [orderTop]

中文:
引理 orderTop_eq_top
  结论: orderTop x = ⊤ ↔ x = 0
  证明: by simp [orderTop]
-/
@[simp] lemma orderTop_eq_top : orderTop x = ⊤ ↔ x = 0 := by simp [orderTop]

/--
lemma `orderTop_lt_top` / 引理 `orderTop_lt_top`

English:
lemma orderTop_lt_top
  statement: orderTop x < ⊤ ↔ x != 0
  proof: by simp [lt_top_iff_ne_top]

中文:
引理 orderTop_lt_top
  结论: orderTop x < ⊤ ↔ x != 0
  证明: by simp [lt_top_iff_ne_top]
-/
@[simp] lemma orderTop_lt_top : orderTop x < ⊤ ↔ x != 0 := by simp [lt_top_iff_ne_top]

/--
lemma `orderTop_ne_top` / 引理 `orderTop_ne_top`

English:
lemma orderTop_ne_top
  statement: orderTop x != ⊤ ↔ x != 0
  proof: orderTop_eq_top.not

中文:
引理 orderTop_ne_top
  结论: orderTop x != ⊤ ↔ x != 0
  证明: orderTop_eq_top.not

Depends on / 依赖: Nat.rawCast, orderTop_eq_top, orderTop_eq_top.not, rawCast
-/
lemma orderTop_ne_top : orderTop x != ⊤ ↔ x != 0 := orderTop_eq_top.not

/--
theorem `orderTop_eq_of_le` / 定理 `orderTop_eq_of_le`

English:
theorem orderTop_eq_of_le
  statement: {x : R⟦Γ⟧} {g : Γ} (hg : g in x.support)
  proof: by
  rw [orderTop_of_ne_zero <| support_nonempty_iff.mp <| Set.nonempty_of_mem hg]; rw [x.isWF_support.min_eq_of_le hg hx]

中文:
定理 orderTop_eq_of_le
  结论: {x : R⟦Γ⟧} {g : Γ} (hg : g in x.support)
  证明: by
  rw [orderTop_of_ne_zero <| support_nonempty_iff.mp <| Set.nonempty_of_mem hg]; rw [x.isWF_support.min_eq_of_le hg hx]

Depends on / 依赖: Nat.rawCast, Set.nonempty_of_mem, isWF_support, min_eq_of_le, nonempty_of_mem, orderTop_of_ne_zero, rawCast, support_nonempty_iff, support_nonempty_iff.mp, x.isWF_support.min_eq_of_le
-/
theorem orderTop_eq_of_le {x : R⟦Γ⟧} {g : Γ} (hg : g in x.support)
    (hx : forall g' in x.support, g <= g') : orderTop x = g := by
  rw [orderTop_of_ne_zero <| support_nonempty_iff.mp <| Set.nonempty_of_mem hg]; rw [x.isWF_support.min_eq_of_le hg hx]

/--
theorem `untop_orderTop_of_ne_zero` / 定理 `untop_orderTop_of_ne_zero`

English:
theorem untop_orderTop_of_ne_zero
  given: {x : R⟦Γ⟧} (hx : x != 0)
  proof: WithTop.coe_inj.mp ((WithTop.coe_untop (orderTop x) (orderTop_ne_top.2 hx)).trans
    (orderTop_of_ne_zero hx))

中文:
定理 untop_orderTop_of_ne_zero
  条件: {x : R⟦Γ⟧} (hx : x != 0)
  证明: WithTop.coe_inj.mp ((WithTop.coe_untop (orderTop x) (orderTop_ne_top.2 hx)).trans
    (orderTop_of_ne_zero hx))

Depends on / 依赖: WithTop, WithTop.coe_inj.mp, WithTop.coe_untop, coe_inj, coe_untop, orderTop, orderTop_ne_top, orderTop_of_ne_zero
-/
theorem untop_orderTop_of_ne_zero {x : R⟦Γ⟧} (hx : x != 0) :
    WithTop.untop x.orderTop (orderTop_ne_top.2 hx) =
      x.isWF_support.min (support_nonempty_iff.2 hx) :=
  WithTop.coe_inj.mp ((WithTop.coe_untop (orderTop x) (orderTop_ne_top.2 hx)).trans
    (orderTop_of_ne_zero hx))

/--
theorem `coeff_orderTop_ne` / 定理 `coeff_orderTop_ne`

English:
theorem coeff_orderTop_ne
  given: {x : R⟦Γ⟧} {g : Γ} (hg : x.orderTop = g)
  proof: by
  have h : orderTop x != ⊤ := by simp_all only [ne_eq, WithTop.coe_ne_top, not_false_eq_true]
  have hx : x != 0 := orderTop_ne_top.1 h
  rw [orderTop_of_ne_zero hx]; rw [WithTop.coe_eq_coe] at hg
  rw [← hg]
  exact x.isWF_support.min_mem (support_nonempty_iff.2 hx)

中文:
定理 coeff_orderTop_ne
  条件: {x : R⟦Γ⟧} {g : Γ} (hg : x.orderTop = g)
  证明: by
  have h : orderTop x != ⊤ := by simp_all only [ne_eq, WithTop.coe_ne_top, not_false_eq_true]
  have hx : x != 0 := orderTop_ne_top.1 h
  rw [orderTop_of_ne_zero hx]; rw [WithTop.coe_eq_coe] at hg
  rw [← hg]
  exact x.isWF_support.min_mem (support_nonempty_iff.2 hx)

Depends on / 依赖: WithTop, WithTop.coe_eq_coe, WithTop.coe_ne_top, coe_eq_coe, coe_ne_top, isWF_support, min_mem, ne_eq, not_false_eq_true, orderTop, orderTop_ne_top, orderTop_of_ne_zero, support_nonempty_iff, x.isWF_support.min_mem
-/
theorem coeff_orderTop_ne {x : R⟦Γ⟧} {g : Γ} (hg : x.orderTop = g) :
    x.coeff g != 0 := by
  have h : orderTop x != ⊤ := by simp_all only [ne_eq, WithTop.coe_ne_top, not_false_eq_true]
  have hx : x != 0 := orderTop_ne_top.1 h
  rw [orderTop_of_ne_zero hx]; rw [WithTop.coe_eq_coe] at hg
  rw [← hg]
  exact x.isWF_support.min_mem (support_nonempty_iff.2 hx)

/--
theorem `orderTop_ne_of_coeff_eq_zero` / 定理 `orderTop_ne_of_coeff_eq_zero`

English:
theorem orderTop_ne_of_coeff_eq_zero
  given: {x : R⟦Γ⟧} {i : Γ} (hx : x.coeff i = 0)
  proof: fun h => coeff_orderTop_ne h hx

中文:
定理 orderTop_ne_of_coeff_eq_zero
  条件: {x : R⟦Γ⟧} {i : Γ} (hx : x.coeff i = 0)
  证明: fun h => coeff_orderTop_ne h hx

Depends on / 依赖: coeff_orderTop_ne
-/
theorem orderTop_ne_of_coeff_eq_zero {x : R⟦Γ⟧} {i : Γ} (hx : x.coeff i = 0) :
    x.orderTop != i :=
  fun h => coeff_orderTop_ne h hx

/--
theorem `orderTop_le_of_coeff_ne_zero` / 定理 `orderTop_le_of_coeff_ne_zero`

English:
theorem orderTop_le_of_coeff_ne_zero
  statement: {Γ} [LinearOrder Γ] {x : R⟦Γ⟧}
  proof: by
  rw [orderTop_of_ne_zero (ne_zero_of_coeff_ne_zero h)]; rw [WithTop.coe_le_coe]
  exact Set.IsWF.min_le _ _ ((mem_support _ _).2 h)

@[simp]

中文:
定理 orderTop_le_of_coeff_ne_zero
  结论: {Γ} [线性序 Γ] {x : R⟦Γ⟧}
  证明: by
  rw [orderTop_of_ne_zero (ne_zero_of_coeff_ne_zero h)]; rw [WithTop.coe_le_coe]
  exact Set.IsWF.min_le _ _ ((mem_support _ _).2 h)

@[simp]

Depends on / 依赖: Set.IsWF.min_le, WithTop, WithTop.coe_le_coe, coe_le_coe, mem_support, min_le, ne_zero_of_coeff_ne_zero, orderTop_of_ne_zero
-/
theorem orderTop_le_of_coeff_ne_zero {Γ} [LinearOrder Γ] {x : R⟦Γ⟧}
    {g : Γ} (h : x.coeff g != 0) : x.orderTop <= g := by
  rw [orderTop_of_ne_zero (ne_zero_of_coeff_ne_zero h)]; rw [WithTop.coe_le_coe]
  exact Set.IsWF.min_le _ _ ((mem_support _ _).2 h)

@[simp]
/--
theorem `orderTop_single` / 定理 `orderTop_single`

English:
theorem orderTop_single
  given: (h : r != 0)
  statement: (single a r).orderTop = a
  proof: (orderTop_of_ne_zero (single_ne_zero h)).trans
    (WithTop.coe_inj.mpr (support_single_subset
      ((single a r).isWF_support.min_mem (support_nonempty_iff.2 (single_ne_zero h)))))

中文:
定理 orderTop_single
  条件: (h : r != 0)
  结论: (single a r).orderTop = a
  证明: (orderTop_of_ne_zero (single_ne_zero h)).trans
    (WithTop.coe_inj.mpr (support_single_subset
      ((single a r).isWF_support.min_mem (support_nonempty_iff.2 (single_ne_zero h)))))

Depends on / 依赖: WithTop, WithTop.coe_inj.mpr, coe_inj, isWF_support, isWF_support.min_mem, min_mem, orderTop_of_ne_zero, single, single_ne_zero, support_nonempty_iff, support_single_subset
-/
theorem orderTop_single (h : r != 0) : (single a r).orderTop = a :=
  (orderTop_of_ne_zero (single_ne_zero h)).trans
    (WithTop.coe_inj.mpr (support_single_subset
      ((single a r).isWF_support.min_mem (support_nonempty_iff.2 (single_ne_zero h)))))

/--
theorem `orderTop_single_le` / 定理 `orderTop_single_le`

English:
theorem orderTop_single_le
  statement: a <= (single a r).orderTop
  proof: by
  by_cases hr : r = 0
  · simp only [hr, map_zero, orderTop_zero, le_top]
  · rw [orderTop_single hr]

中文:
定理 orderTop_single_le
  结论: a <= (single a r).orderTop
  证明: by
  by_cases hr : r = 0
  · simp only [hr, map_zero, orderTop_zero, le_top]
  · rw [orderTop_single hr]

Depends on / 依赖: le_top, map_zero, orderTop_single, orderTop_zero
-/
theorem orderTop_single_le : a <= (single a r).orderTop := by
  by_cases hr : r = 0
  · simp only [hr, map_zero, orderTop_zero, le_top]
  · rw [orderTop_single hr]

/--
theorem `lt_orderTop_single` / 定理 `lt_orderTop_single`

English:
theorem lt_orderTop_single
  given: {g g' : Γ} (hgg' : g < g')
  statement: g < (single g' r).orderTop
  proof: lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hgg') orderTop_single_le

中文:
定理 lt_orderTop_single
  条件: {g g' : Γ} (hgg' : g < g')
  结论: g < (single g' r).orderTop
  证明: lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hgg') orderTop_single_le

Depends on / 依赖: WithTop, WithTop.coe_lt_coe.mpr, coe_lt_coe, lt_of_lt_of_le, orderTop_single_le
-/
theorem lt_orderTop_single {g g' : Γ} (hgg' : g < g') : g < (single g' r).orderTop :=
  lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hgg') orderTop_single_le

/--
theorem `coeff_eq_zero_of_lt_orderTop` / 定理 `coeff_eq_zero_of_lt_orderTop`

English:
theorem coeff_eq_zero_of_lt_orderTop
  given: {x : R⟦Γ⟧} {i : Γ} (hi : i < x.orderTop)
  proof: by
  rcases eq_or_ne x 0 with (rfl | hx)
  · exact coeff_zero
  contrapose! hi
  rw [← mem_support] at hi
  rw [orderTop_of_ne_zero hx]; rw [WithTop.coe_lt_coe]
  exact Set.IsWF.not_lt_min _ _ hi

中文:
定理 coeff_eq_zero_of_lt_orderTop
  条件: {x : R⟦Γ⟧} {i : Γ} (hi : i < x.orderTop)
  证明: by
  rcases eq_or_ne x 0 with (rfl | hx)
  · exact coeff_zero
  contrapose! hi
  rw [← mem_support] at hi
  rw [orderTop_of_ne_zero hx]; rw [WithTop.coe_lt_coe]
  exact Set.IsWF.not_lt_min _ _ hi

Depends on / 依赖: Set.IsWF.not_lt_min, WithTop, WithTop.coe_lt_coe, coe_lt_coe, coeff_zero, contrapose, eq_or_ne, mem_support, not_lt_min, orderTop_of_ne_zero
-/
theorem coeff_eq_zero_of_lt_orderTop {x : R⟦Γ⟧} {i : Γ} (hi : i < x.orderTop) :
    x.coeff i = 0 := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · exact coeff_zero
  contrapose! hi
  rw [← mem_support] at hi
  rw [orderTop_of_ne_zero hx]; rw [WithTop.coe_lt_coe]
  exact Set.IsWF.not_lt_min _ _ hi

/--
Definition of `leadingCoeff` / `leadingCoeff` 的定义

English:
definition leadingCoeff
  signature: (x : R⟦Γ⟧)
  body: x.orderTop.recTopCoe 0 x.coeff

@[simp]

中文:
定义 leadingCoeff
  签名: (x : R⟦Γ⟧)
  定义体: x.orderTop.recTopCoe 0 x.coeff

@[simp]

Depends on / 依赖: orderTop, recTopCoe, x.coeff, x.orderTop.recTopCoe
-/
def leadingCoeff (x : R⟦Γ⟧) : R := x.orderTop.recTopCoe 0 x.coeff

@[simp]
/--
theorem `leadingCoeff_zero` / 定理 `leadingCoeff_zero`

English:
theorem leadingCoeff_zero
  statement: leadingCoeff (0 : R⟦Γ⟧) = 0
  proof: by simp [leadingCoeff]

中文:
定理 leadingCoeff_zero
  结论: leadingCoeff (0 : R⟦Γ⟧) = 0
  证明: by simp [leadingCoeff]

Depends on / 依赖: leadingCoeff
-/
theorem leadingCoeff_zero : leadingCoeff (0 : R⟦Γ⟧) = 0 := by simp [leadingCoeff]

/--
theorem `leadingCoeff_of_ne_zero` / 定理 `leadingCoeff_of_ne_zero`

English:
theorem leadingCoeff_of_ne_zero
  given: {x : R⟦Γ⟧} (hx : x != 0)
  proof: by
  simp [leadingCoeff, orderTop, hx]

@[simp]

中文:
定理 leadingCoeff_of_ne_zero
  条件: {x : R⟦Γ⟧} (hx : x != 0)
  证明: by
  simp [leadingCoeff, orderTop, hx]

@[simp]

Depends on / 依赖: leadingCoeff, orderTop
-/
theorem leadingCoeff_of_ne_zero {x : R⟦Γ⟧} (hx : x != 0) :
    x.leadingCoeff = x.coeff (x.orderTop.untop <| orderTop_ne_top.2 hx) := by
  simp [leadingCoeff, orderTop, hx]

@[simp]
/--
theorem `leadingCoeff_eq_zero` / 定理 `leadingCoeff_eq_zero`

English:
theorem leadingCoeff_eq_zero
  given: {x : R⟦Γ⟧}
  statement: x.leadingCoeff = 0 ↔ x = 0
  proof: by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [leadingCoeff_of_ne_zero, coeff_orderTop_ne, *]

中文:
定理 leadingCoeff_eq_zero
  条件: {x : R⟦Γ⟧}
  结论: x.leadingCoeff = 0 ↔ x = 0
  证明: by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [leadingCoeff_of_ne_zero, coeff_orderTop_ne, *]

Depends on / 依赖: coeff_orderTop_ne, eq_or_ne, leadingCoeff_of_ne_zero
-/
theorem leadingCoeff_eq_zero {x : R⟦Γ⟧} : x.leadingCoeff = 0 ↔ x = 0 := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [leadingCoeff_of_ne_zero, coeff_orderTop_ne, *]

/--
theorem `leadingCoeff_ne_zero` / 定理 `leadingCoeff_ne_zero`

English:
theorem leadingCoeff_ne_zero
  given: {x : R⟦Γ⟧}
  statement: x.leadingCoeff != 0 ↔ x != 0
  proof: leadingCoeff_eq_zero.not

@[simp]

中文:
定理 leadingCoeff_ne_zero
  条件: {x : R⟦Γ⟧}
  结论: x.leadingCoeff != 0 ↔ x != 0
  证明: leadingCoeff_eq_zero.not

@[simp]

Depends on / 依赖: leadingCoeff_eq_zero, leadingCoeff_eq_zero.not
-/
theorem leadingCoeff_ne_zero {x : R⟦Γ⟧} : x.leadingCoeff != 0 ↔ x != 0 :=
  leadingCoeff_eq_zero.not

@[simp]
/--
theorem `leadingCoeff_of_single` / 定理 `leadingCoeff_of_single`

English:
theorem leadingCoeff_of_single
  given: {a : Γ} {r : R}
  statement: leadingCoeff (single a r) = r
  proof: by
  by_cases h : r = 0 <;> simp [leadingCoeff, h]

中文:
定理 leadingCoeff_of_single
  条件: {a : Γ} {r : R}
  结论: leadingCoeff (single a r) = r
  证明: by
  by_cases h : r = 0 <;> simp [leadingCoeff, h]

Depends on / 依赖: leadingCoeff
-/
theorem leadingCoeff_of_single {a : Γ} {r : R} : leadingCoeff (single a r) = r := by
  by_cases h : r = 0 <;> simp [leadingCoeff, h]

/--
theorem `coeff_untop_eq_leadingCoeff` / 定理 `coeff_untop_eq_leadingCoeff`

English:
theorem coeff_untop_eq_leadingCoeff
  given: {x : R⟦Γ⟧} (hx)
  proof: by
  rw [orderTop_ne_top] at hx
  rw [leadingCoeff_of_ne_zero hx]; rw [(WithTop.untop_eq_iff _).mpr (orderTop_of_ne_zero hx)]

中文:
定理 coeff_untop_eq_leadingCoeff
  条件: {x : R⟦Γ⟧} (hx)
  证明: by
  rw [orderTop_ne_top] at hx
  rw [leadingCoeff_of_ne_zero hx]; rw [(WithTop.untop_eq_iff _).mpr (orderTop_of_ne_zero hx)]

Depends on / 依赖: WithTop, WithTop.untop_eq_iff, leadingCoeff_of_ne_zero, orderTop_ne_top, orderTop_of_ne_zero, untop_eq_iff
-/
theorem coeff_untop_eq_leadingCoeff {x : R⟦Γ⟧} (hx) :
    x.coeff (x.orderTop.untop hx) = x.leadingCoeff := by
  rw [orderTop_ne_top] at hx
  rw [leadingCoeff_of_ne_zero hx]; rw [(WithTop.untop_eq_iff _).mpr (orderTop_of_ne_zero hx)]

variable [Zero Γ]

open scoped Classical in
/--
Definition of `order` / `order` 的定义

English:
definition order
  signature: (x : R⟦Γ⟧)
  body: if h : x = 0 then 0 else x.isWF_support.min (support_nonempty_iff.2 h)

@[simp]

中文:
定义 order
  签名: (x : R⟦Γ⟧)
  定义体: if h : x = 0 then 0 else x.isWF_support.min (support_nonempty_iff.2 h)

@[simp]

Depends on / 依赖: isWF_support, support_nonempty_iff, x.isWF_support.min
-/
def order (x : R⟦Γ⟧) : Γ :=
  if h : x = 0 then 0 else x.isWF_support.min (support_nonempty_iff.2 h)

@[simp]
/--
theorem `order_zero` / 定理 `order_zero`

English:
theorem order_zero
  statement: order (0 : R⟦Γ⟧) = 0
  proof: dif_pos rfl

中文:
定理 order_zero
  结论: order (0 : R⟦Γ⟧) = 0
  证明: dif_pos rfl

Depends on / 依赖: dif_pos
-/
theorem order_zero : order (0 : R⟦Γ⟧) = 0 :=
  dif_pos rfl

/--
theorem `order_of_ne` / 定理 `order_of_ne`

English:
theorem order_of_ne
  given: {x : R⟦Γ⟧} (hx : x != 0)
  proof: dif_neg hx

中文:
定理 order_of_ne
  条件: {x : R⟦Γ⟧} (hx : x != 0)
  证明: dif_neg hx

Depends on / 依赖: dif_neg
-/
theorem order_of_ne {x : R⟦Γ⟧} (hx : x != 0) :
    order x = x.isWF_support.min (support_nonempty_iff.2 hx) :=
  dif_neg hx

/--
theorem `order_eq_orderTop_of_ne_zero` / 定理 `order_eq_orderTop_of_ne_zero`

English:
theorem order_eq_orderTop_of_ne_zero
  given: (hx : x != 0)
  statement: order x = orderTop x
  proof: by
  rw [order_of_ne hx]; rw [orderTop_of_ne_zero hx]

@[simp]

中文:
定理 order_eq_orderTop_of_ne_zero
  条件: (hx : x != 0)
  结论: order x = orderTop x
  证明: by
  rw [order_of_ne hx]; rw [orderTop_of_ne_zero hx]

@[simp]

Depends on / 依赖: orderTop_of_ne_zero, order_of_ne
-/
theorem order_eq_orderTop_of_ne_zero (hx : x != 0) : order x = orderTop x := by
  rw [order_of_ne hx]; rw [orderTop_of_ne_zero hx]

@[simp]
/--
theorem `coeff_order_eq_zero` / 定理 `coeff_order_eq_zero`

English:
theorem coeff_order_eq_zero
  given: {x : R⟦Γ⟧}
  statement: x.coeff x.order = 0 ↔ x = 0
  proof: by
  refine ⟨not_imp_not.1 fun hx => ?_, by simp +contextual⟩
  rw [order_of_ne hx]
  exact x.isWF_support.min_mem (support_nonempty_iff.2 hx)

中文:
定理 coeff_order_eq_zero
  条件: {x : R⟦Γ⟧}
  结论: x.coeff x.order = 0 ↔ x = 0
  证明: by
  refine ⟨not_imp_not.1 fun hx => ?_, by simp +contextual⟩
  rw [order_of_ne hx]
  exact x.isWF_support.min_mem (support_nonempty_iff.2 hx)

Depends on / 依赖: contextual, isWF_support, min_mem, not_imp_not, order_of_ne, support_nonempty_iff, x.isWF_support.min_mem
-/
theorem coeff_order_eq_zero {x : R⟦Γ⟧} : x.coeff x.order = 0 ↔ x = 0 := by
  refine ⟨not_imp_not.1 fun hx => ?_, by simp +contextual⟩
  rw [order_of_ne hx]
  exact x.isWF_support.min_mem (support_nonempty_iff.2 hx)

/--
theorem `order_le_of_coeff_ne_zero` / 定理 `order_le_of_coeff_ne_zero`

English:
theorem order_le_of_coeff_ne_zero
  statement: {Γ} [Zero Γ] [LinearOrder Γ] {x : R⟦Γ⟧}
  proof: le_trans (le_of_eq (order_of_ne (ne_zero_of_coeff_ne_zero h)))
    (Set.IsWF.min_le _ _ ((mem_support _ _).2 h))

@[simp]

中文:
定理 order_le_of_coeff_ne_zero
  结论: {Γ} [零 Γ] [线性序 Γ] {x : R⟦Γ⟧}
  证明: le_trans (le_of_eq (order_of_ne (ne_zero_of_coeff_ne_zero h)))
    (Set.IsWF.min_le _ _ ((mem_support _ _).2 h))

@[simp]

Depends on / 依赖: Set.IsWF.min_le, le_of_eq, le_trans, mem_support, min_le, ne_zero_of_coeff_ne_zero, order_of_ne
-/
theorem order_le_of_coeff_ne_zero {Γ} [Zero Γ] [LinearOrder Γ] {x : R⟦Γ⟧}
    {g : Γ} (h : x.coeff g != 0) : x.order <= g :=
  le_trans (le_of_eq (order_of_ne (ne_zero_of_coeff_ne_zero h)))
    (Set.IsWF.min_le _ _ ((mem_support _ _).2 h))

@[simp]
/--
theorem `order_single` / 定理 `order_single`

English:
theorem order_single
  given: (h : r != 0)
  statement: (single a r).order = a
  proof: (order_of_ne (single_ne_zero h)).trans
    (support_single_subset
      ((single a r).isWF_support.min_mem (support_nonempty_iff.2 (single_ne_zero h))))

中文:
定理 order_single
  条件: (h : r != 0)
  结论: (single a r).order = a
  证明: (order_of_ne (single_ne_zero h)).trans
    (support_single_subset
      ((single a r).isWF_support.min_mem (support_nonempty_iff.2 (single_ne_zero h))))

Depends on / 依赖: isWF_support, isWF_support.min_mem, min_mem, order_of_ne, single, single_ne_zero, support_nonempty_iff, support_single_subset
-/
theorem order_single (h : r != 0) : (single a r).order = a :=
  (order_of_ne (single_ne_zero h)).trans
    (support_single_subset
      ((single a r).isWF_support.min_mem (support_nonempty_iff.2 (single_ne_zero h))))

/--
theorem `coeff_eq_zero_of_lt_order` / 定理 `coeff_eq_zero_of_lt_order`

English:
theorem coeff_eq_zero_of_lt_order
  given: {x : R⟦Γ⟧} {i : Γ} (hi : i < x.order)
  statement: x.coeff i = 0
  proof: by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  contrapose! hi
  rw [← mem_support] at hi
  rw [order_of_ne hx]
  exact Set.IsWF.not_lt_min _ _ hi

中文:
定理 coeff_eq_zero_of_lt_order
  条件: {x : R⟦Γ⟧} {i : Γ} (hi : i < x.order)
  结论: x.coeff i = 0
  证明: by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  contrapose! hi
  rw [← mem_support] at hi
  rw [order_of_ne hx]
  exact Set.IsWF.not_lt_min _ _ hi

Depends on / 依赖: Set.IsWF.not_lt_min, contrapose, eq_or_ne, mem_support, not_lt_min, order_of_ne
-/
theorem coeff_eq_zero_of_lt_order {x : R⟦Γ⟧} {i : Γ} (hi : i < x.order) : x.coeff i = 0 := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  contrapose! hi
  rw [← mem_support] at hi
  rw [order_of_ne hx]
  exact Set.IsWF.not_lt_min _ _ hi

/--
theorem `zero_lt_orderTop_iff` / 定理 `zero_lt_orderTop_iff`

English:
theorem zero_lt_orderTop_iff
  given: {x : R⟦Γ⟧} (hx : x != 0)
  proof: by
  simp_all [orderTop_of_ne_zero hx, order_of_ne hx]

中文:
定理 zero_lt_orderTop_iff
  条件: {x : R⟦Γ⟧} (hx : x != 0)
  证明: by
  simp_all [orderTop_of_ne_zero hx, order_of_ne hx]

Depends on / 依赖: orderTop_of_ne_zero, order_of_ne
-/
theorem zero_lt_orderTop_iff {x : R⟦Γ⟧} (hx : x != 0) :
    0 < x.orderTop ↔ 0 < x.order := by
  simp_all [orderTop_of_ne_zero hx, order_of_ne hx]

/--
theorem `zero_lt_orderTop_of_order` / 定理 `zero_lt_orderTop_of_order`

English:
theorem zero_lt_orderTop_of_order
  given: {x : R⟦Γ⟧} (hx : 0 < x.order)
  statement: 0 < x.orderTop
  proof: by
  by_cases h : x = 0
  · simp_all only [order_zero, lt_self_iff_false]
  · exact (zero_lt_orderTop_iff h).mpr hx

中文:
定理 zero_lt_orderTop_of_order
  条件: {x : R⟦Γ⟧} (hx : 0 < x.order)
  结论: 0 < x.orderTop
  证明: by
  by_cases h : x = 0
  · simp_all only [order_zero, lt_self_iff_false]
  · exact (zero_lt_orderTop_iff h).mpr hx

Depends on / 依赖: lt_self_iff_false, order_zero, zero_lt_orderTop_iff
-/
theorem zero_lt_orderTop_of_order {x : R⟦Γ⟧} (hx : 0 < x.order) : 0 < x.orderTop := by
  by_cases h : x = 0
  · simp_all only [order_zero, lt_self_iff_false]
  · exact (zero_lt_orderTop_iff h).mpr hx

/--
theorem `zero_le_orderTop_iff` / 定理 `zero_le_orderTop_iff`

English:
theorem zero_le_orderTop_iff
  given: {x : R⟦Γ⟧}
  statement: 0 <= x.orderTop ↔ 0 <= x.order
  proof: by
  by_cases h : x = 0
  · simp_all
  · simp_all [order_of_ne h, orderTop_of_ne_zero h]

中文:
定理 zero_le_orderTop_iff
  条件: {x : R⟦Γ⟧}
  结论: 0 <= x.orderTop ↔ 0 <= x.order
  证明: by
  by_cases h : x = 0
  · simp_all
  · simp_all [order_of_ne h, orderTop_of_ne_zero h]

Depends on / 依赖: orderTop_of_ne_zero, order_of_ne
-/
theorem zero_le_orderTop_iff {x : R⟦Γ⟧} : 0 <= x.orderTop ↔ 0 <= x.order := by
  by_cases h : x = 0
  · simp_all
  · simp_all [order_of_ne h, orderTop_of_ne_zero h]

/--
theorem `leadingCoeff_eq` / 定理 `leadingCoeff_eq`

English:
theorem leadingCoeff_eq
  given: {x : R⟦Γ⟧}
  statement: x.leadingCoeff = x.coeff x.order
  proof: by
  by_cases h : x = 0
  · rw [h, leadingCoeff_zero, coeff_zero]
  · simp [leadingCoeff_of_ne_zero, orderTop_of_ne_zero, order_of_ne, h]

中文:
定理 leadingCoeff_eq
  条件: {x : R⟦Γ⟧}
  结论: x.leadingCoeff = x.coeff x.order
  证明: by
  by_cases h : x = 0
  · rw [h, leadingCoeff_zero, coeff_zero]
  · simp [leadingCoeff_of_ne_zero, orderTop_of_ne_zero, order_of_ne, h]

Depends on / 依赖: coeff_zero, leadingCoeff_of_ne_zero, leadingCoeff_zero, orderTop_of_ne_zero, order_of_ne
-/
theorem leadingCoeff_eq {x : R⟦Γ⟧} : x.leadingCoeff = x.coeff x.order := by
  by_cases h : x = 0
  · rw [h, leadingCoeff_zero, coeff_zero]
  · simp [leadingCoeff_of_ne_zero, orderTop_of_ne_zero, order_of_ne, h]

end Order

section Finsupp

/--
Definition of `ofFinsupp` / `ofFinsupp` 的定义

English:
definition ofFinsupp
  signature: : ZeroHom (Γ ->₀ R) R⟦Γ⟧ where
  body: { coeff := f, isPWO_support' := f.hasFiniteSupport.isPWO }
  map_zero' := by simp

@[simp]

中文:
定义 ofFinsupp
  签名: : 保零态射 (Γ ->₀ R) R⟦Γ⟧ where
  定义体: { coeff := f, isPWO_support' := f.hasFiniteSupport.isPWO }
  map_zero' := by simp

@[simp]

Depends on / 依赖: f.hasFiniteSupport.isPWO, hasFiniteSupport, isPWO_support
-/
def ofFinsupp : ZeroHom (Γ ->₀ R) R⟦Γ⟧ where
  toFun f := { coeff := f, isPWO_support' := f.hasFiniteSupport.isPWO }
  map_zero' := by simp

@[simp]
/--
theorem `coeff_ofFinsupp` / 定理 `coeff_ofFinsupp`

English:
theorem coeff_ofFinsupp
  given: (f : Γ ->₀ R) (a : Γ)
  statement: (ofFinsupp f).coeff a = f a
  proof: rfl

中文:
定理 coeff_ofFinsupp
  条件: (f : Γ ->₀ R) (a : Γ)
  结论: (ofFinsupp f).coeff a = f a
  证明: rfl
-/
theorem coeff_ofFinsupp (f : Γ ->₀ R) (a : Γ) : (ofFinsupp f).coeff a = f a := rfl

end Finsupp

section Domain

variable [PartialOrder Γ']

open scoped Classical in
/--
Definition of `embDomain` / `embDomain` 的定义

English:
definition embDomain
  signature: (f : Γ ↪o Γ')
  body: fun x =>
  { coeff := fun b : Γ' => if h : b in f '' x.support then x.coeff (Classical.choose h) else 0
    isPWO_support' :=
      (x.isPWO_support.image_of_monotone f.monotone).mono fun b hb => by
        contrapose hb
        rw [Function.mem_support]; rw [dif_neg hb]; rw [Classical.not_not] }

@

中文:
定义 embDomain
  签名: (f : Γ ↪o Γ')
  定义体: fun x =>
  { coeff := fun b : Γ' => if h : b in f '' x.support then x.coeff (Classical.choose h) else 0
    isPWO_support' :=
      (x.isPWO_support.image_of_monotone f.monotone).mono fun b hb => by
        contrapose hb
        rw [Function.mem_support]; rw [dif_neg hb]; rw [Classical.not_not] }

@
-/
def embDomain (f : Γ ↪o Γ') : R⟦Γ⟧ -> R⟦Γ'⟧ := fun x =>
  { coeff := fun b : Γ' => if h : b in f '' x.support then x.coeff (Classical.choose h) else 0
    isPWO_support' :=
      (x.isPWO_support.image_of_monotone f.monotone).mono fun b hb => by
        contrapose hb
        rw [Function.mem_support]; rw [dif_neg hb]; rw [Classical.not_not] }

@[simp]
/--
theorem `embDomain_coeff` / 定理 `embDomain_coeff`

English:
theorem embDomain_coeff
  given: {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {a : Γ}
  proof: by
  rw [embDomain]
  dsimp only
  by_cases ha : a in x.support
  · rw [dif_pos (Set.mem_image_of_mem f ha)]
    exact congr rfl (f.injective (Classical.choose_spec (Set.mem_image_of_mem f ha)).2)
  · rw [dif_neg, Classical.not_not.1 fun c => ha ((mem_support _ _).2 c)]
    contrapose ha
    obtain 

中文:
定理 embDomain_coeff
  条件: {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {a : Γ}
  证明: by
  rw [embDomain]
  dsimp only
  by_cases ha : a in x.support
  · rw [dif_pos (Set.mem_image_of_mem f ha)]
    exact congr rfl (f.injective (Classical.choose_spec (Set.mem_image_of_mem f ha)).2)
  · rw [dif_neg, Classical.not_not.1 fun c => ha ((mem_support _ _).2 c)]
    contrapose ha
    obtain 

Depends on / 依赖: Classical, Classical.choose_spec, Classical.not_not, Set.mem_image, Set.mem_image_of_mem, choose_spec, contrapose, dif_neg, dif_pos, embDomain, f.injective, injective, mem_image, mem_image_of_mem, mem_support, not_not, support, x.support
-/
theorem embDomain_coeff {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {a : Γ} :
    (embDomain f x).coeff (f a) = x.coeff a := by
  rw [embDomain]
  dsimp only
  by_cases ha : a in x.support
  · rw [dif_pos (Set.mem_image_of_mem f ha)]
    exact congr rfl (f.injective (Classical.choose_spec (Set.mem_image_of_mem f ha)).2)
  · rw [dif_neg, Classical.not_not.1 fun c => ha ((mem_support _ _).2 c)]
    contrapose ha
    obtain ⟨b, hb1, hb2⟩ := (Set.mem_image _ _ _).1 ha
    rwa [f.injective hb2] at hb1

@[simp]
/--
theorem `embDomain_mk_coeff` / 定理 `embDomain_mk_coeff`

English:
theorem embDomain_mk_coeff
  statement: {f : Γ -> Γ'} (hfi : Function.Injective f)
  proof: embDomain_coeff

中文:
定理 embDomain_mk_coeff
  结论: {f : Γ -> Γ'} (hfi : 函数.单射 f)
  证明: embDomain_coeff

Depends on / 依赖: embDomain_coeff
-/
theorem embDomain_mk_coeff {f : Γ -> Γ'} (hfi : Function.Injective f)
    (hf : forall g g' : Γ, f g <= f g' ↔ g <= g') {x : R⟦Γ⟧} {a : Γ} :
    (embDomain ⟨⟨f, hfi⟩, hf _ _⟩ x).coeff (f a) = x.coeff a :=
  embDomain_coeff

/--
theorem `embDomain_notin_image_support` / 定理 `embDomain_notin_image_support`

English:
theorem embDomain_notin_image_support
  statement: {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'}
  proof: dif_neg hb

中文:
定理 embDomain_notin_image_support
  结论: {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'}
  证明: dif_neg hb

Depends on / 依赖: dif_neg
-/
theorem embDomain_notin_image_support {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'}
    (hb : b ∉ f '' x.support) : (embDomain f x).coeff b = 0 :=
  dif_neg hb

/--
theorem `support_embDomain_subset` / 定理 `support_embDomain_subset`

English:
theorem support_embDomain_subset
  given: {f : Γ ↪o Γ'} {x : R⟦Γ⟧}
  proof: by
  intro g hg
  contrapose hg
  rw [mem_support]; rw [embDomain_notin_image_support hg]; rw [Classical.not_not]

中文:
定理 support_embDomain_subset
  条件: {f : Γ ↪o Γ'} {x : R⟦Γ⟧}
  证明: by
  intro g hg
  contrapose hg
  rw [mem_support]; rw [embDomain_notin_image_support hg]; rw [Classical.not_not]

Depends on / 依赖: Classical, Classical.not_not, contrapose, embDomain_notin_image_support, mem_support, not_not
-/
theorem support_embDomain_subset {f : Γ ↪o Γ'} {x : R⟦Γ⟧} :
    support (embDomain f x) subseteq f '' x.support := by
  intro g hg
  contrapose hg
  rw [mem_support]; rw [embDomain_notin_image_support hg]; rw [Classical.not_not]

/--
theorem `embDomain_of_notMem_range` / 定理 `embDomain_of_notMem_range`

English:
theorem embDomain_of_notMem_range
  given: {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ Set.range f)
  proof: embDomain_notin_image_support fun con => hb (Set.image_subset_range _ _ con)

@[deprecated (since := "2026-07-15")] alias embDomain_notin_range := embDomain_of_notMem_range

@[simp]

中文:
定理 embDomain_of_notMem_range
  条件: {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ 集合.range f)
  证明: embDomain_notin_image_support fun con => hb (Set.image_subset_range _ _ con)

@[deprecated (since := "2026-07-15")] alias embDomain_notin_range := embDomain_of_notMem_range

@[simp]

Depends on / 依赖: Set.image_subset_range, embDomain_notin_image_support, image_subset_range
-/
theorem embDomain_of_notMem_range {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ Set.range f) :
    (embDomain f x).coeff b = 0 :=
  embDomain_notin_image_support fun con => hb (Set.image_subset_range _ _ con)

@[deprecated (since := "2026-07-15")] alias embDomain_notin_range := embDomain_of_notMem_range

@[simp]
/--
theorem `embDomain_zero` / 定理 `embDomain_zero`

English:
theorem embDomain_zero
  given: {f : Γ ↪o Γ'}
  statement: embDomain f (0 : R⟦Γ⟧) = 0
  proof: by
  ext
  simp [embDomain_notin_image_support]

@[simp]

中文:
定理 embDomain_zero
  条件: {f : Γ ↪o Γ'}
  结论: embDomain f (0 : R⟦Γ⟧) = 0
  证明: by
  ext
  simp [embDomain_notin_image_support]

@[simp]

Depends on / 依赖: embDomain_notin_image_support
-/
theorem embDomain_zero {f : Γ ↪o Γ'} : embDomain f (0 : R⟦Γ⟧) = 0 := by
  ext
  simp [embDomain_notin_image_support]

@[simp]
/--
theorem `embDomain_single` / 定理 `embDomain_single`

English:
theorem embDomain_single
  given: {f : Γ ↪o Γ'} {g : Γ} {r : R}
  proof: by
  ext g'
  by_cases h : g' = f g
  · simp [h]
  rw [embDomain_notin_image_support]; rw [coeff_single_of_ne h]
  by_cases hr : r = 0
  · simp [hr]
  rwa [support_single_of_ne hr, Set.image_singleton, Set.mem_singleton_iff]

中文:
定理 embDomain_single
  条件: {f : Γ ↪o Γ'} {g : Γ} {r : R}
  证明: by
  ext g'
  by_cases h : g' = f g
  · simp [h]
  rw [embDomain_notin_image_support]; rw [coeff_single_of_ne h]
  by_cases hr : r = 0
  · simp [hr]
  rwa [support_single_of_ne hr, Set.image_singleton, Set.mem_singleton_iff]

Depends on / 依赖: Set.image_singleton, Set.mem_singleton_iff, coeff_single_of_ne, embDomain_notin_image_support, image_singleton, mem_singleton_iff, support_single_of_ne
-/
theorem embDomain_single {f : Γ ↪o Γ'} {g : Γ} {r : R} :
    embDomain f (single g r) = single (f g) r := by
  ext g'
  by_cases h : g' = f g
  · simp [h]
  rw [embDomain_notin_image_support]; rw [coeff_single_of_ne h]
  by_cases hr : r = 0
  · simp [hr]
  rwa [support_single_of_ne hr, Set.image_singleton, Set.mem_singleton_iff]

/--
theorem `embDomain_injective` / 定理 `embDomain_injective`

English:
theorem embDomain_injective
  given: {f : Γ ↪o Γ'}
  proof: fun x y xy => by
  ext g
  rw [HahnSeries.ext_iff]; rw [funext_iff] at xy
  have xyg := xy (f g)
  rwa [embDomain_coeff, embDomain_coeff] at xyg

@[simp]

中文:
定理 embDomain_injective
  条件: {f : Γ ↪o Γ'}
  证明: fun x y xy => by
  ext g
  rw [HahnSeries.ext_iff]; rw [funext_iff] at xy
  have xyg := xy (f g)
  rwa [embDomain_coeff, embDomain_coeff] at xyg

@[simp]

Depends on / 依赖: HahnSeries, HahnSeries.ext_iff, embDomain_coeff, ext_iff, funext_iff
-/
theorem embDomain_injective {f : Γ ↪o Γ'} :
    Function.Injective (embDomain f : R⟦Γ⟧ -> R⟦Γ'⟧) := fun x y xy => by
  ext g
  rw [HahnSeries.ext_iff]; rw [funext_iff] at xy
  have xyg := xy (f g)
  rwa [embDomain_coeff, embDomain_coeff] at xyg

@[simp]
/--
theorem `orderTop_embDomain` / 定理 `orderTop_embDomain`

English:
theorem orderTop_embDomain
  given: {Γ : Type*} [LinearOrder Γ] {f : Γ ↪o Γ'} {x : R⟦Γ⟧}
  proof: by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  rw [← WithTop.coe_untop x.orderTop (by simpa using hx)]; rw [WithTop.map_coe]
  apply orderTop_eq_of_le
  · simpa using coeff_orderTop_ne (by simp)
  intro y hy
  obtain ⟨z, hz, rfl⟩ :=
(Set.mem_image _ _ _).mp Set.mem_of_subset_of_mem support_embDomai

中文:
定理 orderTop_embDomain
  条件: {Γ : 类型} [线性序 Γ] {f : Γ ↪o Γ'} {x : R⟦Γ⟧}
  证明: by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  rw [← WithTop.coe_untop x.orderTop (by simpa using hx)]; rw [WithTop.map_coe]
  apply orderTop_eq_of_le
  · simpa using coeff_orderTop_ne (by simp)
  intro y hy
  obtain ⟨z, hz, rfl⟩ :=
(Set.mem_image _ _ _).mp Set.mem_of_subset_of_mem support_embDomai

Depends on / 依赖: OrderEmbedding, OrderEmbedding.le_iff_le, Set.mem_image, Set.mem_of_subset_of_mem, WithTop, WithTop.coe_untop, WithTop.map_coe, WithTop.untop_le_iff, coe_untop, coeff_orderTop_ne, eq_or_ne, le_iff_le, map_coe, mem_image, mem_of_subset_of_mem, orderTop, orderTop_eq_of_le, orderTop_le_of_coeff_ne_zero, support_embDomain_subset, untop_le_iff
-/
theorem orderTop_embDomain {Γ : Type*} [LinearOrder Γ] {f : Γ ↪o Γ'} {x : R⟦Γ⟧} :
    (embDomain f x).orderTop = WithTop.map f x.orderTop := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  rw [← WithTop.coe_untop x.orderTop (by simpa using hx)]; rw [WithTop.map_coe]
  apply orderTop_eq_of_le
  · simpa using coeff_orderTop_ne (by simp)
  intro y hy
  obtain ⟨z, hz, rfl⟩ :=
(Set.mem_image _ _ _).mp Set.mem_of_subset_of_mem support_embDomain_subset hy
  rw [OrderEmbedding.le_iff_le]; rw [WithTop.untop_le_iff]
  apply orderTop_le_of_coeff_ne_zero
  simpa using hz

end Domain

end Zero

section LinearOrder

variable [Zero R] [LinearOrder Γ]

@[deprecated "directly use n as a lower bound." (since := "2026-01-02")]
/--
theorem `forallLTEqZero_supp_BddBelow` / 定理 `forallLTEqZero_supp_BddBelow`

English:
theorem forallLTEqZero_supp_BddBelow
  given: (f : Γ -> R) (n : Γ) (hn : forall (m : Γ), m < n -> f m = 0)
  proof: by
  refine ⟨n, fun _ => ?_⟩
  contrapose
  simp_all

@[deprecated bddBelow_empty (since := "2026-01-02")]

中文:
定理 对任意LTEqZero_supp_BddBelow
  条件: (f : Γ -> R) (n : Γ) (hn : 对任意 (m : Γ), m < n -> f m = 0)
  证明: by
  refine ⟨n, fun _ => ?_⟩
  contrapose
  simp_all

@[deprecated bddBelow_empty (since := "2026-01-02")]

Depends on / 依赖: contrapose
-/
theorem forallLTEqZero_supp_BddBelow (f : Γ -> R) (n : Γ) (hn : forall (m : Γ), m < n -> f m = 0) :
    BddBelow (Function.support f) := by
  refine ⟨n, fun _ => ?_⟩
  contrapose
  simp_all

@[deprecated bddBelow_empty (since := "2026-01-02")]
/--
theorem `BddBelow_zero` / 定理 `BddBelow_zero`

English:
theorem BddBelow_zero
  given: [Nonempty Γ]
  statement: BddBelow (Function.support (0 : Γ -> R))
  proof: by
  simp

中文:
定理 BddBelow_zero
  条件: [非空 Γ]
  结论: BddBelow (函数.support (0 : Γ -> R))
  证明: by
  simp
-/
theorem BddBelow_zero [Nonempty Γ] : BddBelow (Function.support (0 : Γ -> R)) := by
  simp

/--
theorem `le_orderTop_iff_forall` / 定理 `le_orderTop_iff_forall`

English:
theorem le_orderTop_iff_forall
  given: {x : R⟦Γ⟧} {i : WithTop Γ}
  proof: coeff_eq_zero_of_lt_orderTop (hj.trans_le hi)
  mpr H := by
    obtain rfl | h := eq_or_ne x 0
    · simp
    · by_contra! hi
      exact x.isWF_support.min_mem (support_nonempty_iff.2 h) (H _ (orderTop_of_ne_zero h ▸ hi))

中文:
定理 le_orderTop_iff_对任意
  条件: {x : R⟦Γ⟧} {i : WithTop Γ}
  证明: coeff_eq_zero_of_lt_orderTop (hj.trans_le hi)
  mpr H := by
    obtain rfl | h := eq_or_ne x 0
    · simp
    · by_contra! hi
      exact x.isWF_support.min_mem (support_nonempty_iff.2 h) (H _ (orderTop_of_ne_zero h ▸ hi))

Depends on / 依赖: coeff_eq_zero_of_lt_orderTop, hj.trans_le, trans_le
-/
theorem le_orderTop_iff_forall {x : R⟦Γ⟧} {i : WithTop Γ} :
    i <= x.orderTop ↔ forall j : Γ, j < i -> x.coeff j = 0 where
  mp hi j hj := coeff_eq_zero_of_lt_orderTop (hj.trans_le hi)
  mpr H := by
    obtain rfl | h := eq_or_ne x 0
    · simp
    · by_contra! hi
      exact x.isWF_support.min_mem (support_nonempty_iff.2 h) (H _ (orderTop_of_ne_zero h ▸ hi))

/--
theorem `orderTop_lt_iff_exists` / 定理 `orderTop_lt_iff_exists`

English:
theorem orderTop_lt_iff_exists
  given: {x : R⟦Γ⟧} {i : WithTop Γ}
  proof: by
  rw [← not_le]; rw [le_orderTop_iff_forall]
  simp

中文:
定理 orderTop_lt_iff_存在
  条件: {x : R⟦Γ⟧} {i : WithTop Γ}
  证明: by
  rw [← not_le]; rw [le_orderTop_iff_forall]
  simp

Depends on / 依赖: le_orderTop_iff_forall, not_le
-/
theorem orderTop_lt_iff_exists {x : R⟦Γ⟧} {i : WithTop Γ} :
    x.orderTop < i ↔ exists j : Γ, j < i ∧ x.coeff j != 0 := by
  rw [← not_le]; rw [le_orderTop_iff_forall]
  simp

/--
theorem `le_order_iff_forall` / 定理 `le_order_iff_forall`

English:
theorem le_order_iff_forall
  given: [Zero Γ] {x : R⟦Γ⟧} {i : Γ} (h : x != 0)
  proof: coeff_eq_zero_of_lt_order (hj.trans_le hi)
  mpr H := by
    contrapose! h
    have := H _ h
    rwa [coeff_order_eq_zero] at this

中文:
定理 le_order_iff_对任意
  条件: [零 Γ] {x : R⟦Γ⟧} {i : Γ} (h : x != 0)
  证明: coeff_eq_zero_of_lt_order (hj.trans_le hi)
  mpr H := by
    contrapose! h
    have := H _ h
    rwa [coeff_order_eq_zero] at this

Depends on / 依赖: coeff_eq_zero_of_lt_order, hj.trans_le, trans_le
-/
theorem le_order_iff_forall [Zero Γ] {x : R⟦Γ⟧} {i : Γ} (h : x != 0) :
    i <= x.order ↔ forall j < i, x.coeff j = 0 where
  mp hi j hj := coeff_eq_zero_of_lt_order (hj.trans_le hi)
  mpr H := by
    contrapose! h
    have := H _ h
    rwa [coeff_order_eq_zero] at this

/--
theorem `order_lt_iff_exists` / 定理 `order_lt_iff_exists`

English:
theorem order_lt_iff_exists
  given: [Zero Γ] {x : R⟦Γ⟧} {i : Γ} (h : x != 0)
  proof: by
  rw [← not_le]; rw [le_order_iff_forall h]
  simp

中文:
定理 order_lt_iff_存在
  条件: [零 Γ] {x : R⟦Γ⟧} {i : Γ} (h : x != 0)
  证明: by
  rw [← not_le]; rw [le_order_iff_forall h]
  simp

Depends on / 依赖: le_order_iff_forall, not_le
-/
theorem order_lt_iff_exists [Zero Γ] {x : R⟦Γ⟧} {i : Γ} (h : x != 0) :
    x.order < i ↔ exists j < i, x.coeff j != 0 := by
  rw [← not_le]; rw [le_order_iff_forall h]
  simp

variable [LocallyFiniteOrder Γ]

@[deprecated BddBelow.isWF (since := "2026-01-02")]
/--
theorem `suppBddBelow_supp_PWO` / 定理 `suppBddBelow_supp_PWO`

English:
theorem suppBddBelow_supp_PWO
  given: (f : Γ -> R) (hf : BddBelow (Function.support f))
  proof: hf.isWF.isPWO

中文:
定理 suppBddBelow_supp_PWO
  条件: (f : Γ -> R) (hf : BddBelow (函数.support f))
  证明: hf.isWF.isPWO

Depends on / 依赖: hf.isWF.isPWO
-/
theorem suppBddBelow_supp_PWO (f : Γ -> R) (hf : BddBelow (Function.support f)) :
    (Function.support f).IsPWO :=
  hf.isWF.isPWO

/-- Construct a Hahn series from any function whose support is bounded below. -/
@[simps]
/--
Definition of `ofSuppBddBelow` / `ofSuppBddBelow` 的定义

English:
definition ofSuppBddBelow
  signature: (f : Γ -> R) (hf : BddBelow (Function.support f))
  body: ⟨f, hf.isWF.isPWO⟩

@[simp]

中文:
定义 ofSuppBddBelow
  签名: (f : Γ -> R) (hf : BddBelow (函数.support f))
  定义体: ⟨f, hf.isWF.isPWO⟩

@[simp]

Depends on / 依赖: hf.isWF.isPWO
-/
def ofSuppBddBelow (f : Γ -> R) (hf : BddBelow (Function.support f)) : R⟦Γ⟧ :=
  ⟨f, hf.isWF.isPWO⟩

@[simp]
/--
theorem `ofSuppBddBelow_zero` / 定理 `ofSuppBddBelow_zero`

English:
theorem ofSuppBddBelow_zero
  given: [Nonempty Γ]
  statement: ofSuppBddBelow 0 (by simp) = (0 : R⟦Γ⟧)
  proof: rfl

@[deprecated (since := "2026-01-02")]
alias zero_ofSuppBddBelow := ofSuppBddBelow_zero

@[simp]

中文:
定理 ofSuppBddBelow_zero
  条件: [非空 Γ]
  结论: ofSuppBddBelow 0 (by simp) = (0 : R⟦Γ⟧)
  证明: rfl

@[deprecated (since := "2026-01-02")]
alias zero_ofSuppBddBelow := ofSuppBddBelow_zero

@[simp]
-/
theorem ofSuppBddBelow_zero [Nonempty Γ] : ofSuppBddBelow 0 (by simp) = (0 : R⟦Γ⟧) :=
  rfl

@[deprecated (since := "2026-01-02")]
alias zero_ofSuppBddBelow := ofSuppBddBelow_zero

@[simp]
/--
theorem `ofSuppBddBelow_eq_zero` / 定理 `ofSuppBddBelow_eq_zero`

English:
theorem ofSuppBddBelow_eq_zero
  given: {f : Γ -> R} {hf}
  statement: ofSuppBddBelow f hf = 0 ↔ f = 0
  proof: HahnSeries.ext_iff

@[simp]

中文:
定理 ofSuppBddBelow_eq_zero
  条件: {f : Γ -> R} {hf}
  结论: ofSuppBddBelow f hf = 0 ↔ f = 0
  证明: HahnSeries.ext_iff

@[simp]

Depends on / 依赖: HahnSeries, HahnSeries.ext_iff, ext_iff
-/
theorem ofSuppBddBelow_eq_zero {f : Γ -> R} {hf} : ofSuppBddBelow f hf = 0 ↔ f = 0 :=
  HahnSeries.ext_iff

@[simp]
/--
theorem `coeff_ofSuppBddBelow` / 定理 `coeff_ofSuppBddBelow`

English:
theorem coeff_ofSuppBddBelow
  given: {f : Γ -> R} {hf}
  statement: (ofSuppBddBelow f hf).coeff = f
  proof: rfl

@[deprecated le_order_iff_forall (since := "2026-01-02")]

中文:
定理 coeff_ofSuppBddBelow
  条件: {f : Γ -> R} {hf}
  结论: (ofSuppBddBelow f hf).coeff = f
  证明: rfl

@[deprecated le_order_iff_forall (since := "2026-01-02")]
-/
theorem coeff_ofSuppBddBelow {f : Γ -> R} {hf} : (ofSuppBddBelow f hf).coeff = f :=
  rfl

@[deprecated le_order_iff_forall (since := "2026-01-02")]
/--
theorem `order_ofForallLtEqZero` / 定理 `order_ofForallLtEqZero`

English:
theorem order_ofForallLtEqZero
  statement: [Zero Γ] (f : Γ -> R) (hf : f != 0) (n : Γ)
  proof: by
  rw [le_order_iff_forall]
  · exact hn
  · simpa

中文:
定理 order_ofForallLtEqZero
  结论: [零 Γ] (f : Γ -> R) (hf : f != 0) (n : Γ)
  证明: by
  rw [le_order_iff_forall]
  · exact hn
  · simpa

Depends on / 依赖: le_order_iff_forall
-/
theorem order_ofForallLtEqZero [Zero Γ] (f : Γ -> R) (hf : f != 0) (n : Γ)
    (hn : forall (m : Γ), m < n -> f m = 0) :
    n <= order (ofSuppBddBelow f (forallLTEqZero_supp_BddBelow f n hn)) := by
  rw [le_order_iff_forall]
  · exact hn
  · simpa

end LinearOrder

section Truncate
variable [Zero R]

/--
Definition of `truncLT` / `truncLT` 的定义

English:
definition truncLT
  signature: [PartialOrder Γ] [DecidableLT Γ] (c : Γ)
  body: { coeff i := if i < c then x.coeff i else 0
      isPWO_support' := Set.IsPWO.mono x.isPWO_support (by simp) }
  map_zero' := by ext; simp

中文:
定义 truncLT
  签名: [偏序 Γ] [DecidableLT Γ] (c : Γ)
  定义体: { coeff i := if i < c then x.coeff i else 0
      isPWO_support' := Set.IsPWO.mono x.isPWO_support (by simp) }
  map_zero' := by ext; simp

Depends on / 依赖: Set.IsPWO.mono, isPWO_support, map_zero, x.coeff, x.isPWO_support
-/
def truncLT [PartialOrder Γ] [DecidableLT Γ] (c : Γ) : ZeroHom R⟦Γ⟧ R⟦Γ⟧ where
  toFun x :=
    { coeff i := if i < c then x.coeff i else 0
      isPWO_support' := Set.IsPWO.mono x.isPWO_support (by simp) }
  map_zero' := by ext; simp

/--
theorem `support_truncLT` / 定理 `support_truncLT`

English:
theorem support_truncLT
  given: [PartialOrder Γ] [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧)
  proof: by
  simp [truncLT, Function.support, and_comm]

中文:
定理 support_truncLT
  条件: [偏序 Γ] [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧)
  证明: by
  simp [truncLT, Function.support, and_comm]

Depends on / 依赖: Function, Function.support, and_comm, support, truncLT
-/
theorem support_truncLT [PartialOrder Γ] [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧) :
    (truncLT c x).support = {y in x.support | y < c} := by
  simp [truncLT, Function.support, and_comm]

/--
theorem `support_truncLT_subset` / 定理 `support_truncLT_subset`

English:
theorem support_truncLT_subset
  given: [PartialOrder Γ] [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧)
  proof: by
  rw [support_truncLT]
  exact Set.sep_subset ..

@[simp]

中文:
定理 support_truncLT_subset
  条件: [偏序 Γ] [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧)
  证明: by
  rw [support_truncLT]
  exact Set.sep_subset ..

@[simp]

Depends on / 依赖: Set.sep_subset, sep_subset, support_truncLT
-/
theorem support_truncLT_subset [PartialOrder Γ] [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧) :
    (truncLT c x).support subseteq x.support := by
  rw [support_truncLT]
  exact Set.sep_subset ..

@[simp]
/--
theorem `coeff_truncLT` / 定理 `coeff_truncLT`

English:
theorem coeff_truncLT
  given: [PartialOrder Γ] [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧) (i : Γ)
  proof: rfl

中文:
定理 coeff_truncLT
  条件: [偏序 Γ] [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧) (i : Γ)
  证明: rfl
-/
protected theorem coeff_truncLT [PartialOrder Γ] [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧) (i : Γ) :
    (truncLT c x).coeff i = if i < c then x.coeff i else 0 := rfl

/--
theorem `coeff_truncLT_of_lt` / 定理 `coeff_truncLT_of_lt`

English:
theorem coeff_truncLT_of_lt
  given: [PartialOrder Γ] [DecidableLT Γ] {c i : Γ} (h : i < c) (x : R⟦Γ⟧)
  proof: by
  simp [h]

中文:
定理 coeff_truncLT_of_lt
  条件: [偏序 Γ] [DecidableLT Γ] {c i : Γ} (h : i < c) (x : R⟦Γ⟧)
  证明: by
  simp [h]
-/
theorem coeff_truncLT_of_lt [PartialOrder Γ] [DecidableLT Γ] {c i : Γ} (h : i < c) (x : R⟦Γ⟧) :
    (truncLT c x).coeff i = x.coeff i := by
  simp [h]

/--
theorem `coeff_truncLT_of_le` / 定理 `coeff_truncLT_of_le`

English:
theorem coeff_truncLT_of_le
  given: [LinearOrder Γ] {c i : Γ} (h : c <= i) (x : R⟦Γ⟧)
  proof: by
  simp [h]

中文:
定理 coeff_truncLT_of_le
  条件: [线性序 Γ] {c i : Γ} (h : c <= i) (x : R⟦Γ⟧)
  证明: by
  simp [h]
-/
theorem coeff_truncLT_of_le [LinearOrder Γ] {c i : Γ} (h : c <= i) (x : R⟦Γ⟧) :
    (truncLT c x).coeff i = 0 := by
  simp [h]

end Truncate

end HahnSeries
