/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.Archimedean
public import Mathlib.Algebra.Ring.Subring.Order
public import Mathlib.Order.Quotient
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.Algebra.Order.Archimedean.Real.Hom

/-!
# Standard part function

Given a finite element in a non-archimedean field, the standard part function rounds it to the
unique closest real number. That is, it chops off any infinitesimals.

Let `K` be a linearly ordered field. The subset of finite elements (i.e. those bounded by a natural
number) is a `ValuationSubring`, which means we can construct its residue field
`FiniteResidueField`, roughly corresponding to the finite elements quotiented by infinitesimals.
This field inherits a `LinearOrder` instance, which makes it into an Archimedean linearly ordered
field, meaning we can uniquely embed it in the reals.

Given a finite element of the field, the `ArchimedeanClass.stdPart` function returns the real number
corresponding to this unique embedding. This function generalizes, among other things, the standard
part function on `Hyperreal`.

## References

* https://en.wikipedia.org/wiki/Standard_part_function
-/

@[expose] public noncomputable section

namespace ArchimedeanClass
variable
  {K : Type*} [LinearOrder K] [Field K] [IsOrderedRing K] {x y : K}
  {R : Type*} [LinearOrder R] [CommRing R] [IsStrictOrderedRing R] [Archimedean R]

/-! ### Finite residue field -/

variable (K) in
/--
Definition of `FiniteElement` / `FiniteElement` 的定义

English:
definition FiniteElement
  signature: : Type _
  body: (addValuation K).toValuation.valuationSubring
deriving CommRing, IsDomain, ValuationRing, LinearOrder, IsStrictOrderedRing

中文:
定义 FiniteElement
  签名: : 类型 _
  定义体: (addValuation K).toValuation.valuationSubring
deriving CommRing, IsDomain, ValuationRing, LinearOrder, IsStrictOrderedRing

Depends on / 依赖: addValuation, toValuation, toValuation.valuationSubring, valuationSubring
-/
def FiniteElement : Type _ :=
  (addValuation K).toValuation.valuationSubring
deriving CommRing, IsDomain, ValuationRing, LinearOrder, IsStrictOrderedRing

namespace FiniteElement

/--
theorem `val_zero` / 定理 `val_zero`

English:
theorem val_zero
  statement: (0 : FiniteElement K).1 = 0
  proof: rfl

中文:
定理 val_zero
  结论: (0 : FiniteElement K).1 = 0
  证明: rfl
-/
@[simp] theorem val_zero : (0 : FiniteElement K).1 = 0 := rfl
/--
theorem `val_one` / 定理 `val_one`

English:
theorem val_one
  statement: (1 : FiniteElement K).1 = 1
  proof: rfl

中文:
定理 val_one
  结论: (1 : FiniteElement K).1 = 1
  证明: rfl
-/
@[simp] theorem val_one : (1 : FiniteElement K).1 = 1 := rfl
/--
theorem `val_add` / 定理 `val_add`

English:
theorem val_add
  given: (x y : FiniteElement K)
  statement: (x + y).1 = x.1 + y.1
  proof: rfl

中文:
定理 val_add
  条件: (x y : FiniteElement K)
  结论: (x + y).1 = x.1 + y.1
  证明: rfl
-/
@[simp] theorem val_add (x y : FiniteElement K) : (x + y).1 = x.1 + y.1 := rfl
/--
theorem `val_sub` / 定理 `val_sub`

English:
theorem val_sub
  given: (x y : FiniteElement K)
  statement: (x - y).1 = x.1 - y.1
  proof: rfl

中文:
定理 val_sub
  条件: (x y : FiniteElement K)
  结论: (x - y).1 = x.1 - y.1
  证明: rfl
-/
@[simp] theorem val_sub (x y : FiniteElement K) : (x - y).1 = x.1 - y.1 := rfl
/--
theorem `val_mul` / 定理 `val_mul`

English:
theorem val_mul
  given: (x y : FiniteElement K)
  statement: (x * y).1 = x.1 * y.1
  proof: rfl

中文:
定理 val_mul
  条件: (x y : FiniteElement K)
  结论: (x * y).1 = x.1 * y.1
  证明: rfl
-/
@[simp] theorem val_mul (x y : FiniteElement K) : (x * y).1 = x.1 * y.1 := rfl

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {x y : FiniteElement K} (h : x.1 = y.1)
  statement: x = y
  proof: Subtype.ext h

中文:
定理 ext
  条件: {x y : FiniteElement K} (h : x.1 = y.1)
  结论: x = y
  证明: Subtype.ext h
-/
@[ext] theorem ext {x y : FiniteElement K} (h : x.1 = y.1) : x = y := Subtype.ext h

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (x : K) (h : 0 <= mk x)
  body: ⟨x, h⟩

中文:
定义 mk
  签名: (x : K) (h : 0 <= mk x)
  定义体: ⟨x, h⟩
-/
protected def mk (x : K) (h : 0 <= mk x) : FiniteElement K := ⟨x, h⟩

/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  statement: FiniteElement.mk (0 : K) (by simp) = 0
  proof: rfl

中文:
定理 mk_zero
  结论: FiniteElement.mk (0 : K) (by simp) = 0
  证明: rfl
-/
@[simp] theorem mk_zero : FiniteElement.mk (0 : K) (by simp) = 0 := rfl
/--
theorem `mk_one` / 定理 `mk_one`

English:
theorem mk_one
  statement: FiniteElement.mk (1 : K) (by simp) = 1
  proof: rfl

中文:
定理 mk_one
  结论: FiniteElement.mk (1 : K) (by simp) = 1
  证明: rfl
-/
@[simp] theorem mk_one : FiniteElement.mk (1 : K) (by simp) = 1 := rfl
/--
theorem `mk_natCast` / 定理 `mk_natCast`

English:
theorem mk_natCast
  given: (n : Nat)
  statement: FiniteElement.mk (n : K) (mk_natCast_nonneg n) = n
  proof: rfl

中文:
定理 mk_natCast
  条件: (n : 自然数)
  结论: FiniteElement.mk (n : K) (mk_natCast_nonneg n) = n
  证明: rfl
-/
@[simp] theorem mk_natCast (n : Nat) : FiniteElement.mk (n : K) (mk_natCast_nonneg n) = n := rfl
/--
theorem `mk_intCast` / 定理 `mk_intCast`

English:
theorem mk_intCast
  given: (n : Int)
  statement: FiniteElement.mk (n : K) (mk_intCast_nonneg n) = n
  proof: rfl

@[simp]

中文:
定理 mk_intCast
  条件: (n : 整数)
  结论: FiniteElement.mk (n : K) (mk_intCast_nonneg n) = n
  证明: rfl

@[simp]
-/
@[simp] theorem mk_intCast (n : Int) : FiniteElement.mk (n : K) (mk_intCast_nonneg n) = n := rfl

@[simp]
/--
theorem `neg_mk` / 定理 `neg_mk`

English:
theorem neg_mk
  given: {x : K} (h : 0 <= mk x)
  proof: rfl

@[simp]

中文:
定理 neg_mk
  条件: {x : K} (h : 0 <= mk x)
  证明: rfl

@[simp]
-/
theorem neg_mk {x : K} (h : 0 <= mk x) :
    -FiniteElement.mk x h = FiniteElement.mk (-x) (by rwa [mk_neg]) :=
  rfl

@[simp]
/--
theorem `mk_add_mk` / 定理 `mk_add_mk`

English:
theorem mk_add_mk
  given: (x y : K) (hx hy)
  proof: rfl

@[simp]

中文:
定理 mk_add_mk
  条件: (x y : K) (hx hy)
  证明: rfl

@[simp]
-/
theorem mk_add_mk (x y : K) (hx hy) :
    .mk x hx + .mk y hy = FiniteElement.mk (x + y) ((le_min hx hy).trans <| min_le_mk_add ..) :=
  rfl

@[simp]
/--
theorem `mk_sub_mk` / 定理 `mk_sub_mk`

English:
theorem mk_sub_mk
  given: (x y : K) (hx hy)
  proof: rfl

@[simp]

中文:
定理 mk_sub_mk
  条件: (x y : K) (hx hy)
  证明: rfl

@[simp]
-/
theorem mk_sub_mk (x y : K) (hx hy) :
    .mk x hx - .mk y hy = FiniteElement.mk (x - y) ((le_min hx hy).trans <| min_le_mk_sub ..) :=
  rfl

@[simp]
/--
theorem `mk_mul_mk` / 定理 `mk_mul_mk`

English:
theorem mk_mul_mk
  given: (x y : K) (hx hy)
  proof: rfl

@[simp]

中文:
定理 mk_mul_mk
  条件: (x y : K) (hx hy)
  证明: rfl

@[simp]
-/
theorem mk_mul_mk (x y : K) (hx hy) :
    .mk x hx * .mk y hy = FiniteElement.mk (x * y) (add_nonneg hx hy) :=
  rfl

@[simp]
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: (x y : K) (hx hy)
  statement: FiniteElement.mk x hx <= .mk y hy ↔ x <= y
  proof: .rfl

@[simp]

中文:
定理 mk_le_mk
  条件: (x y : K) (hx hy)
  结论: FiniteElement.mk x hx <= .mk y hy ↔ x <= y
  证明: .rfl

@[simp]
-/
theorem mk_le_mk (x y : K) (hx hy) : FiniteElement.mk x hx <= .mk y hy ↔ x <= y :=
  .rfl

@[simp]
/--
theorem `mk_lt_mk` / 定理 `mk_lt_mk`

English:
theorem mk_lt_mk
  given: (x y : K) (hx hy)
  statement: FiniteElement.mk x hx < .mk y hy ↔ x < y
  proof: .rfl

中文:
定理 mk_lt_mk
  条件: (x y : K) (hx hy)
  结论: FiniteElement.mk x hx < .mk y hy ↔ x < y
  证明: .rfl
-/
theorem mk_lt_mk (x y : K) (hx hy) : FiniteElement.mk x hx < .mk y hy ↔ x < y :=
  .rfl

/--
theorem `not_isUnit_iff_mk_pos` / 定理 `not_isUnit_iff_mk_pos`

English:
theorem not_isUnit_iff_mk_pos
  given: {x : FiniteElement K}
  statement: ¬ IsUnit x ↔ 0 < mk x.1
  proof: Valuation.Integer.not_isUnit_iff_valuation_lt_one

中文:
定理 not_isUnit_iff_mk_pos
  条件: {x : FiniteElement K}
  结论: ¬ 是单位 x ↔ 0 < mk x.1
  证明: Valuation.Integer.not_isUnit_iff_valuation_lt_one

Depends on / 依赖: Integer, Valuation, Valuation.Integer.not_isUnit_iff_valuation_lt_one, not_isUnit_iff_valuation_lt_one
-/
theorem not_isUnit_iff_mk_pos {x : FiniteElement K} : ¬ IsUnit x ↔ 0 < mk x.1 :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one

/--
theorem `isUnit_iff_mk_eq_zero` / 定理 `isUnit_iff_mk_eq_zero`

English:
theorem isUnit_iff_mk_eq_zero
  given: {x : FiniteElement K}
  statement: IsUnit x ↔ mk x.1 = 0
  proof: by
  rw [← not_iff_not]; rw [not_isUnit_iff_mk_pos]; rw [lt_iff_not_ge]; rw [x.2.ge_iff_eq']

中文:
定理 isUnit_iff_mk_eq_zero
  条件: {x : FiniteElement K}
  结论: 是单位 x ↔ mk x.1 = 0
  证明: by
  rw [← not_iff_not]; rw [not_isUnit_iff_mk_pos]; rw [lt_iff_not_ge]; rw [x.2.ge_iff_eq']

Depends on / 依赖: ge_iff_eq, lt_iff_not_ge, not_iff_not, not_isUnit_iff_mk_pos
-/
theorem isUnit_iff_mk_eq_zero {x : FiniteElement K} : IsUnit x ↔ mk x.1 = 0 := by
  rw [← not_iff_not]; rw [not_isUnit_iff_mk_pos]; rw [lt_iff_not_ge]; rw [x.2.ge_iff_eq']

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RatCast (FiniteElement K)
  body: .mk q (mk_ratCast_nonneg q)

中文:
实例 :
  签名: 有理数嵌入 (FiniteElement K)
  定义体: .mk q (mk_ratCast_nonneg q)

Depends on / 依赖: mk_ratCast_nonneg
-/
instance : RatCast (FiniteElement K) where
  ratCast q := .mk q (mk_ratCast_nonneg q)

/--
theorem `mk_ratCast` / 定理 `mk_ratCast`

English:
theorem mk_ratCast
  given: (q : Rat)
  statement: FiniteElement.mk (q : K) (mk_ratCast_nonneg q) = q
  proof: rfl

@[no_expose]

中文:
定理 mk_ratCast
  条件: (q : 有理数)
  结论: FiniteElement.mk (q : K) (mk_ratCast_nonneg q) = q
  证明: rfl

@[no_expose]
-/
@[simp] theorem mk_ratCast (q : Rat) : FiniteElement.mk (q : K) (mk_ratCast_nonneg q) = q := rfl

@[no_expose]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FloorRing (FiniteElement K)
  body: .ofBounded _ fun x => by
    obtain ⟨n, hn⟩ := x.2
    refine ⟨n, (le_abs_self x).trans ?_⟩
    simpa using! hn

中文:
实例 :
  签名: Floor环 (FiniteElement K)
  定义体: .ofBounded _ fun x => by
    obtain ⟨n, hn⟩ := x.2
    refine ⟨n, (le_abs_self x).trans ?_⟩
    simpa using! hn

Depends on / 依赖: le_abs_self, ofBounded
-/
instance : FloorRing (FiniteElement K) :=
  .ofBounded _ fun x => by
    obtain ⟨n, hn⟩ := x.2
    refine ⟨n, (le_abs_self x).trans ?_⟩
    simpa using! hn

end FiniteElement

set_option backward.isDefEq.respectTransparency.types false in
variable (K) in
/--
Definition of `FiniteResidueField` / `FiniteResidueField` 的定义

English:
definition FiniteResidueField
  signature: : Type _
  body: IsLocalRing.ResidueField (FiniteElement K)
deriving Field

中文:
定义 FiniteResidueField
  签名: : 类型 _
  定义体: IsLocalRing.ResidueField (FiniteElement K)
deriving Field

Depends on / 依赖: FiniteElement, IsLocalRing, IsLocalRing.ResidueField, ResidueField
-/
def FiniteResidueField : Type _ :=
  IsLocalRing.ResidueField (FiniteElement K)
deriving Field

namespace FiniteResidueField

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `ordConnected_preimage_mk'` / 实例 `ordConnected_preimage_mk'`

English:
instance ordConnected_preimage_mk'
  signature: : forall x, Set.OrdConnected Quotient.mk
  body: by
  refine fun x => ⟨?_⟩
  rintro x rfl y hy z ⟨hxz, hzy⟩
  have := hxz.trans hzy
  rw [Set.mem_preimage]; rw [Set.mem_singleton_iff]; rw [Quotient.eq]; rw [Submodule.quotientRel_def]; rw [IsLocalRing.mem_maximalIdeal]; rw [mem_nonunits_iff]; rw [FiniteElement.not_isUnit_iff_mk_pos] at hy ⊢
  apply

中文:
实例 ordConnected_preimage_mk'
  签名: : 对任意 x, 集合.序连通 商.mk
  定义体: by
  refine fun x => ⟨?_⟩
  rintro x rfl y hy z ⟨hxz, hzy⟩
  have := hxz.trans hzy
  rw [Set.mem_preimage]; rw [Set.mem_singleton_iff]; rw [Quotient.eq]; rw [Submodule.quotientRel_def]; rw [IsLocalRing.mem_maximalIdeal]; rw [mem_nonunits_iff]; rw [FiniteElement.not_isUnit_iff_mk_pos] at hy ⊢
  apply

Depends on / 依赖: FiniteElement, FiniteElement.not_isUnit_iff_mk_pos, IsLocalRing, IsLocalRing.mem_maximalIdeal, Quotient, Quotient.eq, Set.mem_preimage, Set.mem_singleton_iff, Submodule, Submodule.quotientRel_def, hxz.trans, hy.trans_le, mem_maximalIdeal, mem_nonunits_iff, mem_preimage, mem_singleton_iff, mk_antitoneOn, not_isUnit_iff_mk_pos, quotientRel_def, trans_le
-/
instance ordConnected_preimage_mk' : forall x, Set.OrdConnected Quotient.mk
    (Submodule.quotientRel (IsLocalRing.maximalIdeal (FiniteElement K))) ⁻¹' {x} := by
  refine fun x => ⟨?_⟩
  rintro x rfl y hy z ⟨hxz, hzy⟩
  have := hxz.trans hzy
  rw [Set.mem_preimage]; rw [Set.mem_singleton_iff]; rw [Quotient.eq]; rw [Submodule.quotientRel_def]; rw [IsLocalRing.mem_maximalIdeal]; rw [mem_nonunits_iff]; rw [FiniteElement.not_isUnit_iff_mk_pos] at hy ⊢
  apply hy.trans_le (mk_antitoneOn _ _ _) <;> simpa

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder (FiniteResidueField K)
  body: haveI := Classical.decRel fun x y : FiniteElement K =>
    letI := Submodule.quotientRel (IsLocalRing.maximalIdeal (FiniteElement K))
    x ≈ y
inferInstanceAs LinearOrder (Quotient _)

中文:
实例 :
  签名: 线性序 (FiniteResidueField K)
  定义体: haveI := Classical.decRel fun x y : FiniteElement K =>
    letI := Submodule.quotientRel (IsLocalRing.maximalIdeal (FiniteElement K))
    x ≈ y
inferInstanceAs LinearOrder (Quotient _)

Depends on / 依赖: Classical, Classical.decRel, FiniteElement, IsLocalRing, IsLocalRing.maximalIdeal, LinearOrder, Quotient, Submodule, Submodule.quotientRel, decRel, maximalIdeal, quotientRel
-/
instance : LinearOrder (FiniteResidueField K) :=
  haveI := Classical.decRel fun x y : FiniteElement K =>
    letI := Submodule.quotientRel (IsLocalRing.maximalIdeal (FiniteElement K))
    x ≈ y
inferInstanceAs LinearOrder (Quotient _)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : FiniteElement K ->+*o FiniteResidueField K where
  body: Quotient.mk_monotone h
  __ := IsLocalRing.residue (FiniteElement K)

中文:
定义 mk
  签名: : FiniteElement K ->+*o FiniteResidueField K where
  定义体: Quotient.mk_monotone h
  __ := IsLocalRing.residue (FiniteElement K)

Depends on / 依赖: Quotient, Quotient.mk_monotone, mk_monotone
-/
def mk : FiniteElement K ->+*o FiniteResidueField K where
  monotone' _ _ h := Quotient.mk_monotone h
  __ := IsLocalRing.residue (FiniteElement K)

set_option backward.isDefEq.respectTransparency.types false in
@[induction_eliminator]
/--
theorem `ind` / 定理 `ind`

English:
theorem ind
  given: {motive : FiniteResidueField K -> Prop} (mk : forall x, motive (mk x))
  statement: forall x, motive x
  proof: Quotient.ind mk

中文:
定理 ind
  条件: {motive : FiniteResidueField K -> 命题} (mk : 对任意 x, motive (mk x))
  结论: 对任意 x, motive x
  证明: Quotient.ind mk

Depends on / 依赖: Quotient, Quotient.ind
-/
theorem ind {motive : FiniteResidueField K -> Prop} (mk : forall x, motive (mk x)) : forall x, motive x :=
  Quotient.ind mk

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `ordConnected_preimage_mk` / 实例 `ordConnected_preimage_mk`

English:
instance ordConnected_preimage_mk
  signature: :
  body: ordConnected_preimage_mk'

中文:
实例 ordConnected_preimage_mk
  签名: :
  定义体: ordConnected_preimage_mk'

Depends on / 依赖: ordConnected_preimage_mk
-/
instance ordConnected_preimage_mk :
    forall x, Set.OrdConnected (mk ⁻¹' ({x} : Set (FiniteResidueField K))) :=
  ordConnected_preimage_mk'

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mk_eq_mk` / 定理 `mk_eq_mk`

English:
theorem mk_eq_mk
  given: {x y : FiniteElement K}
  statement: mk x = mk y ↔ 0 < ArchimedeanClass.mk (x.1 - y.1)
  proof: by
  apply Quotient.eq.trans
  rw [Submodule.quotientRel_def]; rw [IsLocalRing.mem_maximalIdeal]; rw [mem_nonunits_iff]; rw [FiniteElement.not_isUnit_iff_mk_pos]; rw [AddSubgroupClass.coe_sub]

中文:
定理 mk_eq_mk
  条件: {x y : FiniteElement K}
  结论: mk x = mk y ↔ 0 < ArchimedeanClass.mk (x.1 - y.1)
  证明: by
  apply Quotient.eq.trans
  rw [Submodule.quotientRel_def]; rw [IsLocalRing.mem_maximalIdeal]; rw [mem_nonunits_iff]; rw [FiniteElement.not_isUnit_iff_mk_pos]; rw [AddSubgroupClass.coe_sub]

Depends on / 依赖: AddSubgroupClass, AddSubgroupClass.coe_sub, FiniteElement, FiniteElement.not_isUnit_iff_mk_pos, IsLocalRing, IsLocalRing.mem_maximalIdeal, Quotient, Quotient.eq.trans, Submodule, Submodule.quotientRel_def, coe_sub, mem_maximalIdeal, mem_nonunits_iff, not_isUnit_iff_mk_pos, quotientRel_def
-/
theorem mk_eq_mk {x y : FiniteElement K} : mk x = mk y ↔ 0 < ArchimedeanClass.mk (x.1 - y.1) := by
  apply Quotient.eq.trans
  rw [Submodule.quotientRel_def]; rw [IsLocalRing.mem_maximalIdeal]; rw [mem_nonunits_iff]; rw [FiniteElement.not_isUnit_iff_mk_pos]; rw [AddSubgroupClass.coe_sub]

/--
theorem `mk_eq_zero` / 定理 `mk_eq_zero`

English:
theorem mk_eq_zero
  given: {x : FiniteElement K}
  statement: mk x = 0 ↔ 0 < ArchimedeanClass.mk x.1
  proof: by
  apply mk_eq_mk.trans
  simp

中文:
定理 mk_eq_zero
  条件: {x : FiniteElement K}
  结论: mk x = 0 ↔ 0 < ArchimedeanClass.mk x.1
  证明: by
  apply mk_eq_mk.trans
  simp

Depends on / 依赖: mk_eq_mk, mk_eq_mk.trans
-/
theorem mk_eq_zero {x : FiniteElement K} : mk x = 0 ↔ 0 < ArchimedeanClass.mk x.1 := by
  apply mk_eq_mk.trans
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mk_ne_zero` / 定理 `mk_ne_zero`

English:
theorem mk_ne_zero
  given: {x : FiniteElement K}
  statement: mk x != 0 ↔ ArchimedeanClass.mk x.1 = 0
  proof: by
  rw [ne_eq]; rw [mk_eq_zero]; rw [not_lt]; rw [x.2.ge_iff_eq']

中文:
定理 mk_ne_zero
  条件: {x : FiniteElement K}
  结论: mk x != 0 ↔ ArchimedeanClass.mk x.1 = 0
  证明: by
  rw [ne_eq]; rw [mk_eq_zero]; rw [not_lt]; rw [x.2.ge_iff_eq']

Depends on / 依赖: ge_iff_eq, mk_eq_zero, ne_eq, not_lt
-/
theorem mk_ne_zero {x : FiniteElement K} : mk x != 0 ↔ ArchimedeanClass.mk x.1 = 0 := by
  rw [ne_eq]; rw [mk_eq_zero]; rw [not_lt]; rw [x.2.ge_iff_eq']

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: {x y : FiniteElement K}
  statement: mk x <= mk y ↔ x <= y ∨ mk x = mk y
  proof: by
  refine (Quotient.mk_le_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

中文:
定理 mk_le_mk
  条件: {x y : FiniteElement K}
  结论: mk x <= mk y ↔ x <= y ∨ mk x = mk y
  证明: by
  refine (Quotient.mk_le_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

Depends on / 依赖: Quotient, Quotient.eq_iff_equiv, Quotient.mk_le_mk, eq_iff_equiv, mk_le_mk, ordConnected_preimage_mk
-/
theorem mk_le_mk {x y : FiniteElement K} : mk x <= mk y ↔ x <= y ∨ mk x = mk y := by
  refine (Quotient.mk_le_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mk_lt_mk` / 定理 `mk_lt_mk`

English:
theorem mk_lt_mk
  given: {x y : FiniteElement K}
  statement: mk x < mk y ↔ x < y ∧ mk x != mk y
  proof: by
  refine (Quotient.mk_lt_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

中文:
定理 mk_lt_mk
  条件: {x y : FiniteElement K}
  结论: mk x < mk y ↔ x < y ∧ mk x != mk y
  证明: by
  refine (Quotient.mk_lt_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

Depends on / 依赖: Quotient, Quotient.eq_iff_equiv, Quotient.mk_lt_mk, eq_iff_equiv, mk_lt_mk, ordConnected_preimage_mk
-/
theorem mk_lt_mk {x y : FiniteElement K} : mk x < mk y ↔ x < y ∧ mk x != mk y := by
  refine (Quotient.mk_lt_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `lt_of_mk_lt_mk` / 定理 `lt_of_mk_lt_mk`

English:
theorem lt_of_mk_lt_mk
  given: {x y : FiniteElement K} (h : mk x < mk y)
  statement: x < y
  proof: (mk_lt_mk.1 h).1

中文:
定理 lt_of_mk_lt_mk
  条件: {x y : FiniteElement K} (h : mk x < mk y)
  结论: x < y
  证明: (mk_lt_mk.1 h).1

Depends on / 依赖: mk_lt_mk
-/
theorem lt_of_mk_lt_mk {x y : FiniteElement K} (h : mk x < mk y) : x < y :=
  (mk_lt_mk.1 h).1

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mul_le_mul_of_nonneg_left'` / 定理 `mul_le_mul_of_nonneg_left'`

English:
theorem mul_le_mul_of_nonneg_left'
  given: {x y z : FiniteResidueField K} (h : x <= y) (hz : 0 <= z)
  proof: by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  rw [← map_mul]; rw [← map_mul]
  rw [← map_zero mk] at hz
  rw [mk_le_mk] at h hz ⊢
  grind [mul_le_mul_of_nonneg_left]

中文:
定理 mul_le_mul_of_nonneg_left'
  条件: {x y z : FiniteResidueField K} (h : x <= y) (hz : 0 <= z)
  证明: by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  rw [← map_mul]; rw [← map_mul]
  rw [← map_zero mk] at hz
  rw [mk_le_mk] at h hz ⊢
  grind [mul_le_mul_of_nonneg_left]
-/
private theorem mul_le_mul_of_nonneg_left' {x y z : FiniteResidueField K} (h : x <= y) (hz : 0 <= z) :
    z * x <= z * y := by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  rw [← map_mul]; rw [← map_mul]
  rw [← map_zero mk] at hz
  rw [mk_le_mk] at h hz ⊢
  grind [mul_le_mul_of_nonneg_left]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedRing (FiniteResidueField K)
  body: mk.monotone' zero_le_one
  add_le_add_left x y h z := by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    obtain h | h := mk_le_mk.1 h
· exact mk.monotone' add_le_add_left h _
    · rw [h]
  mul_le_mul_of_nonneg_left _ hx _ _ h := mul_le_mul_of_nonneg_left' h h

中文:
实例 :
  签名: 是Ordered环 (FiniteResidueField K)
  定义体: mk.monotone' zero_le_one
  add_le_add_left x y h z := by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    obtain h | h := mk_le_mk.1 h
· exact mk.monotone' add_le_add_left h _
    · rw [h]
  mul_le_mul_of_nonneg_left _ hx _ _ h := mul_le_mul_of_nonneg_left' h h

Depends on / 依赖: mk.monotone, monotone, zero_le_one
-/
instance : IsOrderedRing (FiniteResidueField K) where
  zero_le_one := mk.monotone' zero_le_one
  add_le_add_left x y h z := by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    obtain h | h := mk_le_mk.1 h
· exact mk.monotone' add_le_add_left h _
    · rw [h]
  mul_le_mul_of_nonneg_left _ hx _ _ h := mul_le_mul_of_nonneg_left' h hx
  mul_le_mul_of_nonneg_right x hx y z h := by
    simp_rw [mul_comm _ x]
    exact mul_le_mul_of_nonneg_left' h hx

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Archimedean (FiniteResidueField K)
  body: by
    induction x with | mk x
    induction y with | mk y
    obtain hx | hx := le_or_gt (mk x) 0
    · use 0
      rwa [zero_nsmul]
    · obtain ⟨n, hn⟩ := ((mk_ne_zero.1 hy.ne').trans (mk_ne_zero.1 hx.ne').symm).le
      refine ⟨n, mk.monotone' ?_⟩
      change x.1 <= n • y.1
      convert! ← hn


中文:
实例 :
  签名: 阿基米德 (FiniteResidueField K)
  定义体: by
    induction x with | mk x
    induction y with | mk y
    obtain hx | hx := le_or_gt (mk x) 0
    · use 0
      rwa [zero_nsmul]
    · obtain ⟨n, hn⟩ := ((mk_ne_zero.1 hy.ne').trans (mk_ne_zero.1 hx.ne').symm).le
      refine ⟨n, mk.monotone' ?_⟩
      change x.1 <= n • y.1
      convert! ← hn


Depends on / 依赖: abs_of_pos, convert, hx.ne, hy.ne, le_or_gt, lt_of_mk_lt_mk, mk.monotone, mk_ne_zero, monotone, zero_nsmul
-/
instance : Archimedean (FiniteResidueField K) where
  arch x y hy := by
    induction x with | mk x
    induction y with | mk y
    obtain hx | hx := le_or_gt (mk x) 0
    · use 0
      rwa [zero_nsmul]
    · obtain ⟨n, hn⟩ := ((mk_ne_zero.1 hy.ne').trans (mk_ne_zero.1 hx.ne').symm).le
      refine ⟨n, mk.monotone' ?_⟩
      change x.1 <= n • y.1
      convert! ← hn
· exact abs_of_pos lt_of_mk_lt_mk hx
· exact abs_of_pos lt_of_mk_lt_mk hy

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `mk_ratCast` / 定理 `mk_ratCast`

English:
theorem mk_ratCast
  given: (q : Rat)
  statement: mk (q : FiniteElement K) = q
  proof: by
  change mk (FiniteElement.mk ..) = _
  cases q with | div n d hd
  rw [← mul_left_inj' (c := ↑d) (mod_cast hd)]; rw [← map_natCast mk d]; rw [← map_mul]; rw [← FiniteElement.mk_natCast]; rw [FiniteElement.mk_mul_mk]
  simp_all

中文:
定理 mk_ratCast
  条件: (q : 有理数)
  结论: mk (q : FiniteElement K) = q
  证明: by
  change mk (FiniteElement.mk ..) = _
  cases q with | div n d hd
  rw [← mul_left_inj' (c := ↑d) (mod_cast hd)]; rw [← map_natCast mk d]; rw [← map_mul]; rw [← FiniteElement.mk_natCast]; rw [FiniteElement.mk_mul_mk]
  simp_all

Depends on / 依赖: FiniteElement, FiniteElement.mk, FiniteElement.mk_mul_mk, FiniteElement.mk_natCast, map_mul, map_natCast, mk_mul_mk, mk_natCast, mod_cast, mul_left_inj
-/
theorem mk_ratCast (q : Rat) : mk (q : FiniteElement K) = q := by
  change mk (FiniteElement.mk ..) = _
  cases q with | div n d hd
  rw [← mul_left_inj' (c := ↑d) (mod_cast hd)]; rw [← map_natCast mk d]; rw [← map_mul]; rw [← FiniteElement.mk_natCast]; rw [FiniteElement.mk_mul_mk]
  simp_all

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `ofArchimedean` / `ofArchimedean` 的定义

English:
definition ofArchimedean
  signature: (f : R ->+*o K)
  body: mk .mk _ (mk_map_nonneg_of_archimedean f r)
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by
    simp_rw [map_add]
    exact mk.map_add
      (.mk _ (mk_map_nonneg_of_archimedean f x)) (.mk _ (mk_map_nonneg_of_archimedean f y))
  map_mul' x y := by
    simp_rw [map_mul]
    exact mk

中文:
定义 ofArchimedean
  签名: (f : R ->+*o K)
  定义体: mk .mk _ (mk_map_nonneg_of_archimedean f r)
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by
    simp_rw [map_add]
    exact mk.map_add
      (.mk _ (mk_map_nonneg_of_archimedean f x)) (.mk _ (mk_map_nonneg_of_archimedean f y))
  map_mul' x y := by
    simp_rw [map_mul]
    exact mk

Depends on / 依赖: mk_map_nonneg_of_archimedean
-/
def ofArchimedean (f : R ->+*o K) : R ->+*o FiniteResidueField K where
toFun r := mk .mk _ (mk_map_nonneg_of_archimedean f r)
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by
    simp_rw [map_add]
    exact mk.map_add
      (.mk _ (mk_map_nonneg_of_archimedean f x)) (.mk _ (mk_map_nonneg_of_archimedean f y))
  map_mul' x y := by
    simp_rw [map_mul]
    exact mk.map_mul
      (.mk _ (mk_map_nonneg_of_archimedean f x)) (.mk _ (mk_map_nonneg_of_archimedean f y))
monotone' x y h := mk.monotone' f.monotone' h

/--
theorem `ofArchimedean_apply` / 定理 `ofArchimedean_apply`

English:
theorem ofArchimedean_apply
  given: (f : R ->+*o K) (r : R)
  proof: rfl

中文:
定理 ofArchimedean_apply
  条件: (f : R ->+*o K) (r : R)
  证明: rfl
-/
theorem ofArchimedean_apply (f : R ->+*o K) (r : R) :
    ofArchimedean f r = mk (.mk _ (mk_map_nonneg_of_archimedean f r)) :=
  rfl

/--
theorem `ofArchimedean_injective` / 定理 `ofArchimedean_injective`

English:
theorem ofArchimedean_injective
  given: (f : R ->+*o K)
  statement: Function.Injective (ofArchimedean f)
  proof: by
  rw [injective_iff_map_eq_zero]
  intro r hr
  contrapose! hr
  rw [ofArchimedean_apply]; rw [mk_ne_zero]
  exact mk_map_of_archimedean' f hr

中文:
定理 ofArchimedean_injective
  条件: (f : R ->+*o K)
  结论: 函数.单射 (ofArchimedean f)
  证明: by
  rw [injective_iff_map_eq_zero]
  intro r hr
  contrapose! hr
  rw [ofArchimedean_apply]; rw [mk_ne_zero]
  exact mk_map_of_archimedean' f hr

Depends on / 依赖: contrapose, injective_iff_map_eq_zero, mk_map_of_archimedean, mk_ne_zero, ofArchimedean_apply
-/
theorem ofArchimedean_injective (f : R ->+*o K) : Function.Injective (ofArchimedean f) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  contrapose! hr
  rw [ofArchimedean_apply]; rw [mk_ne_zero]
  exact mk_map_of_archimedean' f hr

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `ofArchimedean_inj` / 定理 `ofArchimedean_inj`

English:
theorem ofArchimedean_inj
  given: (f : R ->+*o K) {x y : R}
  proof: (ofArchimedean_injective f).eq_iff

中文:
定理 ofArchimedean_inj
  条件: (f : R ->+*o K) {x y : R}
  证明: (ofArchimedean_injective f).eq_iff

Depends on / 依赖: eq_iff, ofArchimedean_injective
-/
theorem ofArchimedean_inj (f : R ->+*o K) {x y : R} :
    ofArchimedean f x = ofArchimedean f y ↔ x = y :=
  (ofArchimedean_injective f).eq_iff

end FiniteResidueField

/-! ### Standard part -/

set_option backward.isDefEq.respectTransparency.types false in
/-- The standard part of a `FiniteElement` is the unique real number with an infinitesimal
difference.

For any infinite inputs, this function outputs a junk value of 0. -/
@[no_expose]
/--
Definition of `stdPart` / `stdPart` 的定义

English:
definition stdPart
  signature: (x : K)
  body: if h : 0 <= mk x then
    OrderRingHom.comp Classical.ofNonempty FiniteResidueField.mk (.mk x h) else 0

中文:
定义 stdPart
  签名: (x : K)
  定义体: if h : 0 <= mk x then
    OrderRingHom.comp Classical.ofNonempty FiniteResidueField.mk (.mk x h) else 0

Depends on / 依赖: Classical, Classical.ofNonempty, FiniteResidueField, FiniteResidueField.mk, OrderRingHom, OrderRingHom.comp, ofNonempty
-/
def stdPart (x : K) : Real :=
  if h : 0 <= mk x then
    OrderRingHom.comp Classical.ofNonempty FiniteResidueField.mk (.mk x h) else 0

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `stdPart_of_mk_nonneg` / 定理 `stdPart_of_mk_nonneg`

English:
theorem stdPart_of_mk_nonneg
  given: (f : FiniteResidueField K ->+*o Real) (h : 0 <= mk x)
  proof: by
  rw [stdPart]; rw [dif_pos h]; rw [OrderRingHom.comp_apply]
  congr
  exact Subsingleton.allEq _ _

中文:
定理 stdPart_of_mk_nonneg
  条件: (f : FiniteResidueField K ->+*o 实数) (h : 0 <= mk x)
  证明: by
  rw [stdPart]; rw [dif_pos h]; rw [OrderRingHom.comp_apply]
  congr
  exact Subsingleton.allEq _ _

Depends on / 依赖: OrderRingHom, OrderRingHom.comp_apply, Subsingleton, Subsingleton.allEq, comp_apply, dif_pos, stdPart
-/
theorem stdPart_of_mk_nonneg (f : FiniteResidueField K ->+*o Real) (h : 0 <= mk x) :
    stdPart x = f (.mk <| .mk x h) := by
  rw [stdPart]; rw [dif_pos h]; rw [OrderRingHom.comp_apply]
  congr
  exact Subsingleton.allEq _ _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `stdPart_eq_zero` / 定理 `stdPart_eq_zero`

English:
theorem stdPart_eq_zero
  given: {x : K}
  statement: stdPart x = 0 ↔ mk x != 0 where
  proof: by
    obtain h | h := h.lt_or_gt
    · exact dif_neg h.not_ge
    · rw [stdPart, dif_pos h.le, OrderRingHom.comp_apply, FiniteResidueField.mk_eq_zero.2 h,
        map_zero]
  mp := by
    contrapose!
    intro h
    rwa [stdPart_of_mk_nonneg Classical.ofNonempty h.ge, map_ne_zero, FiniteResidueFiel

中文:
定理 stdPart_eq_zero
  条件: {x : K}
  结论: stdPart x = 0 ↔ mk x != 0 where
  证明: by
    obtain h | h := h.lt_or_gt
    · exact dif_neg h.not_ge
    · rw [stdPart, dif_pos h.le, OrderRingHom.comp_apply, FiniteResidueField.mk_eq_zero.2 h,
        map_zero]
  mp := by
    contrapose!
    intro h
    rwa [stdPart_of_mk_nonneg Classical.ofNonempty h.ge, map_ne_zero, FiniteResidueFiel

Depends on / 依赖: Classical, Classical.ofNonempty, FiniteResidueField, FiniteResidueField.mk_eq_zero, FiniteResidueField.mk_ne_zero, OrderRingHom, OrderRingHom.comp_apply, comp_apply, contrapose, dif_neg, dif_pos, h.ge, h.le, h.lt_or_gt, h.not_ge, lt_or_gt, map_ne_zero, map_zero, mk_eq_zero, mk_ne_zero
-/
theorem stdPart_eq_zero {x : K} : stdPart x = 0 ↔ mk x != 0 where
  mpr h := by
    obtain h | h := h.lt_or_gt
    · exact dif_neg h.not_ge
    · rw [stdPart, dif_pos h.le, OrderRingHom.comp_apply, FiniteResidueField.mk_eq_zero.2 h,
        map_zero]
  mp := by
    contrapose!
    intro h
    rwa [stdPart_of_mk_nonneg Classical.ofNonempty h.ge, map_ne_zero, FiniteResidueField.mk_ne_zero]

alias ⟨_, stdPart_of_mk_ne_zero⟩ := stdPart_eq_zero

/--
theorem `stdPart_monotoneOn` / 定理 `stdPart_monotoneOn`

English:
theorem stdPart_monotoneOn
  statement: MonotoneOn stdPart {x : K | 0 <= mk x}
  proof: by
  intro x (hx : 0 <= mk x) y (hy : 0 <= mk y) h
  unfold stdPart
  rw [dif_pos hx]; rw [dif_pos hy]
  apply OrderRingHom.monotone'
  rwa [FiniteElement.mk_le_mk]

@[simp]

中文:
定理 stdPart_monotoneOn
  结论: MonotoneOn stdPart {x : K | 0 <= mk x}
  证明: by
  intro x (hx : 0 <= mk x) y (hy : 0 <= mk y) h
  unfold stdPart
  rw [dif_pos hx]; rw [dif_pos hy]
  apply OrderRingHom.monotone'
  rwa [FiniteElement.mk_le_mk]

@[simp]

Depends on / 依赖: FiniteElement, FiniteElement.mk_le_mk, OrderRingHom, OrderRingHom.monotone, dif_pos, mk_le_mk, monotone, stdPart
-/
theorem stdPart_monotoneOn : MonotoneOn stdPart {x : K | 0 <= mk x} := by
  intro x (hx : 0 <= mk x) y (hy : 0 <= mk y) h
  unfold stdPart
  rw [dif_pos hx]; rw [dif_pos hy]
  apply OrderRingHom.monotone'
  rwa [FiniteElement.mk_le_mk]

@[simp]
/--
theorem `stdPart_zero` / 定理 `stdPart_zero`

English:
theorem stdPart_zero
  statement: stdPart (0 : K) = 0
  proof: by
  rw [stdPart]; rw [dif_pos] <;> simp

@[simp]

中文:
定理 stdPart_zero
  结论: stdPart (0 : K) = 0
  证明: by
  rw [stdPart]; rw [dif_pos] <;> simp

@[simp]

Depends on / 依赖: dif_pos, stdPart
-/
theorem stdPart_zero : stdPart (0 : K) = 0 := by
  rw [stdPart]; rw [dif_pos] <;> simp

@[simp]
/--
theorem `stdPart_one` / 定理 `stdPart_one`

English:
theorem stdPart_one
  statement: stdPart (1 : K) = 1
  proof: by
  rw [stdPart]; rw [dif_pos] <;> simp

@[simp]

中文:
定理 stdPart_one
  结论: stdPart (1 : K) = 1
  证明: by
  rw [stdPart]; rw [dif_pos] <;> simp

@[simp]

Depends on / 依赖: dif_pos, stdPart
-/
theorem stdPart_one : stdPart (1 : K) = 1 := by
  rw [stdPart]; rw [dif_pos] <;> simp

@[simp]
/--
theorem `stdPart_neg` / 定理 `stdPart_neg`

English:
theorem stdPart_neg
  given: (x : K)
  statement: stdPart (-x) = -stdPart x
  proof: by
  simp_rw [stdPart, ArchimedeanClass.mk_neg]
  split_ifs
  · rw [← FiniteElement.neg_mk, map_neg]
  · simp

@[simp]

中文:
定理 stdPart_neg
  条件: (x : K)
  结论: stdPart (-x) = -stdPart x
  证明: by
  simp_rw [stdPart, ArchimedeanClass.mk_neg]
  split_ifs
  · rw [← FiniteElement.neg_mk, map_neg]
  · simp

@[simp]

Depends on / 依赖: ArchimedeanClass, ArchimedeanClass.mk_neg, FiniteElement, FiniteElement.neg_mk, map_neg, mk_neg, neg_mk, simp_rw, split_ifs, stdPart
-/
theorem stdPart_neg (x : K) : stdPart (-x) = -stdPart x := by
  simp_rw [stdPart, ArchimedeanClass.mk_neg]
  split_ifs
  · rw [← FiniteElement.neg_mk, map_neg]
  · simp

@[simp]
/--
theorem `stdPart_inv` / 定理 `stdPart_inv`

English:
theorem stdPart_inv
  given: (x : K)
  statement: stdPart x⁻¹ = (stdPart x)⁻¹
  proof: by
  obtain hx | hx := eq_or_ne (mk x) 0
  · unfold stdPart
    have hx' : 0 <= mk x⁻¹ := by simp_all
    rw [dif_pos hx.ge]; rw [dif_pos hx']
    · apply eq_inv_of_mul_eq_one_left
      suffices FiniteElement.mk x⁻¹ hx' * .mk x hx.ge = 1 by
        rw [← map_mul]; rw [this]; rw [map_one]
      ext


中文:
定理 stdPart_inv
  条件: (x : K)
  结论: stdPart x⁻¹ = (stdPart x)⁻¹
  证明: by
  obtain hx | hx := eq_or_ne (mk x) 0
  · unfold stdPart
    have hx' : 0 <= mk x⁻¹ := by simp_all
    rw [dif_pos hx.ge]; rw [dif_pos hx']
    · apply eq_inv_of_mul_eq_one_left
      suffices FiniteElement.mk x⁻¹ hx' * .mk x hx.ge = 1 by
        rw [← map_mul]; rw [this]; rw [map_one]
      ext


Depends on / 依赖: FiniteElement, FiniteElement.mk, dif_pos, eq_inv_of_mul_eq_one_left, eq_or_ne, hx.ge, inv_zero, map_mul, map_one, mk_inv, neg_ne_zero, stdPart, stdPart_of_mk_ne_zero
-/
theorem stdPart_inv (x : K) : stdPart x⁻¹ = (stdPart x)⁻¹ := by
  obtain hx | hx := eq_or_ne (mk x) 0
  · unfold stdPart
    have hx' : 0 <= mk x⁻¹ := by simp_all
    rw [dif_pos hx.ge]; rw [dif_pos hx']
    · apply eq_inv_of_mul_eq_one_left
      suffices FiniteElement.mk x⁻¹ hx' * .mk x hx.ge = 1 by
        rw [← map_mul]; rw [this]; rw [map_one]
      ext
      apply inv_mul_cancel₀
      aesop
  · rw [stdPart_of_mk_ne_zero hx, stdPart_of_mk_ne_zero, inv_zero]
    rwa [mk_inv, neg_ne_zero]

/--
theorem `stdPart_add` / 定理 `stdPart_add`

English:
theorem stdPart_add
  given: (hx : 0 <= mk x) (hy : 0 <= mk y)
  statement: stdPart (x + y) = stdPart x + stdPart y
  proof: by
  unfold stdPart
  rw [dif_pos hx]; rw [dif_pos hy]; rw [dif_pos]
  exact map_add _ (FiniteElement.mk x hx) (.mk y hy)

中文:
定理 stdPart_add
  条件: (hx : 0 <= mk x) (hy : 0 <= mk y)
  结论: stdPart (x + y) = stdPart x + stdPart y
  证明: by
  unfold stdPart
  rw [dif_pos hx]; rw [dif_pos hy]; rw [dif_pos]
  exact map_add _ (FiniteElement.mk x hx) (.mk y hy)

Depends on / 依赖: FiniteElement, FiniteElement.mk, dif_pos, map_add, stdPart
-/
theorem stdPart_add (hx : 0 <= mk x) (hy : 0 <= mk y) : stdPart (x + y) = stdPart x + stdPart y := by
  unfold stdPart
  rw [dif_pos hx]; rw [dif_pos hy]; rw [dif_pos]
  exact map_add _ (FiniteElement.mk x hx) (.mk y hy)

/--
theorem `stdPart_add_eq_right` / 定理 `stdPart_add_eq_right`

English:
theorem stdPart_add_eq_right
  given: (hx : 0 < mk x)
  statement: stdPart (x + y) = stdPart y
  proof: by
  obtain hy | hy := le_or_gt 0 (mk y)
  · rw [stdPart_add hx.le hy, stdPart_of_mk_ne_zero hx.ne', zero_add]
  · rw [stdPart_of_mk_ne_zero hy.ne, stdPart_of_mk_ne_zero]
    rw [mk_add_eq_mk_right (hy.trans hx)]
    exact hy.ne

中文:
定理 stdPart_add_eq_right
  条件: (hx : 0 < mk x)
  结论: stdPart (x + y) = stdPart y
  证明: by
  obtain hy | hy := le_or_gt 0 (mk y)
  · rw [stdPart_add hx.le hy, stdPart_of_mk_ne_zero hx.ne', zero_add]
  · rw [stdPart_of_mk_ne_zero hy.ne, stdPart_of_mk_ne_zero]
    rw [mk_add_eq_mk_right (hy.trans hx)]
    exact hy.ne

Depends on / 依赖: hx.le, hx.ne, hy.ne, hy.trans, le_or_gt, mk_add_eq_mk_right, stdPart_add, stdPart_of_mk_ne_zero, zero_add
-/
theorem stdPart_add_eq_right (hx : 0 < mk x) : stdPart (x + y) = stdPart y := by
  obtain hy | hy := le_or_gt 0 (mk y)
  · rw [stdPart_add hx.le hy, stdPart_of_mk_ne_zero hx.ne', zero_add]
  · rw [stdPart_of_mk_ne_zero hy.ne, stdPart_of_mk_ne_zero]
    rw [mk_add_eq_mk_right (hy.trans hx)]
    exact hy.ne

/--
theorem `stdPart_add_eq_left` / 定理 `stdPart_add_eq_left`

English:
theorem stdPart_add_eq_left
  given: (hy : 0 < mk y)
  statement: stdPart (x + y) = stdPart x
  proof: by
  rw [add_comm]; rw [stdPart_add_eq_right hy]

中文:
定理 stdPart_add_eq_left
  条件: (hy : 0 < mk y)
  结论: stdPart (x + y) = stdPart x
  证明: by
  rw [add_comm]; rw [stdPart_add_eq_right hy]

Depends on / 依赖: add_comm, stdPart_add_eq_right
-/
theorem stdPart_add_eq_left (hy : 0 < mk y) : stdPart (x + y) = stdPart x := by
  rw [add_comm]; rw [stdPart_add_eq_right hy]

/--
theorem `stdPart_sub` / 定理 `stdPart_sub`

English:
theorem stdPart_sub
  given: (hx : 0 <= mk x) (hy : 0 <= mk y)
  statement: stdPart (x - y) = stdPart x - stdPart y
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [stdPart_add hx]; rw [stdPart_neg]
  rwa [mk_neg]

中文:
定理 stdPart_sub
  条件: (hx : 0 <= mk x) (hy : 0 <= mk y)
  结论: stdPart (x - y) = stdPart x - stdPart y
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [stdPart_add hx]; rw [stdPart_neg]
  rwa [mk_neg]

Depends on / 依赖: mk_neg, stdPart_add, stdPart_neg, sub_eq_add_neg
-/
theorem stdPart_sub (hx : 0 <= mk x) (hy : 0 <= mk y) : stdPart (x - y) = stdPart x - stdPart y := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [stdPart_add hx]; rw [stdPart_neg]
  rwa [mk_neg]

/--
theorem `stdPart_sub_eq_right` / 定理 `stdPart_sub_eq_right`

English:
theorem stdPart_sub_eq_right
  given: (hx : 0 < mk x)
  statement: stdPart (x - y) = -stdPart y
  proof: by
  rw [sub_eq_add_neg]; rw [stdPart_add_eq_right hx]; rw [stdPart_neg]

中文:
定理 stdPart_sub_eq_right
  条件: (hx : 0 < mk x)
  结论: stdPart (x - y) = -stdPart y
  证明: by
  rw [sub_eq_add_neg]; rw [stdPart_add_eq_right hx]; rw [stdPart_neg]

Depends on / 依赖: stdPart_add_eq_right, stdPart_neg, sub_eq_add_neg
-/
theorem stdPart_sub_eq_right (hx : 0 < mk x) : stdPart (x - y) = -stdPart y := by
  rw [sub_eq_add_neg]; rw [stdPart_add_eq_right hx]; rw [stdPart_neg]

/--
theorem `stdPart_sub_eq_left` / 定理 `stdPart_sub_eq_left`

English:
theorem stdPart_sub_eq_left
  given: (hy : 0 < mk y)
  statement: stdPart (x - y) = stdPart x
  proof: by
  rw [sub_eq_add_neg]; rw [stdPart_add_eq_left (by simpa)]

中文:
定理 stdPart_sub_eq_left
  条件: (hy : 0 < mk y)
  结论: stdPart (x - y) = stdPart x
  证明: by
  rw [sub_eq_add_neg]; rw [stdPart_add_eq_left (by simpa)]

Depends on / 依赖: stdPart_add_eq_left, sub_eq_add_neg
-/
theorem stdPart_sub_eq_left (hy : 0 < mk y) : stdPart (x - y) = stdPart x := by
  rw [sub_eq_add_neg]; rw [stdPart_add_eq_left (by simpa)]

/--
theorem `stdPart_mul` / 定理 `stdPart_mul`

English:
theorem stdPart_mul
  given: (hx : 0 <= mk x) (hy : 0 <= mk y)
  statement: stdPart (x * y) = stdPart x * stdPart y
  proof: by
  unfold stdPart
  rw [dif_pos hx]; rw [dif_pos hy]; rw [dif_pos]
  exact map_mul _ (FiniteElement.mk x hx) (.mk y hy)

中文:
定理 stdPart_mul
  条件: (hx : 0 <= mk x) (hy : 0 <= mk y)
  结论: stdPart (x * y) = stdPart x * stdPart y
  证明: by
  unfold stdPart
  rw [dif_pos hx]; rw [dif_pos hy]; rw [dif_pos]
  exact map_mul _ (FiniteElement.mk x hx) (.mk y hy)

Depends on / 依赖: FiniteElement, FiniteElement.mk, dif_pos, map_mul, stdPart
-/
theorem stdPart_mul (hx : 0 <= mk x) (hy : 0 <= mk y) : stdPart (x * y) = stdPart x * stdPart y := by
  unfold stdPart
  rw [dif_pos hx]; rw [dif_pos hy]; rw [dif_pos]
  exact map_mul _ (FiniteElement.mk x hx) (.mk y hy)

/--
theorem `stdPart_div` / 定理 `stdPart_div`

English:
theorem stdPart_div
  given: (hx : 0 <= mk x) (hy : 0 <= -mk y)
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [stdPart_mul hx]; rw [stdPart_inv]
  rwa [mk_inv]

中文:
定理 stdPart_div
  条件: (hx : 0 <= mk x) (hy : 0 <= -mk y)
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [stdPart_mul hx]; rw [stdPart_inv]
  rwa [mk_inv]

Depends on / 依赖: div_eq_mul_inv, mk_inv, stdPart_inv, stdPart_mul
-/
theorem stdPart_div (hx : 0 <= mk x) (hy : 0 <= -mk y) :
    stdPart (x / y) = stdPart x / stdPart y := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [stdPart_mul hx]; rw [stdPart_inv]
  rwa [mk_inv]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `stdPart_ratCast` / 定理 `stdPart_ratCast`

English:
theorem stdPart_ratCast
  given: (q : Rat)
  statement: stdPart (q : K) = q
  proof: by
  rw [stdPart_of_mk_nonneg Classical.ofNonempty (mk_ratCast_nonneg q)]; rw [FiniteElement.mk_ratCast]; rw [FiniteResidueField.mk_ratCast]; rw [map_ratCast]

@[simp]

中文:
定理 stdPart_ratCast
  条件: (q : 有理数)
  结论: stdPart (q : K) = q
  证明: by
  rw [stdPart_of_mk_nonneg Classical.ofNonempty (mk_ratCast_nonneg q)]; rw [FiniteElement.mk_ratCast]; rw [FiniteResidueField.mk_ratCast]; rw [map_ratCast]

@[simp]

Depends on / 依赖: Classical, Classical.ofNonempty, FiniteElement, FiniteElement.mk_ratCast, FiniteResidueField, FiniteResidueField.mk_ratCast, map_ratCast, mk_ratCast, mk_ratCast_nonneg, ofNonempty, stdPart_of_mk_nonneg
-/
theorem stdPart_ratCast (q : Rat) : stdPart (q : K) = q := by
  rw [stdPart_of_mk_nonneg Classical.ofNonempty (mk_ratCast_nonneg q)]; rw [FiniteElement.mk_ratCast]; rw [FiniteResidueField.mk_ratCast]; rw [map_ratCast]

@[simp]
/--
theorem `stdPart_intCast` / 定理 `stdPart_intCast`

English:
theorem stdPart_intCast
  given: (n : Int)
  statement: stdPart (n : K) = n
  proof: mod_cast stdPart_ratCast n

@[simp]

中文:
定理 stdPart_intCast
  条件: (n : 整数)
  结论: stdPart (n : K) = n
  证明: mod_cast stdPart_ratCast n

@[simp]

Depends on / 依赖: mod_cast, stdPart_ratCast
-/
theorem stdPart_intCast (n : Int) : stdPart (n : K) = n :=
  mod_cast stdPart_ratCast n

@[simp]
/--
theorem `stdPart_natCast` / 定理 `stdPart_natCast`

English:
theorem stdPart_natCast
  given: (n : Nat)
  statement: stdPart (n : K) = n
  proof: mod_cast stdPart_intCast n

@[simp]

中文:
定理 stdPart_natCast
  条件: (n : 自然数)
  结论: stdPart (n : K) = n
  证明: mod_cast stdPart_intCast n

@[simp]

Depends on / 依赖: mod_cast, stdPart_intCast
-/
theorem stdPart_natCast (n : Nat) : stdPart (n : K) = n :=
  mod_cast stdPart_intCast n

@[simp]
/--
theorem `stdPart_ofNat` / 定理 `stdPart_ofNat`

English:
theorem stdPart_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: stdPart (ofNat(n) : K) = n
  proof: stdPart_natCast n

@[simp]

中文:
定理 stdPart_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: stdPart (of自然数(n) : K) = n
  证明: stdPart_natCast n

@[simp]

Depends on / 依赖: stdPart_natCast
-/
theorem stdPart_ofNat (n : Nat) [n.AtLeastTwo] : stdPart (ofNat(n) : K) = n :=
  stdPart_natCast n

@[simp]
/--
theorem `stdPart_map_real` / 定理 `stdPart_map_real`

English:
theorem stdPart_map_real
  given: (f : Real ->+*o K) (r : Real)
  statement: stdPart (f r) = r
  proof: by
  rw [stdPart]; rw [dif_pos]
exact r.ringHom_apply OrderRingHom.comp _ (FiniteResidueField.ofArchimedean f)

@[simp]

中文:
定理 stdPart_map_real
  条件: (f : 实数 ->+*o K) (r : 实数)
  结论: stdPart (f r) = r
  证明: by
  rw [stdPart]; rw [dif_pos]
exact r.ringHom_apply OrderRingHom.comp _ (FiniteResidueField.ofArchimedean f)

@[simp]

Depends on / 依赖: FiniteResidueField, FiniteResidueField.ofArchimedean, OrderRingHom, OrderRingHom.comp, dif_pos, ofArchimedean, r.ringHom_apply, ringHom_apply, stdPart
-/
theorem stdPart_map_real (f : Real ->+*o K) (r : Real) : stdPart (f r) = r := by
  rw [stdPart]; rw [dif_pos]
exact r.ringHom_apply OrderRingHom.comp _ (FiniteResidueField.ofArchimedean f)

@[simp]
/--
theorem `stdPart_real` / 定理 `stdPart_real`

English:
theorem stdPart_real
  given: (r : Real)
  statement: stdPart r = r
  proof: stdPart_map_real (.id Real) r

中文:
定理 stdPart_real
  条件: (r : 实数)
  结论: stdPart r = r
  证明: stdPart_map_real (.id Real) r

Depends on / 依赖: stdPart_map_real
-/
theorem stdPart_real (r : Real) : stdPart r = r :=
  stdPart_map_real (.id Real) r

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `ofArchimedean_stdPart` / 定理 `ofArchimedean_stdPart`

English:
theorem ofArchimedean_stdPart
  given: (f : Real ->+*o K) (hx : 0 <= mk x)
  proof: by
  rw [stdPart]; rw [dif_pos hx]; rw [← OrderRingHom.comp_apply]; rw [← OrderRingHom.comp_assoc]; rw [OrderRingHom.comp_apply]; rw [OrderRingHom.apply_eq_self]

中文:
定理 ofArchimedean_stdPart
  条件: (f : 实数 ->+*o K) (hx : 0 <= mk x)
  证明: by
  rw [stdPart]; rw [dif_pos hx]; rw [← OrderRingHom.comp_apply]; rw [← OrderRingHom.comp_assoc]; rw [OrderRingHom.comp_apply]; rw [OrderRingHom.apply_eq_self]

Depends on / 依赖: OrderRingHom, OrderRingHom.apply_eq_self, OrderRingHom.comp_apply, OrderRingHom.comp_assoc, apply_eq_self, comp_apply, comp_assoc, dif_pos, stdPart
-/
theorem ofArchimedean_stdPart (f : Real ->+*o K) (hx : 0 <= mk x) :
    FiniteResidueField.ofArchimedean f (stdPart x) = .mk (.mk x hx) := by
  rw [stdPart]; rw [dif_pos hx]; rw [← OrderRingHom.comp_apply]; rw [← OrderRingHom.comp_assoc]; rw [OrderRingHom.comp_apply]; rw [OrderRingHom.apply_eq_self]

/--
theorem `stdPart_nonneg` / 定理 `stdPart_nonneg`

English:
theorem stdPart_nonneg
  given: {x : K} (h : 0 <= x)
  statement: 0 <= stdPart x
  proof: by
  obtain hx | hx := eq_or_ne (ArchimedeanClass.mk x) 0
  · rw [stdPart, dif_pos hx.ge]
    exact map_nonneg _ h
  · rw [stdPart_of_mk_ne_zero hx]

中文:
定理 stdPart_nonneg
  条件: {x : K} (h : 0 <= x)
  结论: 0 <= stdPart x
  证明: by
  obtain hx | hx := eq_or_ne (ArchimedeanClass.mk x) 0
  · rw [stdPart, dif_pos hx.ge]
    exact map_nonneg _ h
  · rw [stdPart_of_mk_ne_zero hx]

Depends on / 依赖: ArchimedeanClass, ArchimedeanClass.mk, dif_pos, eq_or_ne, hx.ge, map_nonneg, stdPart, stdPart_of_mk_ne_zero
-/
theorem stdPart_nonneg {x : K} (h : 0 <= x) : 0 <= stdPart x := by
  obtain hx | hx := eq_or_ne (ArchimedeanClass.mk x) 0
  · rw [stdPart, dif_pos hx.ge]
    exact map_nonneg _ h
  · rw [stdPart_of_mk_ne_zero hx]

/--
theorem `stdPart_nonpos` / 定理 `stdPart_nonpos`

English:
theorem stdPart_nonpos
  given: {x : K} (h : x <= 0)
  statement: stdPart x <= 0
  proof: by
  simpa using stdPart_nonneg (neg_nonneg.2 h)

中文:
定理 stdPart_nonpos
  条件: {x : K} (h : x <= 0)
  结论: stdPart x <= 0
  证明: by
  simpa using stdPart_nonneg (neg_nonneg.2 h)

Depends on / 依赖: neg_nonneg, stdPart_nonneg
-/
theorem stdPart_nonpos {x : K} (h : x <= 0) : stdPart x <= 0 := by
  simpa using stdPart_nonneg (neg_nonneg.2 h)

/--
theorem `mk_sub_pos_iff` / 定理 `mk_sub_pos_iff`

English:
theorem mk_sub_pos_iff
  given: (f : Real ->+*o K) {r : Real} (hx : 0 <= mk x)
  proof: by
  refine (FiniteResidueField.mk_eq_zero
    (x := .mk x hx - .mk _ (mk_map_nonneg_of_archimedean f r))).symm.trans ?_
  rw [map_sub]; rw [← FiniteResidueField.ofArchimedean_apply]; rw [← ofArchimedean_stdPart f hx]; rw [sub_eq_zero]; rw [FiniteResidueField.ofArchimedean_inj f]

中文:
定理 mk_sub_pos_iff
  条件: (f : 实数 ->+*o K) {r : 实数} (hx : 0 <= mk x)
  证明: by
  refine (FiniteResidueField.mk_eq_zero
    (x := .mk x hx - .mk _ (mk_map_nonneg_of_archimedean f r))).symm.trans ?_
  rw [map_sub]; rw [← FiniteResidueField.ofArchimedean_apply]; rw [← ofArchimedean_stdPart f hx]; rw [sub_eq_zero]; rw [FiniteResidueField.ofArchimedean_inj f]

Depends on / 依赖: FiniteResidueField, FiniteResidueField.mk_eq_zero, FiniteResidueField.ofArchimedean_apply, FiniteResidueField.ofArchimedean_inj, map_sub, mk_eq_zero, mk_map_nonneg_of_archimedean, ofArchimedean_apply, ofArchimedean_inj, ofArchimedean_stdPart, sub_eq_zero, symm.trans
-/
theorem mk_sub_pos_iff (f : Real ->+*o K) {r : Real} (hx : 0 <= mk x) :
    0 < mk (x - f r) ↔ stdPart x = r := by
  refine (FiniteResidueField.mk_eq_zero
    (x := .mk x hx - .mk _ (mk_map_nonneg_of_archimedean f r))).symm.trans ?_
  rw [map_sub]; rw [← FiniteResidueField.ofArchimedean_apply]; rw [← ofArchimedean_stdPart f hx]; rw [sub_eq_zero]; rw [FiniteResidueField.ofArchimedean_inj f]

/--
theorem `mk_sub_stdPart_pos` / 定理 `mk_sub_stdPart_pos`

English:
theorem mk_sub_stdPart_pos
  given: (f : Real ->+*o K) (hx : 0 <= mk x)
  statement: 0 < mk (x - f (stdPart x))
  proof: (mk_sub_pos_iff f hx).2 rfl

中文:
定理 mk_sub_stdPart_pos
  条件: (f : 实数 ->+*o K) (hx : 0 <= mk x)
  结论: 0 < mk (x - f (stdPart x))
  证明: (mk_sub_pos_iff f hx).2 rfl

Depends on / 依赖: mk_sub_pos_iff
-/
theorem mk_sub_stdPart_pos (f : Real ->+*o K) (hx : 0 <= mk x) : 0 < mk (x - f (stdPart x)) :=
  (mk_sub_pos_iff f hx).2 rfl

/--
theorem `lt_of_lt_stdPart` / 定理 `lt_of_lt_stdPart`

English:
theorem lt_of_lt_stdPart
  given: (f : Real ->+*o K) {r : Real} (hx : 0 <= mk x) (h : r < stdPart x)
  statement: f r < x
  proof: by
  rw [← sub_lt_sub_iff_right (c := f (stdPart x))]; rw [← map_sub]
  apply lt_of_mk_lt_mk_of_nonpos
  · rw [mk_map_of_archimedean', mk_sub_pos_iff f hx]
    rw [ne_eq]; rw [sub_eq_zero]
    exact h.ne
  · simpa using f.monotone' h.le

中文:
定理 lt_of_lt_stdPart
  条件: (f : 实数 ->+*o K) {r : 实数} (hx : 0 <= mk x) (h : r < stdPart x)
  结论: f r < x
  证明: by
  rw [← sub_lt_sub_iff_right (c := f (stdPart x))]; rw [← map_sub]
  apply lt_of_mk_lt_mk_of_nonpos
  · rw [mk_map_of_archimedean', mk_sub_pos_iff f hx]
    rw [ne_eq]; rw [sub_eq_zero]
    exact h.ne
  · simpa using f.monotone' h.le

Depends on / 依赖: f.monotone, h.le, h.ne, lt_of_mk_lt_mk_of_nonpos, map_sub, mk_map_of_archimedean, mk_sub_pos_iff, monotone, ne_eq, stdPart, sub_eq_zero, sub_lt_sub_iff_right
-/
theorem lt_of_lt_stdPart (f : Real ->+*o K) {r : Real} (hx : 0 <= mk x) (h : r < stdPart x) : f r < x := by
  rw [← sub_lt_sub_iff_right (c := f (stdPart x))]; rw [← map_sub]
  apply lt_of_mk_lt_mk_of_nonpos
  · rw [mk_map_of_archimedean', mk_sub_pos_iff f hx]
    rw [ne_eq]; rw [sub_eq_zero]
    exact h.ne
  · simpa using f.monotone' h.le

/--
theorem `lt_of_stdPart_lt` / 定理 `lt_of_stdPart_lt`

English:
theorem lt_of_stdPart_lt
  given: (f : Real ->+*o K) {r : Real} (hx : 0 <= mk x) (h : stdPart x < r)
  statement: x < f r
  proof: by
  rw [← neg_lt_neg_iff]; rw [← map_neg]
  apply lt_of_lt_stdPart <;> simpa

中文:
定理 lt_of_stdPart_lt
  条件: (f : 实数 ->+*o K) {r : 实数} (hx : 0 <= mk x) (h : stdPart x < r)
  结论: x < f r
  证明: by
  rw [← neg_lt_neg_iff]; rw [← map_neg]
  apply lt_of_lt_stdPart <;> simpa

Depends on / 依赖: lt_of_lt_stdPart, map_neg, neg_lt_neg_iff
-/
theorem lt_of_stdPart_lt (f : Real ->+*o K) {r : Real} (hx : 0 <= mk x) (h : stdPart x < r) : x < f r := by
  rw [← neg_lt_neg_iff]; rw [← map_neg]
  apply lt_of_lt_stdPart <;> simpa

/--
theorem `stdPart_le_of_le` / 定理 `stdPart_le_of_le`

English:
theorem stdPart_le_of_le
  given: (f : Real ->+*o K) {r : Real} (hx : 0 <= mk x) (h : x <= f r)
  statement: stdPart x <= r
  proof: le_imp_le_iff_lt_imp_lt.2 (lt_of_lt_stdPart f hx) h

中文:
定理 stdPart_le_of_le
  条件: (f : 实数 ->+*o K) {r : 实数} (hx : 0 <= mk x) (h : x <= f r)
  结论: stdPart x <= r
  证明: le_imp_le_iff_lt_imp_lt.2 (lt_of_lt_stdPart f hx) h

Depends on / 依赖: le_imp_le_iff_lt_imp_lt, lt_of_lt_stdPart
-/
theorem stdPart_le_of_le (f : Real ->+*o K) {r : Real} (hx : 0 <= mk x) (h : x <= f r) : stdPart x <= r :=
  le_imp_le_iff_lt_imp_lt.2 (lt_of_lt_stdPart f hx) h

/--
theorem `le_stdPart_of_le` / 定理 `le_stdPart_of_le`

English:
theorem le_stdPart_of_le
  given: (f : Real ->+*o K) {r : Real} (hx : 0 <= mk x) (h : f r <= x)
  statement: r <= stdPart x
  proof: le_imp_le_iff_lt_imp_lt.2 (lt_of_stdPart_lt f hx) h

中文:
定理 le_stdPart_of_le
  条件: (f : 实数 ->+*o K) {r : 实数} (hx : 0 <= mk x) (h : f r <= x)
  结论: r <= stdPart x
  证明: le_imp_le_iff_lt_imp_lt.2 (lt_of_stdPart_lt f hx) h

Depends on / 依赖: le_imp_le_iff_lt_imp_lt, lt_of_stdPart_lt
-/
theorem le_stdPart_of_le (f : Real ->+*o K) {r : Real} (hx : 0 <= mk x) (h : f r <= x) : r <= stdPart x :=
  le_imp_le_iff_lt_imp_lt.2 (lt_of_stdPart_lt f hx) h

/--
theorem `stdPart_eq` / 定理 `stdPart_eq`

English:
theorem stdPart_eq
  given: (f : Real ->+*o K) {r : Real} (hl : forall s < r, f s <= x) (hr : forall s > r, x <= f s)
  proof: by
  have hx : 0 <= mk x := by
    apply mk_nonneg_of_le_of_le_of_archimedean f (hl (r - 1) _) (hr (r + 1) _) <;> simp
  obtain h | rfl | h := lt_trichotomy (stdPart x) r
  · obtain ⟨s, hs, hs'⟩ := exists_between h
    cases (le_stdPart_of_le f hx (hl _ hs')).not_gt hs
  · rfl
  · obtain ⟨s, hs, hs'

中文:
定理 stdPart_eq
  条件: (f : 实数 ->+*o K) {r : 实数} (hl : 对任意 s < r, f s <= x) (hr : 对任意 s > r, x <= f s)
  证明: by
  have hx : 0 <= mk x := by
    apply mk_nonneg_of_le_of_le_of_archimedean f (hl (r - 1) _) (hr (r + 1) _) <;> simp
  obtain h | rfl | h := lt_trichotomy (stdPart x) r
  · obtain ⟨s, hs, hs'⟩ := exists_between h
    cases (le_stdPart_of_le f hx (hl _ hs')).not_gt hs
  · rfl
  · obtain ⟨s, hs, hs'

Depends on / 依赖: exists_between, le_stdPart_of_le, lt_trichotomy, mk_nonneg_of_le_of_le_of_archimedean, not_gt, stdPart, stdPart_le_of_le
-/
theorem stdPart_eq (f : Real ->+*o K) {r : Real} (hl : forall s < r, f s <= x) (hr : forall s > r, x <= f s) :
    stdPart x = r := by
  have hx : 0 <= mk x := by
    apply mk_nonneg_of_le_of_le_of_archimedean f (hl (r - 1) _) (hr (r + 1) _) <;> simp
  obtain h | rfl | h := lt_trichotomy (stdPart x) r
  · obtain ⟨s, hs, hs'⟩ := exists_between h
    cases (le_stdPart_of_le f hx (hl _ hs')).not_gt hs
  · rfl
  · obtain ⟨s, hs, hs'⟩ := exists_between h
    cases (stdPart_le_of_le f hx (hr _ hs)).not_gt hs'

/--
theorem `stdPart_eq_sInf` / 定理 `stdPart_eq_sInf`

English:
theorem stdPart_eq_sInf
  given: (f : Real ->+*o K) (x : K)
  statement: stdPart x = sInf {r | x < f r}
  proof: by
  obtain hx | hx := le_or_gt 0 (mk x)
  · obtain ⟨a, ha⟩ := exists_int_lt_of_mk_nonneg hx
    obtain ⟨b, hb⟩ := exists_int_gt_of_mk_nonneg hx
    have hn : {r | x < f r}.Nonempty := ⟨b, by simpa using hb⟩
    have hb : BddBelow {r | x < f r} := by
      refine ⟨a, fun r hr => ?_⟩
      by_contra!

中文:
定理 stdPart_eq_sInf
  条件: (f : 实数 ->+*o K) (x : K)
  结论: stdPart x = sInf {r | x < f r}
  证明: by
  obtain hx | hx := le_or_gt 0 (mk x)
  · obtain ⟨a, ha⟩ := exists_int_lt_of_mk_nonneg hx
    obtain ⟨b, hb⟩ := exists_int_gt_of_mk_nonneg hx
    have hn : {r | x < f r}.Nonempty := ⟨b, by simpa using hb⟩
    have hb : BddBelow {r | x < f r} := by
      refine ⟨a, fun r hr => ?_⟩
      by_contra!

Depends on / 依赖: BddBelow, Nonempty, csInf_lt_iff, exists_int_gt_of_mk_nonneg, exists_int_lt_of_mk_nonneg, f.monotone, ha.trans, hra.le, hs.le.trans, le_or_gt, monotone, notMem_of_lt_csInf, not_gt, stdPart_eq
-/
theorem stdPart_eq_sInf (f : Real ->+*o K) (x : K) : stdPart x = sInf {r | x < f r} := by
  obtain hx | hx := le_or_gt 0 (mk x)
  · obtain ⟨a, ha⟩ := exists_int_lt_of_mk_nonneg hx
    obtain ⟨b, hb⟩ := exists_int_gt_of_mk_nonneg hx
    have hn : {r | x < f r}.Nonempty := ⟨b, by simpa using hb⟩
    have hb : BddBelow {r | x < f r} := by
      refine ⟨a, fun r hr => ?_⟩
      by_contra! hra
      exact (f.monotone' hra.le).not_gt (by simpa using ha.trans hr)
    apply stdPart_eq f <;> intro r hr
    · simpa using notMem_of_lt_csInf hr hb
    · obtain ⟨s, hs, hs'⟩ := (csInf_lt_iff hb hn).1 hr
      exact hs.le.trans (f.monotone' hs'.le)
  · rw [stdPart_of_mk_ne_zero hx.ne]
    have hr {r} := hx.trans_le (mk_map_nonneg_of_archimedean f r)
    obtain h | h := le_or_gt 0 x
    · convert! Real.sInf_empty.symm
      rw [Set.eq_empty_iff_forall_notMem]
      exact fun r => (lt_of_mk_lt_mk_of_nonneg hr h).not_gt
    · convert! Real.sInf_univ.symm
      rw [Set.eq_univ_iff_forall]
      exact fun r => lt_of_mk_lt_mk_of_nonpos hr h.le

/--
theorem `stdPart_eq_sSup` / 定理 `stdPart_eq_sSup`

English:
theorem stdPart_eq_sSup
  given: (f : Real ->+*o K) (x : K)
  statement: stdPart x = sSup {r | f r < x}
  proof: by
  rw [← neg_inj]; rw [← stdPart_neg]; rw [stdPart_eq_sInf f]; rw [← Real.sInf_neg]
  congr 1
  ext
  simp [neg_lt]

中文:
定理 stdPart_eq_sSup
  条件: (f : 实数 ->+*o K) (x : K)
  结论: stdPart x = sSup {r | f r < x}
  证明: by
  rw [← neg_inj]; rw [← stdPart_neg]; rw [stdPart_eq_sInf f]; rw [← Real.sInf_neg]
  congr 1
  ext
  simp [neg_lt]

Depends on / 依赖: Real.sInf_neg, neg_inj, neg_lt, sInf_neg, stdPart_eq_sInf, stdPart_neg
-/
theorem stdPart_eq_sSup (f : Real ->+*o K) (x : K) : stdPart x = sSup {r | f r < x} := by
  rw [← neg_inj]; rw [← stdPart_neg]; rw [stdPart_eq_sInf f]; rw [← Real.sInf_neg]
  congr 1
  ext
  simp [neg_lt]

end ArchimedeanClass
