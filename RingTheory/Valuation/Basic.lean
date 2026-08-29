/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Patrick Massot, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Range
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Ring.Torsion
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Tactic.TFAE

/-!

# The basics of valuation theory.

The basic theory of valuations (non-archimedean norms) on a commutative ring,
following T. Wedhorn's unpublished notes “Adic Spaces” ([wedhorn_adic]).

The definition of a valuation we use here is Definition 1.22 of [wedhorn_adic].
A valuation on a ring `R` is a monoid homomorphism `v` to a linearly ordered
commutative monoid with zero, that in addition satisfies the following two axioms:
* `v 0 = 0`
* `∀ x y, v (x + y) ≤ max (v x) (v y)`

`Valuation R Γ₀` is the type of valuations `R → Γ₀`, with a coercion to the underlying
function. If `v` is a valuation from `R` to `Γ₀` then the induced group
homomorphism `Units(R) → Γ₀` is called `unit_map v`.

The equivalence "relation" `IsEquiv v₁ v₂ : Prop` defined in 1.27 of [wedhorn_adic] is not strictly
speaking a relation, because `v₁ : Valuation R Γ₁` and `v₂ : Valuation R Γ₂` might
not have the same type. This corresponds in ZFC to the set-theoretic difficulty
that the class of all valuations (as `Γ₀` varies) on a ring `R` is not a set.
The "relation" is however reflexive, symmetric and transitive in the obvious
sense. Note that we use 1.27(iii) of [wedhorn_adic] as the definition of equivalence.

## Main definitions

* `Valuation R Γ₀`, the type of valuations on `R` with values in `Γ₀`
* `Valuation.IsNontrivial` is the class of non-trivial valuations, namely those for which there
  is an element in the ring whose valuation is `≠ 0` and `≠ 1`.
* `Valuation.IsEquiv`, the heterogeneous equivalence relation on valuations
* `Valuation.supp`, the support of a valuation
* `orderMonoidIso` is the ordered isomorphism between the value groups of two equivalent valuations.

* `AddValuation R Γ₀`, the type of additive valuations on `R` with values in a
  linearly ordered additive commutative group with a top element, `Γ₀`.

## Implementation Details

`AddValuation R Γ₀` is implemented as `Valuation R (Multiplicative Γ₀)ᵒᵈ`.

## Notation

In the `WithZero` locale, `Mᵐ⁰` is a shorthand for `WithZero (Multiplicative M)`.

## TODO

If ever someone extends `Valuation`, we should fully comply with `DFunLike` by migrating the
boilerplate lemmas to `ValuationClass`.
-/

@[expose] public section

open Function Ideal

noncomputable section

variable {K F R : Type*} [DivisionRing K]

section

variable (F R) (Γ₀ : Type*) [LinearOrderedCommMonoidWithZero Γ₀] [Ring R]

/--
Definition of `Valuation` / `Valuation` 的定义

English:
structure Valuation
  parameters: extends R ->*₀ Γ₀
  extends: R ->*₀ Γ₀
  axioms and operations (1):
    - map_add_le_max' : forall x y, toFun (x + y) <= max (toFun x) (toFun y)

中文:
结构 赋值
  参数: extends R ->*₀ Γ₀
  继承: R ->*₀ Γ₀
  公理与运算 (1 个):
    - map_add_le_max' : 对任意 x y, toFun (x + y) <= 最大值 (toFun x) (toFun y)
-/
structure Valuation extends R ->*₀ Γ₀ where
  /-- The valuation of a sum is less than or equal to the maximum of the valuations. -/
  map_add_le_max' : forall x y, toFun (x + y) <= max (toFun x) (toFun y)

/--
Definition of `ValuationClass` / `ValuationClass` 的定义

English:
class ValuationClass
  parameters: (F) (R Γ₀ : outParam Type*) [LinearOrderedCommMonoidWithZero Γ₀] [Ring R]
  extends: MonoidWithZeroHomClass F R Γ₀
  axioms and operations (1):
    - map_add_le_max((f : F) (x y : R)) : f (x + y) <= max (f x) (f y)

中文:
类 赋值类
  参数: (F) (R Γ₀ : outParam 类型) [带零LinearOrderedComm幺半群 Γ₀] [环 R]
  继承: 带零幺半群态射类 F R Γ₀
  公理与运算 (1 个):
    - map_add_le_max((f : F) (x y : R)) : f (x + y) <= 最大值 (f x) (f y)
-/
class ValuationClass (F) (R Γ₀ : outParam Type*) [LinearOrderedCommMonoidWithZero Γ₀] [Ring R]
    [FunLike F R Γ₀] : Prop
  extends MonoidWithZeroHomClass F R Γ₀ where
  /-- The valuation of a sum is less than or equal to the maximum of the valuations. -/
  map_add_le_max (f : F) (x y : R) : f (x + y) <= max (f x) (f y)

export ValuationClass (map_add_le_max)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FunLike
  signature: F R Γ₀] [ValuationClass F R Γ₀] : CoeTC F (Valuation R Γ₀)
  body: ⟨fun f =>
    { toFun := f
      map_one' := map_one f
      map_zero' := map_zero f
      map_mul' := map_mul f
      map_add_le_max' := map_add_le_max f }⟩

中文:
实例 [函数状
  签名: F R Γ₀] [赋值类 F R Γ₀] : CoeTC F (赋值 R Γ₀)
  定义体: ⟨fun f =>
    { toFun := f
      map_one' := map_one f
      map_zero' := map_zero f
      map_mul' := map_mul f
      map_add_le_max' := map_add_le_max f }⟩
-/
instance [FunLike F R Γ₀] [ValuationClass F R Γ₀] : CoeTC F (Valuation R Γ₀) :=
  ⟨fun f =>
    { toFun := f
      map_one' := map_one f
      map_zero' := map_zero f
      map_mul' := map_mul f
      map_add_le_max' := map_add_le_max f }⟩

end

namespace Valuation

variable {Γ₀ : Type*} {Γ'₀ : Type*} {Γ''₀ : Type*}

section Basic

variable [Ring R]

section Monoid

variable [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]
  [LinearOrderedCommMonoidWithZero Γ''₀]

/--
lemma `toMonoidWithZeroHom_injective` / 引理 `toMonoidWithZeroHom_injective`

English:
lemma toMonoidWithZeroHom_injective
  proof: by
  rintro ⟨f, _⟩ g hfg; congr!

中文:
引理 toMonoidWithZeroHom_injective
  证明: by
  rintro ⟨f, _⟩ g hfg; congr!
-/
lemma toMonoidWithZeroHom_injective :
    (toMonoidWithZeroHom : Valuation R Γ₀ -> R ->*₀ Γ₀).Injective := by
  rintro ⟨f, _⟩ g hfg; congr!

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (Valuation R Γ₀) R Γ₀
  body: f.toMonoidWithZeroHom
  coe_injective := DFunLike.coe_injective.comp toMonoidWithZeroHom_injective

中文:
实例 :
  签名: 函数状 (赋值 R Γ₀) R Γ₀
  定义体: f.toMonoidWithZeroHom
  coe_injective := DFunLike.coe_injective.comp toMonoidWithZeroHom_injective

Depends on / 依赖: f.toMonoidWithZeroHom, toMonoidWithZeroHom
-/
instance : FunLike (Valuation R Γ₀) R Γ₀ where
  coe f := f.toMonoidWithZeroHom
  coe_injective := DFunLike.coe_injective.comp toMonoidWithZeroHom_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ValuationClass (Valuation R Γ₀) R Γ₀
  body: f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'
  map_add_le_max f := f.map_add_le_max'

@[simp]

中文:
实例 :
  签名: 赋值类 (赋值 R Γ₀) R Γ₀
  定义体: f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'
  map_add_le_max f := f.map_add_le_max'

@[simp]

Depends on / 依赖: f.map_mul, map_mul
-/
instance : ValuationClass (Valuation R Γ₀) R Γ₀ where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'
  map_add_le_max f := f.map_add_le_max'

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : R ->*₀ Γ₀) (h)
  statement: ⇑(Valuation.mk f h) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : R ->*₀ Γ₀) (h)
  结论: ⇑(赋值.mk f h) = f
  证明: rfl
-/
theorem coe_mk (f : R ->*₀ Γ₀) (h) : ⇑(Valuation.mk f h) = f := rfl

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (v : Valuation R Γ₀)
  statement: v.toFun = v
  proof: rfl

@[simp]

中文:
定理 toFun_eq_coe
  条件: (v : 赋值 R Γ₀)
  结论: v.toFun = v
  证明: rfl

@[simp]
-/
theorem toFun_eq_coe (v : Valuation R Γ₀) : v.toFun = v := rfl

@[simp]
/--
theorem `toMonoidWithZeroHom_coe_eq_coe` / 定理 `toMonoidWithZeroHom_coe_eq_coe`

English:
theorem toMonoidWithZeroHom_coe_eq_coe
  given: (v : Valuation R Γ₀)
  proof: rfl

@[ext]

中文:
定理 toMonoidWithZeroHom_coe_eq_coe
  条件: (v : 赋值 R Γ₀)
  证明: rfl

@[ext]
-/
theorem toMonoidWithZeroHom_coe_eq_coe (v : Valuation R Γ₀) :
    (v.toMonoidWithZeroHom : R -> Γ₀) = v := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {v₁ v₂ : Valuation R Γ₀} (h : forall r, v₁ r = v₂ r)
  statement: v₁ = v₂
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {v₁ v₂ : 赋值 R Γ₀} (h : 对任意 r, v₁ r = v₂ r)
  结论: v₁ = v₂
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {v₁ v₂ : Valuation R Γ₀} (h : forall r, v₁ r = v₂ r) : v₁ = v₂ :=
  DFunLike.ext _ _ h

variable (v : Valuation R Γ₀)

@[simp]
/--
theorem `coe_ofClass` / 定理 `coe_ofClass`

English:
theorem coe_ofClass
  statement: ⇑(MonoidWithZeroHom.ofClass v) = v
  proof: rfl

中文:
定理 coe_ofClass
  结论: ⇑(带零幺半群态射.ofClass v) = v
  证明: rfl
-/
theorem coe_ofClass : ⇑(MonoidWithZeroHom.ofClass v) = v := rfl

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: v 0 = 0
  proof: v.map_zero'

中文:
定理 map_zero
  结论: v 0 = 0
  证明: v.map_zero'
-/
protected theorem map_zero : v 0 = 0 :=
  v.map_zero'

/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  statement: v 1 = 1
  proof: v.map_one'

中文:
定理 map_one
  结论: v 1 = 1
  证明: v.map_one'
-/
protected theorem map_one : v 1 = 1 :=
  v.map_one'

/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  statement: forall x y, v (x * y) = v x * v y
  proof: v.map_mul'

中文:
定理 map_mul
  结论: 对任意 x y, v (x * y) = v x * v y
  证明: v.map_mul'
-/
protected theorem map_mul : forall x y, v (x * y) = v x * v y :=
  v.map_mul'

-- `simp`-normal form is `map_add'`
/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  statement: forall x y, v (x + y) <= max (v x) (v y)
  proof: v.map_add_le_max'

@[simp]

中文:
定理 map_add
  结论: 对任意 x y, v (x + y) <= 最大值 (v x) (v y)
  证明: v.map_add_le_max'

@[simp]
-/
protected theorem map_add : forall x y, v (x + y) <= max (v x) (v y) :=
  v.map_add_le_max'

@[simp]
/--
theorem `map_add'` / 定理 `map_add'`

English:
theorem map_add'
  statement: forall x y, v (x + y) <= v x ∨ v (x + y) <= v y
  proof: by
  intro x y
  rw [← le_max_iff]
  apply v.map_add

中文:
定理 map_add'
  结论: 对任意 x y, v (x + y) <= v x ∨ v (x + y) <= v y
  证明: by
  intro x y
  rw [← le_max_iff]
  apply v.map_add

Depends on / 依赖: le_max_iff, map_add, v.map_add
-/
theorem map_add' : forall x y, v (x + y) <= v x ∨ v (x + y) <= v y := by
  intro x y
  rw [← le_max_iff]
  apply v.map_add

/--
theorem `map_add_le` / 定理 `map_add_le`

English:
theorem map_add_le
  given: {x y g} (hx : v x <= g) (hy : v y <= g)
  statement: v (x + y) <= g
  proof: le_trans (v.map_add x y) max_le hx hy

中文:
定理 map_add_le
  条件: {x y g} (hx : v x <= g) (hy : v y <= g)
  结论: v (x + y) <= g
  证明: le_trans (v.map_add x y) max_le hx hy

Depends on / 依赖: le_trans, map_add, max_le, v.map_add
-/
theorem map_add_le {x y g} (hx : v x <= g) (hy : v y <= g) : v (x + y) <= g :=
le_trans (v.map_add x y) max_le hx hy

/--
theorem `map_add_lt` / 定理 `map_add_lt`

English:
theorem map_add_lt
  given: {x y g} (hx : v x < g) (hy : v y < g)
  statement: v (x + y) < g
  proof: lt_of_le_of_lt (v.map_add x y) max_lt hx hy

中文:
定理 map_add_lt
  条件: {x y g} (hx : v x < g) (hy : v y < g)
  结论: v (x + y) < g
  证明: lt_of_le_of_lt (v.map_add x y) max_lt hx hy

Depends on / 依赖: lt_of_le_of_lt, map_add, max_lt, v.map_add
-/
theorem map_add_lt {x y g} (hx : v x < g) (hy : v y < g) : v (x + y) < g :=
lt_of_le_of_lt (v.map_add x y) max_lt hx hy

/--
theorem `map_sum_le` / 定理 `map_sum_le`

English:
theorem map_sum_le
  given: {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hf : forall i in s, v (f i) <= g)
  proof: by
  classical
  refine Finset.induction_on s (fun _ => v.map_zero ▸ zero_le) (fun a s has ih hf => ?_) hf
  rw [Finset.forall_mem_insert] at hf; rw [Finset.sum_insert has]
  exact v.map_add_le hf.1 (ih hf.2)

中文:
定理 map_sum_le
  条件: {ι : 类型} {s : 有限集 ι} {f : ι -> R} {g : Γ₀} (hf : 对任意 i in s, v (f i) <= g)
  证明: by
  classical
  refine Finset.induction_on s (fun _ => v.map_zero ▸ zero_le) (fun a s has ih hf => ?_) hf
  rw [Finset.forall_mem_insert] at hf; rw [Finset.sum_insert has]
  exact v.map_add_le hf.1 (ih hf.2)

Depends on / 依赖: Finset, Finset.forall_mem_insert, Finset.induction_on, Finset.sum_insert, classical, forall_mem_insert, induction_on, map_add_le, map_zero, sum_insert, v.map_add_le, v.map_zero, zero_le
-/
theorem map_sum_le {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hf : forall i in s, v (f i) <= g) :
    v (∑ i in s, f i) <= g := by
  classical
  refine Finset.induction_on s (fun _ => v.map_zero ▸ zero_le) (fun a s has ih hf => ?_) hf
  rw [Finset.forall_mem_insert] at hf; rw [Finset.sum_insert has]
  exact v.map_add_le hf.1 (ih hf.2)

/--
theorem `map_sum_lt` / 定理 `map_sum_lt`

English:
theorem map_sum_lt
  statement: {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hg : g != 0)
  proof: by
  classical
  refine
    Finset.induction_on s (fun _ => v.map_zero ▸ (zero_lt_iff.2 hg))
      (fun a s has ih hf => ?_) hf
  rw [Finset.forall_mem_insert] at hf; rw [Finset.sum_insert has]
  exact v.map_add_lt hf.1 (ih hf.2)

中文:
定理 map_sum_lt
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> R} {g : Γ₀} (hg : g != 0)
  证明: by
  classical
  refine
    Finset.induction_on s (fun _ => v.map_zero ▸ (zero_lt_iff.2 hg))
      (fun a s has ih hf => ?_) hf
  rw [Finset.forall_mem_insert] at hf; rw [Finset.sum_insert has]
  exact v.map_add_lt hf.1 (ih hf.2)

Depends on / 依赖: Finset, Finset.forall_mem_insert, Finset.induction_on, Finset.sum_insert, classical, forall_mem_insert, induction_on, map_add_lt, map_zero, sum_insert, v.map_add_lt, v.map_zero, zero_lt_iff
-/
theorem map_sum_lt {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hg : g != 0)
    (hf : forall i in s, v (f i) < g) : v (∑ i in s, f i) < g := by
  classical
  refine
    Finset.induction_on s (fun _ => v.map_zero ▸ (zero_lt_iff.2 hg))
      (fun a s has ih hf => ?_) hf
  rw [Finset.forall_mem_insert] at hf; rw [Finset.sum_insert has]
  exact v.map_add_lt hf.1 (ih hf.2)

/--
theorem `map_sum_lt'` / 定理 `map_sum_lt'`

English:
theorem map_sum_lt'
  statement: {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hg : 0 < g)
  proof: v.map_sum_lt (ne_of_gt hg) hf

中文:
定理 map_sum_lt'
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> R} {g : Γ₀} (hg : 0 < g)
  证明: v.map_sum_lt (ne_of_gt hg) hf

Depends on / 依赖: map_sum_lt, ne_of_gt, v.map_sum_lt
-/
theorem map_sum_lt' {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hg : 0 < g)
    (hf : forall i in s, v (f i) < g) : v (∑ i in s, f i) < g :=
  v.map_sum_lt (ne_of_gt hg) hf

/--
theorem `map_pow` / 定理 `map_pow`

English:
theorem map_pow
  statement: forall (x) (n : Nat), v (x ^ n) = v x ^ n
  proof: v.toMonoidWithZeroHom.toMonoidHom.map_pow

中文:
定理 map_pow
  结论: 对任意 (x) (n : 自然数), v (x ^ n) = v x ^ n
  证明: v.toMonoidWithZeroHom.toMonoidHom.map_pow

Depends on / 依赖: Y.property, property
-/
protected theorem map_pow : forall (x) (n : Nat), v (x ^ n) = v x ^ n :=
  v.toMonoidWithZeroHom.toMonoidHom.map_pow

-- The following definition is not an instance, because we have more than one `v` on a given `R`.
-- In addition, type class inference would not be able to infer `v`.
/-- A valuation gives a preorder on the underlying ring. -/
@[instance_reducible]
/--
Definition of `toPreorder` / `toPreorder` 的定义

English:
definition toPreorder
  signature: : Preorder R
  body: Preorder.lift v

中文:
定义 toPreorder
  签名: : 预序 R
  定义体: Preorder.lift v

Depends on / 依赖: Preorder, Preorder.lift
-/
def toPreorder : Preorder R :=
  Preorder.lift v

/--
theorem `zero_iff` / 定理 `zero_iff`

English:
theorem zero_iff
  given: [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K}
  statement: v x = 0 ↔ x = 0
  proof: map_eq_zero v

中文:
定理 zero_iff
  条件: [非平凡 Γ₀] (v : 赋值 K Γ₀) {x : K}
  结论: v x = 0 ↔ x = 0
  证明: map_eq_zero v

Depends on / 依赖: map_eq_zero
-/
theorem zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} : v x = 0 ↔ x = 0 :=
  map_eq_zero v

/--
theorem `ne_zero_iff` / 定理 `ne_zero_iff`

English:
theorem ne_zero_iff
  given: [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K}
  statement: v x != 0 ↔ x != 0
  proof: map_ne_zero v

中文:
定理 ne_zero_iff
  条件: [非平凡 Γ₀] (v : 赋值 K Γ₀) {x : K}
  结论: v x != 0 ↔ x != 0
  证明: map_ne_zero v

Depends on / 依赖: map_ne_zero
-/
theorem ne_zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} : v x != 0 ↔ x != 0 :=
  map_ne_zero v

/--
lemma `pos_iff` / 引理 `pos_iff`

English:
lemma pos_iff
  given: [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K}
  statement: 0 < v x ↔ x != 0
  proof: by
  rw [zero_lt_iff]; rw [ne_zero_iff]

中文:
引理 pos_iff
  条件: [非平凡 Γ₀] (v : 赋值 K Γ₀) {x : K}
  结论: 0 < v x ↔ x != 0
  证明: by
  rw [zero_lt_iff]; rw [ne_zero_iff]

Depends on / 依赖: Y.property, ne_zero_iff, property, zero_lt_iff
-/
lemma pos_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} : 0 < v x ↔ x != 0 := by
  rw [zero_lt_iff]; rw [ne_zero_iff]

/--
theorem `unit_map_eq` / 定理 `unit_map_eq`

English:
theorem unit_map_eq
  given: (u : Rˣ)
  statement: (Units.map (v : R ->* Γ₀) u : Γ₀) = v u
  proof: rfl

中文:
定理 unit_map_eq
  条件: (u : Rˣ)
  结论: (单位群.map (v : R ->* Γ₀) u : Γ₀) = v u
  证明: rfl
-/
theorem unit_map_eq (u : Rˣ) : (Units.map (v : R ->* Γ₀) u : Γ₀) = v u :=
  rfl

/--
theorem `ne_zero_of_unit` / 定理 `ne_zero_of_unit`

English:
theorem ne_zero_of_unit
  given: [Nontrivial Γ₀] (v : Valuation K Γ₀) (x : Kˣ)
  statement: v x != (0 : Γ₀)
  proof: by
  simp only [ne_eq, Valuation.zero_iff, Units.ne_zero x, not_false_iff]

中文:
定理 ne_zero_of_unit
  条件: [非平凡 Γ₀] (v : 赋值 K Γ₀) (x : Kˣ)
  结论: v x != (0 : Γ₀)
  证明: by
  simp only [ne_eq, Valuation.zero_iff, Units.ne_zero x, not_false_iff]

Depends on / 依赖: Units.ne_zero, Valuation, Valuation.zero_iff, ne_eq, ne_zero, not_false_iff, zero_iff
-/
theorem ne_zero_of_unit [Nontrivial Γ₀] (v : Valuation K Γ₀) (x : Kˣ) : v x != (0 : Γ₀) := by
  simp only [ne_eq, Valuation.zero_iff, Units.ne_zero x, not_false_iff]

/--
theorem `ne_zero_of_isUnit` / 定理 `ne_zero_of_isUnit`

English:
theorem ne_zero_of_isUnit
  given: [Nontrivial Γ₀] (v : Valuation K Γ₀) (x : K) (hx : IsUnit x)
  proof: by
  simpa [hx.choose_spec] using ne_zero_of_unit v hx.choose

中文:
定理 ne_zero_of_isUnit
  条件: [非平凡 Γ₀] (v : 赋值 K Γ₀) (x : K) (hx : 是单位 x)
  证明: by
  simpa [hx.choose_spec] using ne_zero_of_unit v hx.choose

Depends on / 依赖: choose_spec, hx.choose, hx.choose_spec, ne_zero_of_unit
-/
theorem ne_zero_of_isUnit [Nontrivial Γ₀] (v : Valuation K Γ₀) (x : K) (hx : IsUnit x) :
    v x != (0 : Γ₀) := by
  simpa [hx.choose_spec] using ne_zero_of_unit v hx.choose

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: {S : Type*} [Ring S] (f : S ->+* R) (v : Valuation R Γ₀)
  body: { v.toMonoidWithZeroHom.comp f.toMonoidWithZeroHom with
    toFun := v ∘ f
    map_add_le_max' := fun x y => by simp }

@[simp]

中文:
定义 comap
  签名: {S : 类型} [环 S] (f : S ->+* R) (v : 赋值 R Γ₀)
  定义体: { v.toMonoidWithZeroHom.comp f.toMonoidWithZeroHom with
    toFun := v ∘ f
    map_add_le_max' := fun x y => by simp }

@[simp]

Depends on / 依赖: f.toMonoidWithZeroHom, map_add_le_max, toMonoidWithZeroHom, v.toMonoidWithZeroHom.comp
-/
def comap {S : Type*} [Ring S] (f : S ->+* R) (v : Valuation R Γ₀) : Valuation S Γ₀ :=
  { v.toMonoidWithZeroHom.comp f.toMonoidWithZeroHom with
    toFun := v ∘ f
    map_add_le_max' := fun x y => by simp }

@[simp]
/--
theorem `comap_apply` / 定理 `comap_apply`

English:
theorem comap_apply
  given: {S : Type*} [Ring S] (f : S ->+* R) (v : Valuation R Γ₀) (s : S)
  proof: rfl

@[simp]

中文:
定理 comap_apply
  条件: {S : 类型} [环 S] (f : S ->+* R) (v : 赋值 R Γ₀) (s : S)
  证明: rfl

@[simp]
-/
theorem comap_apply {S : Type*} [Ring S] (f : S ->+* R) (v : Valuation R Γ₀) (s : S) :
    v.comap f s = v (f s) := rfl

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  statement: v.comap (RingHom.id R) = v
  proof: ext fun _r => rfl

中文:
定理 comap_id
  结论: v.comap (环态射.id R) = v
  证明: ext fun _r => rfl
-/
theorem comap_id : v.comap (RingHom.id R) = v :=
  ext fun _r => rfl

/--
theorem `comap_comp` / 定理 `comap_comp`

English:
theorem comap_comp
  given: {S₁ : Type*} {S₂ : Type*} [Ring S₁] [Ring S₂] (f : S₁ ->+* S₂) (g : S₂ ->+* R)
  proof: ext fun _r => rfl

中文:
定理 comap_comp
  条件: {S₁ : 类型} {S₂ : 类型} [环 S₁] [环 S₂] (f : S₁ ->+* S₂) (g : S₂ ->+* R)
  证明: ext fun _r => rfl
-/
theorem comap_comp {S₁ : Type*} {S₂ : Type*} [Ring S₁] [Ring S₂] (f : S₁ ->+* S₂) (g : S₂ ->+* R) :
    v.comap (g.comp f) = (v.comap g).comap f :=
  ext fun _r => rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : Γ₀ ->*₀ Γ'₀) (hf : Monotone f) (v : Valuation R Γ₀)
  body: { MonoidWithZeroHom.comp f v.toMonoidWithZeroHom with
    toFun := f ∘ v
    map_add_le_max' := fun r s =>
      calc
        f (v (r + s)) <= f (max (v r) (v s)) := hf (v.map_add r s)
        _ = max (f (v r)) (f (v s)) := hf.map_max
         }

@[simp]

中文:
定义 map
  签名: (f : Γ₀ ->*₀ Γ'₀) (hf : 递增 f) (v : 赋值 R Γ₀)
  定义体: { MonoidWithZeroHom.comp f v.toMonoidWithZeroHom with
    toFun := f ∘ v
    map_add_le_max' := fun r s =>
      calc
        f (v (r + s)) <= f (max (v r) (v s)) := hf (v.map_add r s)
        _ = max (f (v r)) (f (v s)) := hf.map_max
         }

@[simp]

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.comp, hf.map_max, map_add, map_add_le_max, map_max, toMonoidWithZeroHom, v.map_add, v.toMonoidWithZeroHom
-/
def map (f : Γ₀ ->*₀ Γ'₀) (hf : Monotone f) (v : Valuation R Γ₀) : Valuation R Γ'₀ :=
  { MonoidWithZeroHom.comp f v.toMonoidWithZeroHom with
    toFun := f ∘ v
    map_add_le_max' := fun r s =>
      calc
        f (v (r + s)) <= f (max (v r) (v s)) := hf (v.map_add r s)
        _ = max (f (v r)) (f (v s)) := hf.map_max
         }

@[simp]
/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  given: (f : Γ₀ ->*₀ Γ'₀) (hf : Monotone f) (v : Valuation R Γ₀) (r : R)
  proof: rfl

中文:
引理 map_apply
  条件: (f : Γ₀ ->*₀ Γ'₀) (hf : 递增 f) (v : 赋值 R Γ₀) (r : R)
  证明: rfl
-/
lemma map_apply (f : Γ₀ ->*₀ Γ'₀) (hf : Monotone f) (v : Valuation R Γ₀) (r : R) :
    v.map f hf r = f (v r) := rfl

/--
Definition of `IsEquiv` / `IsEquiv` 的定义

English:
definition IsEquiv
  signature: (v₁ : Valuation R Γ₀) (v₂ : Valuation R Γ'₀)
  body: forall r s, v₁ r <= v₁ s ↔ v₂ r <= v₂ s

@[simp]

中文:
定义 Is等价
  签名: (v₁ : 赋值 R Γ₀) (v₂ : 赋值 R Γ'₀)
  定义体: forall r s, v₁ r <= v₁ s ↔ v₂ r <= v₂ s

@[simp]
-/
def IsEquiv (v₁ : Valuation R Γ₀) (v₂ : Valuation R Γ'₀) : Prop :=
  forall r s, v₁ r <= v₁ s ↔ v₂ r <= v₂ s

@[simp]
/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: (x : R)
  statement: v (-x) = v x
  proof: v.toMonoidWithZeroHom.toMonoidHom.map_neg x

中文:
定理 map_neg
  条件: (x : R)
  结论: v (-x) = v x
  证明: v.toMonoidWithZeroHom.toMonoidHom.map_neg x

Depends on / 依赖: map_neg, toMonoidHom, toMonoidWithZeroHom, v.toMonoidWithZeroHom.toMonoidHom.map_neg
-/
theorem map_neg (x : R) : v (-x) = v x :=
  v.toMonoidWithZeroHom.toMonoidHom.map_neg x

/--
theorem `map_sub_swap` / 定理 `map_sub_swap`

English:
theorem map_sub_swap
  given: (x y : R)
  statement: v (x - y) = v (y - x)
  proof: v.toMonoidWithZeroHom.toMonoidHom.map_sub_swap x y

中文:
定理 map_sub_swap
  条件: (x y : R)
  结论: v (x - y) = v (y - x)
  证明: v.toMonoidWithZeroHom.toMonoidHom.map_sub_swap x y

Depends on / 依赖: map_sub_swap, toMonoidHom, toMonoidWithZeroHom, v.toMonoidWithZeroHom.toMonoidHom.map_sub_swap
-/
theorem map_sub_swap (x y : R) : v (x - y) = v (y - x) :=
  v.toMonoidWithZeroHom.toMonoidHom.map_sub_swap x y

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (x y : R)
  statement: v (x - y) <= max (v x) (v y)
  proof: calc
    v (x - y) = v (x + -y) := by rw [sub_eq_add_neg]
    _ <= max (v x) (v <| -y) := v.map_add _ _
    _ = max (v x) (v y) := by rw [map_neg]

中文:
定理 map_sub
  条件: (x y : R)
  结论: v (x - y) <= 最大值 (v x) (v y)
  证明: calc
    v (x - y) = v (x + -y) := by rw [sub_eq_add_neg]
    _ <= max (v x) (v <| -y) := v.map_add _ _
    _ = max (v x) (v y) := by rw [map_neg]

Depends on / 依赖: map_add, map_neg, sub_eq_add_neg, v.map_add
-/
theorem map_sub (x y : R) : v (x - y) <= max (v x) (v y) :=
  calc
    v (x - y) = v (x + -y) := by rw [sub_eq_add_neg]
    _ <= max (v x) (v <| -y) := v.map_add _ _
    _ = max (v x) (v y) := by rw [map_neg]

/--
theorem `map_sub_le` / 定理 `map_sub_le`

English:
theorem map_sub_le
  given: {x y g} (hx : v x <= g) (hy : v y <= g)
  statement: v (x - y) <= g
  proof: by
  rw [sub_eq_add_neg]
exact v.map_add_le hx (v.map_neg y).trans_le hy

中文:
定理 map_sub_le
  条件: {x y g} (hx : v x <= g) (hy : v y <= g)
  结论: v (x - y) <= g
  证明: by
  rw [sub_eq_add_neg]
exact v.map_add_le hx (v.map_neg y).trans_le hy

Depends on / 依赖: map_add_le, map_neg, sub_eq_add_neg, trans_le, v.map_add_le, v.map_neg
-/
theorem map_sub_le {x y g} (hx : v x <= g) (hy : v y <= g) : v (x - y) <= g := by
  rw [sub_eq_add_neg]
exact v.map_add_le hx (v.map_neg y).trans_le hy

/--
theorem `map_sub_lt` / 定理 `map_sub_lt`

English:
theorem map_sub_lt
  given: {x y : R} {g : Γ₀} (hx : v x < g) (hy : v y < g)
  statement: v (x - y) < g
  proof: by
  rw [sub_eq_add_neg]
exact v.map_add_lt hx (v.map_neg y).trans_lt hy

中文:
定理 map_sub_lt
  条件: {x y : R} {g : Γ₀} (hx : v x < g) (hy : v y < g)
  结论: v (x - y) < g
  证明: by
  rw [sub_eq_add_neg]
exact v.map_add_lt hx (v.map_neg y).trans_lt hy

Depends on / 依赖: map_add_lt, map_neg, sub_eq_add_neg, trans_lt, v.map_add_lt, v.map_neg
-/
theorem map_sub_lt {x y : R} {g : Γ₀} (hx : v x < g) (hy : v y < g) : v (x - y) < g := by
  rw [sub_eq_add_neg]
exact v.map_add_lt hx (v.map_neg y).trans_lt hy

variable {x y : R}

@[simp]
/--
lemma `le_one_of_subsingleton` / 引理 `le_one_of_subsingleton`

English:
lemma le_one_of_subsingleton
  given: [Subsingleton R] (v : Valuation R Γ₀) {x : R}
  proof: by
  rw [Subsingleton.elim x 1]; rw [Valuation.map_one]

中文:
引理 le_one_of_subsingleton
  条件: [子单例 R] (v : 赋值 R Γ₀) {x : R}
  证明: by
  rw [Subsingleton.elim x 1]; rw [Valuation.map_one]

Depends on / 依赖: Subsingleton, Subsingleton.elim, Valuation, Valuation.map_one, map_one
-/
lemma le_one_of_subsingleton [Subsingleton R] (v : Valuation R Γ₀) {x : R} :
    v x <= 1 := by
  rw [Subsingleton.elim x 1]; rw [Valuation.map_one]

/--
theorem `map_add_of_distinct_val` / 定理 `map_add_of_distinct_val`

English:
theorem map_add_of_distinct_val
  given: (h : v x != v y)
  statement: v (x + y) = max (v x) (v y)
  proof: by
  suffices ¬v (x + y) < max (v x) (v y) from
    or_iff_not_imp_right.1 (le_iff_eq_or_lt.1 (v.map_add x y)) this
  intro h'
  wlog vyx : v y < v x generalizing x y
  · refine this h.symm ?_ (h.lt_or_gt.resolve_right vyx)
    rwa [add_comm, max_comm]
  rw [max_eq_left_of_lt vyx] at h'
  apply lt_irrefl (v x)
  calc
    v x = v (x + y - y) := by simp
    _ <= max (v <| x + y) (v y) := map_sub _ _ _
    _ < v x := max_lt h' vyx

中文:
定理 map_add_of_distinct_val
  条件: (h : v x != v y)
  结论: v (x + y) = 最大值 (v x) (v y)
  证明: by
  suffices ¬v (x + y) < max (v x) (v y) from
    or_iff_not_imp_right.1 (le_iff_eq_or_lt.1 (v.map_add x y)) this
  intro h'
  wlog vyx : v y < v x generalizing x y
  · refine this h.symm ?_ (h.lt_or_gt.resolve_right vyx)
    rwa [add_comm, max_comm]
  rw [max_eq_left_of_lt vyx] at h'
  apply lt_irrefl (v x)
  calc
    v x = v (x + y - y) := by simp
    _ <= max (v <| x + y) (v y) := map_sub _ _ _
    _ < v x := max_lt h' vyx

Depends on / 依赖: add_comm, generalizing, h.lt_or_gt.resolve_right, h.symm, le_iff_eq_or_lt, lt_irrefl, lt_or_gt, map_add, map_sub, max_comm, max_eq_left_of_lt, max_lt, or_iff_not_imp_right, resolve_right, v.map_add
-/
theorem map_add_of_distinct_val (h : v x != v y) : v (x + y) = max (v x) (v y) := by
  suffices ¬v (x + y) < max (v x) (v y) from
    or_iff_not_imp_right.1 (le_iff_eq_or_lt.1 (v.map_add x y)) this
  intro h'
  wlog vyx : v y < v x generalizing x y
  · refine this h.symm ?_ (h.lt_or_gt.resolve_right vyx)
    rwa [add_comm, max_comm]
  rw [max_eq_left_of_lt vyx] at h'
  apply lt_irrefl (v x)
  calc
    v x = v (x + y - y) := by simp
    _ <= max (v <| x + y) (v y) := map_sub _ _ _
    _ < v x := max_lt h' vyx

/--
theorem `map_add_eq_of_lt_right` / 定理 `map_add_eq_of_lt_right`

English:
theorem map_add_eq_of_lt_right
  given: (h : v x < v y)
  statement: v (x + y) = v y
  proof: (v.map_add_of_distinct_val h.ne).trans (max_eq_right_iff.mpr h.le)

中文:
定理 map_add_eq_of_lt_right
  条件: (h : v x < v y)
  结论: v (x + y) = v y
  证明: (v.map_add_of_distinct_val h.ne).trans (max_eq_right_iff.mpr h.le)

Depends on / 依赖: h.le, h.ne, map_add_of_distinct_val, max_eq_right_iff, max_eq_right_iff.mpr, v.map_add_of_distinct_val
-/
theorem map_add_eq_of_lt_right (h : v x < v y) : v (x + y) = v y :=
  (v.map_add_of_distinct_val h.ne).trans (max_eq_right_iff.mpr h.le)

/--
theorem `map_add_eq_of_lt_left` / 定理 `map_add_eq_of_lt_left`

English:
theorem map_add_eq_of_lt_left
  given: (h : v y < v x)
  statement: v (x + y) = v x
  proof: by
  rw [add_comm]; exact map_add_eq_of_lt_right _ h

中文:
定理 map_add_eq_of_lt_left
  条件: (h : v y < v x)
  结论: v (x + y) = v x
  证明: by
  rw [add_comm]; exact map_add_eq_of_lt_right _ h

Depends on / 依赖: add_comm, map_add_eq_of_lt_right
-/
theorem map_add_eq_of_lt_left (h : v y < v x) : v (x + y) = v x := by
  rw [add_comm]; exact map_add_eq_of_lt_right _ h

/--
theorem `map_sub_eq_of_lt_right` / 定理 `map_sub_eq_of_lt_right`

English:
theorem map_sub_eq_of_lt_right
  given: (h : v x < v y)
  statement: v (x - y) = v y
  proof: by
  rw [sub_eq_add_neg]; rw [map_add_eq_of_lt_right]; rw [map_neg]
  rwa [map_neg]

中文:
定理 map_sub_eq_of_lt_right
  条件: (h : v x < v y)
  结论: v (x - y) = v y
  证明: by
  rw [sub_eq_add_neg]; rw [map_add_eq_of_lt_right]; rw [map_neg]
  rwa [map_neg]

Depends on / 依赖: map_add_eq_of_lt_right, map_neg, sub_eq_add_neg
-/
theorem map_sub_eq_of_lt_right (h : v x < v y) : v (x - y) = v y := by
  rw [sub_eq_add_neg]; rw [map_add_eq_of_lt_right]; rw [map_neg]
  rwa [map_neg]

/--
theorem `map_sum_eq_of_lt` / 定理 `map_sum_eq_of_lt`

English:
theorem map_sum_eq_of_lt
  statement: {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι -> R} {j : ι}
  proof: by
  rcases eq_or_ne (v (f j)) 0 with h0 | h0
  · aesop
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hj]
  exact map_add_eq_of_lt_left _ (map_sum_lt _ h0 hf)

中文:
定理 map_sum_eq_of_lt
  结论: {ι : 类型} [DecidableEq ι] {s : 有限集 ι} {f : ι -> R} {j : ι}
  证明: by
  rcases eq_or_ne (v (f j)) 0 with h0 | h0
  · aesop
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hj]
  exact map_add_eq_of_lt_left _ (map_sum_lt _ h0 hf)

Depends on / 依赖: Finset, Finset.sum_eq_add_sum_sdiff_singleton_of_mem, eq_or_ne, map_add_eq_of_lt_left, map_sum_lt, sum_eq_add_sum_sdiff_singleton_of_mem
-/
theorem map_sum_eq_of_lt {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι -> R} {j : ι}
    (hj : j in s) (hf : forall i in s \ {j}, v (f i) < v (f j)) :
    v (∑ i in s, f i) = v (f j) := by
  rcases eq_or_ne (v (f j)) 0 with h0 | h0
  · aesop
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hj]
  exact map_add_eq_of_lt_left _ (map_sum_lt _ h0 hf)

/--
theorem `map_sub_eq_of_lt_left` / 定理 `map_sub_eq_of_lt_left`

English:
theorem map_sub_eq_of_lt_left
  given: (h : v y < v x)
  statement: v (x - y) = v x
  proof: by
  rw [sub_eq_add_neg]; rw [map_add_eq_of_lt_left]
  rwa [map_neg]

中文:
定理 map_sub_eq_of_lt_left
  条件: (h : v y < v x)
  结论: v (x - y) = v x
  证明: by
  rw [sub_eq_add_neg]; rw [map_add_eq_of_lt_left]
  rwa [map_neg]

Depends on / 依赖: map_add_eq_of_lt_left, map_neg, sub_eq_add_neg
-/
theorem map_sub_eq_of_lt_left (h : v y < v x) : v (x - y) = v x := by
  rw [sub_eq_add_neg]; rw [map_add_eq_of_lt_left]
  rwa [map_neg]

/--
theorem `map_eq_of_sub_lt` / 定理 `map_eq_of_sub_lt`

English:
theorem map_eq_of_sub_lt
  given: (h : v (y - x) < v x)
  statement: v y = v x
  proof: by
  have := Valuation.map_add_of_distinct_val v (ne_of_gt h).symm
  rw [max_eq_right (le_of_lt h)] at this
  simpa using this

中文:
定理 map_eq_of_sub_lt
  条件: (h : v (y - x) < v x)
  结论: v y = v x
  证明: by
  have := Valuation.map_add_of_distinct_val v (ne_of_gt h).symm
  rw [max_eq_right (le_of_lt h)] at this
  simpa using this

Depends on / 依赖: Valuation, Valuation.map_add_of_distinct_val, le_of_lt, map_add_of_distinct_val, max_eq_right, ne_of_gt
-/
theorem map_eq_of_sub_lt (h : v (y - x) < v x) : v y = v x := by
  have := Valuation.map_add_of_distinct_val v (ne_of_gt h).symm
  rw [max_eq_right (le_of_lt h)] at this
  simpa using this

/--
lemma `map_sub_of_left_eq_zero` / 引理 `map_sub_of_left_eq_zero`

English:
lemma map_sub_of_left_eq_zero
  given: (hx : v x = 0)
  statement: v (x - y) = v y
  proof: by
  by_cases hy : v y = 0
  · simpa [*] using map_sub v x y
  · simp [*, map_sub_eq_of_lt_right, zero_lt_iff]

中文:
引理 map_sub_of_left_eq_zero
  条件: (hx : v x = 0)
  结论: v (x - y) = v y
  证明: by
  by_cases hy : v y = 0
  · simpa [*] using map_sub v x y
  · simp [*, map_sub_eq_of_lt_right, zero_lt_iff]

Depends on / 依赖: map_sub, map_sub_eq_of_lt_right, zero_lt_iff
-/
lemma map_sub_of_left_eq_zero (hx : v x = 0) : v (x - y) = v y := by
  by_cases hy : v y = 0
  · simpa [*] using map_sub v x y
  · simp [*, map_sub_eq_of_lt_right, zero_lt_iff]

/--
lemma `map_sub_of_right_eq_zero` / 引理 `map_sub_of_right_eq_zero`

English:
lemma map_sub_of_right_eq_zero
  given: (hy : v y = 0)
  statement: v (x - y) = v x
  proof: by
  rw [map_sub_swap]; rw [map_sub_of_left_eq_zero v hy]

中文:
引理 map_sub_of_right_eq_zero
  条件: (hy : v y = 0)
  结论: v (x - y) = v x
  证明: by
  rw [map_sub_swap]; rw [map_sub_of_left_eq_zero v hy]

Depends on / 依赖: map_sub_of_left_eq_zero, map_sub_swap
-/
lemma map_sub_of_right_eq_zero (hy : v y = 0) : v (x - y) = v x := by
  rw [map_sub_swap]; rw [map_sub_of_left_eq_zero v hy]

/--
lemma `map_add_of_left_eq_zero` / 引理 `map_add_of_left_eq_zero`

English:
lemma map_add_of_left_eq_zero
  given: (hx : v x = 0)
  statement: v (x + y) = v y
  proof: by
  rw [← sub_neg_eq_add]; rw [map_sub_of_left_eq_zero v hx]; rw [map_neg]

中文:
引理 map_add_of_left_eq_zero
  条件: (hx : v x = 0)
  结论: v (x + y) = v y
  证明: by
  rw [← sub_neg_eq_add]; rw [map_sub_of_left_eq_zero v hx]; rw [map_neg]

Depends on / 依赖: map_neg, map_sub_of_left_eq_zero, sub_neg_eq_add
-/
lemma map_add_of_left_eq_zero (hx : v x = 0) : v (x + y) = v y := by
  rw [← sub_neg_eq_add]; rw [map_sub_of_left_eq_zero v hx]; rw [map_neg]

/--
lemma `map_add_of_right_eq_zero` / 引理 `map_add_of_right_eq_zero`

English:
lemma map_add_of_right_eq_zero
  given: (hy : v y = 0)
  statement: v (x + y) = v x
  proof: by
  rw [add_comm]; rw [map_add_of_left_eq_zero v hy]

中文:
引理 map_add_of_right_eq_zero
  条件: (hy : v y = 0)
  结论: v (x + y) = v x
  证明: by
  rw [add_comm]; rw [map_add_of_left_eq_zero v hy]

Depends on / 依赖: add_comm, map_add_of_left_eq_zero
-/
lemma map_add_of_right_eq_zero (hy : v y = 0) : v (x + y) = v x := by
  rw [add_comm]; rw [map_add_of_left_eq_zero v hy]

/--
theorem `map_one_add_of_lt` / 定理 `map_one_add_of_lt`

English:
theorem map_one_add_of_lt
  given: (h : v x < 1)
  statement: v (1 + x) = 1
  proof: by
  rw [← v.map_one] at h
  simpa only [v.map_one] using v.map_add_eq_of_lt_left h

中文:
定理 map_one_add_of_lt
  条件: (h : v x < 1)
  结论: v (1 + x) = 1
  证明: by
  rw [← v.map_one] at h
  simpa only [v.map_one] using v.map_add_eq_of_lt_left h

Depends on / 依赖: map_add_eq_of_lt_left, map_one, v.map_add_eq_of_lt_left, v.map_one
-/
theorem map_one_add_of_lt (h : v x < 1) : v (1 + x) = 1 := by
  rw [← v.map_one] at h
  simpa only [v.map_one] using v.map_add_eq_of_lt_left h

/--
theorem `map_one_sub_of_lt` / 定理 `map_one_sub_of_lt`

English:
theorem map_one_sub_of_lt
  given: (h : v x < 1)
  statement: v (1 - x) = 1
  proof: by
  rw [← v.map_one]; rw [← v.map_neg] at h
  rw [sub_eq_add_neg 1 x]
  simpa only [v.map_one, v.map_neg] using v.map_add_eq_of_lt_left h

中文:
定理 map_one_sub_of_lt
  条件: (h : v x < 1)
  结论: v (1 - x) = 1
  证明: by
  rw [← v.map_one]; rw [← v.map_neg] at h
  rw [sub_eq_add_neg 1 x]
  simpa only [v.map_one, v.map_neg] using v.map_add_eq_of_lt_left h

Depends on / 依赖: map_add_eq_of_lt_left, map_neg, map_one, sub_eq_add_neg, v.map_add_eq_of_lt_left, v.map_neg, v.map_one
-/
theorem map_one_sub_of_lt (h : v x < 1) : v (1 - x) = 1 := by
  rw [← v.map_one]; rw [← v.map_neg] at h
  rw [sub_eq_add_neg 1 x]
  simpa only [v.map_one, v.map_neg] using v.map_add_eq_of_lt_left h

/--
lemma `OrderMonoidWithZeroHom.ofClass_monotone` / 引理 `OrderMonoidWithZeroHom.ofClass_monotone`

English:
lemma OrderMonoidWithZeroHom.ofClass_monotone
  statement: {F : Type u_1} {α : Type u_2} {β : Type u_3}
  proof: hf

中文:
引理 带零Order幺半群态射.ofClass_monotone
  结论: {F : 类型u_1} {α : 类型u_2} {β : 类型u_3}
  证明: hf
-/
lemma OrderMonoidWithZeroHom.ofClass_monotone {F : Type u_1} {α : Type u_2} {β : Type u_3}
    [LinearOrderedCommMonoidWithZero α] [LinearOrderedCommMonoidWithZero β] [FunLike F α β]
    [MonoidWithZeroHomClass F α β] {f : F} (hf : Monotone f) :
    Monotone (MonoidWithZeroHom.ofClass f) := hf

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (f : Γ₀ ≃*o Γ'₀)
  body: map (.ofClass f) (OrderMonoidWithZeroHom.ofClass_monotone f.toOrderIso.monotone)
  invFun := map (.ofClass f.symm)
    (OrderMonoidWithZeroHom.ofClass_monotone f.symm.toOrderIso.monotone)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

中文:
定义 congr
  签名: (f : Γ₀ ≃*o Γ'₀)
  定义体: map (.ofClass f) (OrderMonoidWithZeroHom.ofClass_monotone f.toOrderIso.monotone)
  invFun := map (.ofClass f.symm)
    (OrderMonoidWithZeroHom.ofClass_monotone f.symm.toOrderIso.monotone)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

Depends on / 依赖: OrderMonoidWithZeroHom, OrderMonoidWithZeroHom.ofClass_monotone, f.toOrderIso.monotone, monotone, ofClass, ofClass_monotone, toOrderIso
-/
def congr (f : Γ₀ ≃*o Γ'₀) : Valuation R Γ₀ ≃ Valuation R Γ'₀ where
  toFun := map (.ofClass f) (OrderMonoidWithZeroHom.ofClass_monotone f.toOrderIso.monotone)
  invFun := map (.ofClass f.symm)
    (OrderMonoidWithZeroHom.ofClass_monotone f.symm.toOrderIso.monotone)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

section One

variable [Nontrivial R] [NoZeroDivisors R] [DecidablePred fun x : R => x = 0]

variable (R Γ₀) in
/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One (Valuation R Γ₀) where
  body: { __ : R ->*₀ Γ₀ := 1
    map_add_le_max' x y := by
      simp only [ZeroHom.toFun_eq_coe, MonoidWithZeroHom.toZeroHom_coe,
        MonoidWithZeroHom.one_apply_def, le_sup_iff]
      split_ifs <;> simp_all }

中文:
实例 one
  签名: : 幺 (赋值 R Γ₀) where
  定义体: { __ : R ->*₀ Γ₀ := 1
    map_add_le_max' x y := by
      simp only [ZeroHom.toFun_eq_coe, MonoidWithZeroHom.toZeroHom_coe,
        MonoidWithZeroHom.one_apply_def, le_sup_iff]
      split_ifs <;> simp_all }
-/
protected instance one : One (Valuation R Γ₀) where
  one :=
  { __ : R ->*₀ Γ₀ := 1
    map_add_le_max' x y := by
      simp only [ZeroHom.toFun_eq_coe, MonoidWithZeroHom.toZeroHom_coe,
        MonoidWithZeroHom.one_apply_def, le_sup_iff]
      split_ifs <;> simp_all }

/--
lemma `one_apply_def` / 引理 `one_apply_def`

English:
lemma one_apply_def
  given: (x : R)
  statement: (1 : Valuation R Γ₀) x = if x = 0 then 0 else 1
  proof: rfl

中文:
引理 one_apply_def
  条件: (x : R)
  结论: (1 : 赋值 R Γ₀) x = if x = 0 then 0 else 1
  证明: rfl
-/
lemma one_apply_def (x : R) : (1 : Valuation R Γ₀) x = if x = 0 then 0 else 1 := rfl

/--
lemma `toMonoidWithZeroHom_one` / 引理 `toMonoidWithZeroHom_one`

English:
lemma toMonoidWithZeroHom_one
  statement: (1 : Valuation R Γ₀).toMonoidWithZeroHom = 1
  proof: rfl

中文:
引理 toMonoidWithZeroHom_one
  结论: (1 : 赋值 R Γ₀).toMonoidWithZeroHom = 1
  证明: rfl
-/
@[simp] lemma toMonoidWithZeroHom_one : (1 : Valuation R Γ₀).toMonoidWithZeroHom = 1 := rfl

/--
lemma `one_apply_of_ne_zero` / 引理 `one_apply_of_ne_zero`

English:
lemma one_apply_of_ne_zero
  given: {x : R} (hx : x != 0)
  statement: (1 : Valuation R Γ₀) x = 1
  proof: if_neg hx

@[simp]

中文:
引理 one_apply_of_ne_zero
  条件: {x : R} (hx : x != 0)
  结论: (1 : 赋值 R Γ₀) x = 1
  证明: if_neg hx

@[simp]

Depends on / 依赖: if_neg
-/
lemma one_apply_of_ne_zero {x : R} (hx : x != 0) : (1 : Valuation R Γ₀) x = 1 := if_neg hx

@[simp]
/--
lemma `one_apply_eq_zero_iff` / 引理 `one_apply_eq_zero_iff`

English:
lemma one_apply_eq_zero_iff
  given: [Nontrivial Γ₀] {x : R}
  statement: (1 : Valuation R Γ₀) x = 0 ↔ x = 0
  proof: MonoidWithZeroHom.one_apply_eq_zero_iff

中文:
引理 one_apply_eq_zero_iff
  条件: [非平凡 Γ₀] {x : R}
  结论: (1 : 赋值 R Γ₀) x = 0 ↔ x = 0
  证明: MonoidWithZeroHom.one_apply_eq_zero_iff

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.one_apply_eq_zero_iff, one_apply_eq_zero_iff
-/
lemma one_apply_eq_zero_iff [Nontrivial Γ₀] {x : R} : (1 : Valuation R Γ₀) x = 0 ↔ x = 0 :=
  MonoidWithZeroHom.one_apply_eq_zero_iff

/--
lemma `one_apply_le_one` / 引理 `one_apply_le_one`

English:
lemma one_apply_le_one
  given: (x : R)
  statement: (1 : Valuation R Γ₀) x <= 1
  proof: by
  rw [one_apply_def]
  split_ifs <;> simp_all

@[simp]

中文:
引理 one_apply_le_one
  条件: (x : R)
  结论: (1 : 赋值 R Γ₀) x <= 1
  证明: by
  rw [one_apply_def]
  split_ifs <;> simp_all

@[simp]

Depends on / 依赖: one_apply_def, split_ifs
-/
lemma one_apply_le_one (x : R) : (1 : Valuation R Γ₀) x <= 1 := by
  rw [one_apply_def]
  split_ifs <;> simp_all

@[simp]
/--
lemma `one_apply_lt_one_iff` / 引理 `one_apply_lt_one_iff`

English:
lemma one_apply_lt_one_iff
  given: [Nontrivial Γ₀] {x : R}
  statement: (1 : Valuation R Γ₀) x < 1 ↔ x = 0
  proof: by
  rw [one_apply_def]
  split_ifs <;> simp_all

@[simp]

中文:
引理 one_apply_lt_one_iff
  条件: [非平凡 Γ₀] {x : R}
  结论: (1 : 赋值 R Γ₀) x < 1 ↔ x = 0
  证明: by
  rw [one_apply_def]
  split_ifs <;> simp_all

@[simp]

Depends on / 依赖: one_apply_def, split_ifs
-/
lemma one_apply_lt_one_iff [Nontrivial Γ₀] {x : R} : (1 : Valuation R Γ₀) x < 1 ↔ x = 0 := by
  rw [one_apply_def]
  split_ifs <;> simp_all

@[simp]
/--
lemma `one_apply_eq_one_iff` / 引理 `one_apply_eq_one_iff`

English:
lemma one_apply_eq_one_iff
  given: [Nontrivial Γ₀] {x : R}
  statement: (1 : Valuation R Γ₀) x = 1 ↔ x != 0
  proof: MonoidWithZeroHom.one_apply_eq_one_iff

中文:
引理 one_apply_eq_one_iff
  条件: [非平凡 Γ₀] {x : R}
  结论: (1 : 赋值 R Γ₀) x = 1 ↔ x != 0
  证明: MonoidWithZeroHom.one_apply_eq_one_iff

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.one_apply_eq_one_iff, one_apply_eq_one_iff
-/
lemma one_apply_eq_one_iff [Nontrivial Γ₀] {x : R} : (1 : Valuation R Γ₀) x = 1 ↔ x != 0 :=
  MonoidWithZeroHom.one_apply_eq_one_iff

end One

end Monoid

section Group

variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) {x y : R}

/--
theorem `map_inv` / 定理 `map_inv`

English:
theorem map_inv
  given: {R : Type*} [DivisionRing R] (v : Valuation R Γ₀)
  statement: forall x, v x⁻¹ = (v x)⁻¹
  proof: map_inv₀ _

中文:
定理 map_inv
  条件: {R : 类型} [除环 R] (v : 赋值 R Γ₀)
  结论: 对任意 x, v x⁻¹ = (v x)⁻¹
  证明: map_inv₀ _
-/
theorem map_inv {R : Type*} [DivisionRing R] (v : Valuation R Γ₀) : forall x, v x⁻¹ = (v x)⁻¹ :=
  map_inv₀ _

/--
theorem `map_div` / 定理 `map_div`

English:
theorem map_div
  given: {R : Type*} [DivisionRing R] (v : Valuation R Γ₀)
  statement: forall x y, v (x / y) = v x / v y
  proof: map_div₀ _

中文:
定理 map_div
  条件: {R : 类型} [除环 R] (v : 赋值 R Γ₀)
  结论: 对任意 x y, v (x / y) = v x / v y
  证明: map_div₀ _
-/
theorem map_div {R : Type*} [DivisionRing R] (v : Valuation R Γ₀) : forall x y, v (x / y) = v x / v y :=
  map_div₀ _

/--
theorem `one_lt_val_iff` / 定理 `one_lt_val_iff`

English:
theorem one_lt_val_iff
  given: (v : Valuation K Γ₀) {x : K} (h : x != 0)
  statement: 1 < v x ↔ v x⁻¹ < 1
  proof: by
  simp [inv_lt_one₀ (v.pos_iff.2 h)]

中文:
定理 one_lt_val_iff
  条件: (v : 赋值 K Γ₀) {x : K} (h : x != 0)
  结论: 1 < v x ↔ v x⁻¹ < 1
  证明: by
  simp [inv_lt_one₀ (v.pos_iff.2 h)]

Depends on / 依赖: pos_iff, v.pos_iff
-/
theorem one_lt_val_iff (v : Valuation K Γ₀) {x : K} (h : x != 0) : 1 < v x ↔ v x⁻¹ < 1 := by
  simp [inv_lt_one₀ (v.pos_iff.2 h)]

/--
theorem `one_le_val_iff` / 定理 `one_le_val_iff`

English:
theorem one_le_val_iff
  given: (v : Valuation K Γ₀) {x : K} (h : x != 0)
  statement: 1 <= v x ↔ v x⁻¹ <= 1
  proof: by
  simp [inv_le_one₀ (v.pos_iff.2 h)]

中文:
定理 one_le_val_iff
  条件: (v : 赋值 K Γ₀) {x : K} (h : x != 0)
  结论: 1 <= v x ↔ v x⁻¹ <= 1
  证明: by
  simp [inv_le_one₀ (v.pos_iff.2 h)]

Depends on / 依赖: pos_iff, v.pos_iff
-/
theorem one_le_val_iff (v : Valuation K Γ₀) {x : K} (h : x != 0) : 1 <= v x ↔ v x⁻¹ <= 1 := by
  simp [inv_le_one₀ (v.pos_iff.2 h)]

/--
theorem `val_lt_one_iff` / 定理 `val_lt_one_iff`

English:
theorem val_lt_one_iff
  given: (v : Valuation K Γ₀) {x : K} (h : x != 0)
  statement: v x < 1 ↔ 1 < v x⁻¹
  proof: by
  simp [one_lt_inv₀ (v.pos_iff.2 h)]

中文:
定理 val_lt_one_iff
  条件: (v : 赋值 K Γ₀) {x : K} (h : x != 0)
  结论: v x < 1 ↔ 1 < v x⁻¹
  证明: by
  simp [one_lt_inv₀ (v.pos_iff.2 h)]

Depends on / 依赖: pos_iff, v.pos_iff
-/
theorem val_lt_one_iff (v : Valuation K Γ₀) {x : K} (h : x != 0) : v x < 1 ↔ 1 < v x⁻¹ := by
  simp [one_lt_inv₀ (v.pos_iff.2 h)]

/--
theorem `val_le_one_iff` / 定理 `val_le_one_iff`

English:
theorem val_le_one_iff
  given: (v : Valuation K Γ₀) {x : K} (h : x != 0)
  statement: v x <= 1 ↔ 1 <= v x⁻¹
  proof: by
  simp [one_le_inv₀ (v.pos_iff.2 h)]

中文:
定理 val_le_one_iff
  条件: (v : 赋值 K Γ₀) {x : K} (h : x != 0)
  结论: v x <= 1 ↔ 1 <= v x⁻¹
  证明: by
  simp [one_le_inv₀ (v.pos_iff.2 h)]

Depends on / 依赖: pos_iff, v.pos_iff
-/
theorem val_le_one_iff (v : Valuation K Γ₀) {x : K} (h : x != 0) : v x <= 1 ↔ 1 <= v x⁻¹ := by
  simp [one_le_inv₀ (v.pos_iff.2 h)]

/--
theorem `val_eq_one_iff` / 定理 `val_eq_one_iff`

English:
theorem val_eq_one_iff
  given: (v : Valuation K Γ₀) {x : K}
  statement: v x = 1 ↔ v x⁻¹ = 1
  proof: by
  simp

中文:
定理 val_eq_one_iff
  条件: (v : 赋值 K Γ₀) {x : K}
  结论: v x = 1 ↔ v x⁻¹ = 1
  证明: by
  simp
-/
theorem val_eq_one_iff (v : Valuation K Γ₀) {x : K} : v x = 1 ↔ v x⁻¹ = 1 := by
  simp

/--
theorem `val_le_one_or_val_inv_lt_one` / 定理 `val_le_one_or_val_inv_lt_one`

English:
theorem val_le_one_or_val_inv_lt_one
  given: (v : Valuation K Γ₀) (x : K)
  statement: v x <= 1 ∨ v x⁻¹ < 1
  proof: by
  obtain rfl | h := eq_or_ne x 0
  · simp
  · simp only [← one_lt_val_iff v h, le_or_gt]

中文:
定理 val_le_one_or_val_inv_lt_one
  条件: (v : 赋值 K Γ₀) (x : K)
  结论: v x <= 1 ∨ v x⁻¹ < 1
  证明: by
  obtain rfl | h := eq_or_ne x 0
  · simp
  · simp only [← one_lt_val_iff v h, le_or_gt]

Depends on / 依赖: eq_or_ne, le_or_gt, one_lt_val_iff
-/
theorem val_le_one_or_val_inv_lt_one (v : Valuation K Γ₀) (x : K) : v x <= 1 ∨ v x⁻¹ < 1 := by
  obtain rfl | h := eq_or_ne x 0
  · simp
  · simp only [← one_lt_val_iff v h, le_or_gt]

/--
theorem `val_le_one_or_val_inv_le_one` / 定理 `val_le_one_or_val_inv_le_one`

English:
theorem val_le_one_or_val_inv_le_one
  given: (v : Valuation K Γ₀) (x : K)
  statement: v x <= 1 ∨ v x⁻¹ <= 1
  proof: by
  by_cases h : x = 0
  · simp only [h, map_zero, zero_le, inv_zero, or_self]
  · simp only [← one_le_val_iff v h, le_total]

中文:
定理 val_le_one_or_val_inv_le_one
  条件: (v : 赋值 K Γ₀) (x : K)
  结论: v x <= 1 ∨ v x⁻¹ <= 1
  证明: by
  by_cases h : x = 0
  · simp only [h, map_zero, zero_le, inv_zero, or_self]
  · simp only [← one_le_val_iff v h, le_total]

Depends on / 依赖: inv_zero, le_total, map_zero, one_le_val_iff, or_self, zero_le
-/
theorem val_le_one_or_val_inv_le_one (v : Valuation K Γ₀) (x : K) : v x <= 1 ∨ v x⁻¹ <= 1 := by
  by_cases h : x = 0
  · simp only [h, map_zero, zero_le, inv_zero, or_self]
  · simp only [← one_le_val_iff v h, le_total]

/--
Definition of `leAddSubgroup` / `leAddSubgroup` 的定义

English:
definition leAddSubgroup
  signature: (v : Valuation R Γ₀) (γ : Γ₀)
  body: { x | v x <= γ }
  zero_mem' := by simp
  add_mem' {x y} x_in y_in := (v.map_add x y).trans (max_le x_in y_in)
  neg_mem' x_in := by rwa [Set.mem_ofPred, map_neg]

@[simp]

中文:
定义 leAddSubgroup
  签名: (v : 赋值 R Γ₀) (γ : Γ₀)
  定义体: { x | v x <= γ }
  zero_mem' := by simp
  add_mem' {x y} x_in y_in := (v.map_add x y).trans (max_le x_in y_in)
  neg_mem' x_in := by rwa [Set.mem_ofPred, map_neg]

@[simp]
-/
def leAddSubgroup (v : Valuation R Γ₀) (γ : Γ₀) : AddSubgroup R where
  carrier := { x | v x <= γ }
  zero_mem' := by simp
  add_mem' {x y} x_in y_in := (v.map_add x y).trans (max_le x_in y_in)
  neg_mem' x_in := by rwa [Set.mem_ofPred, map_neg]

@[simp]
/--
lemma `mem_leAddSubgroup_iff` / 引理 `mem_leAddSubgroup_iff`

English:
lemma mem_leAddSubgroup_iff
  given: {v : Valuation R Γ₀} {γ : Γ₀} {x : R}
  proof: Iff.rfl

中文:
引理 mem_leAddSubgroup_iff
  条件: {v : 赋值 R Γ₀} {γ : Γ₀} {x : R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_leAddSubgroup_iff {v : Valuation R Γ₀} {γ : Γ₀} {x : R} :
    x in v.leAddSubgroup γ ↔ v x <= γ :=
  Iff.rfl

/--
lemma `leAddSubgroup_monotone` / 引理 `leAddSubgroup_monotone`

English:
lemma leAddSubgroup_monotone
  given: (v : Valuation R Γ₀)
  statement: Monotone v.leAddSubgroup
  proof: fun _ _ h _ => h.trans'

中文:
引理 leAddSubgroup_monotone
  条件: (v : 赋值 R Γ₀)
  结论: 递增 v.leAddSubgroup
  证明: fun _ _ h _ => h.trans'

Depends on / 依赖: h.trans
-/
lemma leAddSubgroup_monotone (v : Valuation R Γ₀) : Monotone v.leAddSubgroup :=
  fun _ _ h _ => h.trans'

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: : Valuation R (ValueGroup₀ (.ofClass v)) where
  body: restrict₀ (.ofClass v)
  map_add_le_max' x y := by
    by_cases H : v x != 0 ∨ v y != 0
    · rcases H with h | h
      all_goals simp only [ZeroHom.toFun_eq_coe, toZeroHom_coe, restrict₀_apply, coe_ofClass, h,
        reduceDIte, le_sup_iff]
      all_goals split_ifs with H
      · simp [H]
      · simp only [H, ↓reduceDIte, WithZero.coe_le_coe, Subtype.mk_le_mk, ← Units.val_le_val,
          Units.val_mk0]
        split_ifs with hy
        · simpa [hy] using map_add_le _ (le_rfl (a := v x)) (hy ▸ zero_le)
        · simp [hy, ← Units.val_le_val]
      · simp [H]
      · simp only [H, ↓reduceDIte, WithZero.coe_le_coe, Subtype.mk_le_mk]
        split_ifs with hx
        · simpa [hx, ← Units.val_le_val] using map_add_le _ (hx ▸ zero_le) (le_rfl (a := v y))
        · simp [hx, ← Units.val_le_val]
    · simp only [ne_eq, not_or, Decidable.not_not] at H
      simp only [ZeroHom.toFun_eq_coe, toZeroHom_coe, restrict₀_apply,
        MonoidWithZeroHom.coe_ofClass, H, ↓reduceDIte, max_self, nonpos_iff_eq_zero]
      replace H : v (x + y) = 0 :=
        le_antisymm (map_add_le _ (le_of_eq H.1) (le_of_eq H.2)) zero_le
      simp [H]

中文:
定义 restrict
  签名: : 赋值 R (ValueGroup₀ (.ofClass v)) where
  定义体: restrict₀ (.ofClass v)
  map_add_le_max' x y := by
    by_cases H : v x != 0 ∨ v y != 0
    · rcases H with h | h
      all_goals simp only [ZeroHom.toFun_eq_coe, toZeroHom_coe, restrict₀_apply, coe_ofClass, h,
        reduceDIte, le_sup_iff]
      all_goals split_ifs with H
      · simp [H]
      · simp only [H, ↓reduceDIte, WithZero.coe_le_coe, Subtype.mk_le_mk, ← Units.val_le_val,
          Units.val_mk0]
        split_ifs with hy
        · simpa [hy] using map_add_le _ (le_rfl (a := v x)) (hy ▸ zero_le)
        · simp [hy, ← Units.val_le_val]
      · simp [H]
      · simp only [H, ↓reduceDIte, WithZero.coe_le_coe, Subtype.mk_le_mk]
        split_ifs with hx
        · simpa [hx, ← Units.val_le_val] using map_add_le _ (hx ▸ zero_le) (le_rfl (a := v y))
        · simp [hx, ← Units.val_le_val]
    · simp only [ne_eq, not_or, Decidable.not_not] at H
      simp only [ZeroHom.toFun_eq_coe, toZeroHom_coe, restrict₀_apply,
        MonoidWithZeroHom.coe_ofClass, H, ↓reduceDIte, max_self, nonpos_iff_eq_zero]
      replace H : v (x + y) = 0 :=
        le_antisymm (map_add_le _ (le_of_eq H.1) (le_of_eq H.2)) zero_le
      simp [H]

Depends on / 依赖: ofClass
-/
def restrict : Valuation R (ValueGroup₀ (.ofClass v)) where
  __ := restrict₀ (.ofClass v)
  map_add_le_max' x y := by
    by_cases H : v x != 0 ∨ v y != 0
    · rcases H with h | h
      all_goals simp only [ZeroHom.toFun_eq_coe, toZeroHom_coe, restrict₀_apply, coe_ofClass, h,
        reduceDIte, le_sup_iff]
      all_goals split_ifs with H
      · simp [H]
      · simp only [H, ↓reduceDIte, WithZero.coe_le_coe, Subtype.mk_le_mk, ← Units.val_le_val,
          Units.val_mk0]
        split_ifs with hy
        · simpa [hy] using map_add_le _ (le_rfl (a := v x)) (hy ▸ zero_le)
        · simp [hy, ← Units.val_le_val]
      · simp [H]
      · simp only [H, ↓reduceDIte, WithZero.coe_le_coe, Subtype.mk_le_mk]
        split_ifs with hx
        · simpa [hx, ← Units.val_le_val] using map_add_le _ (hx ▸ zero_le) (le_rfl (a := v y))
        · simp [hx, ← Units.val_le_val]
    · simp only [ne_eq, not_or, Decidable.not_not] at H
      simp only [ZeroHom.toFun_eq_coe, toZeroHom_coe, restrict₀_apply,
        MonoidWithZeroHom.coe_ofClass, H, ↓reduceDIte, max_self, nonpos_iff_eq_zero]
      replace H : v (x + y) = 0 :=
        le_antisymm (map_add_le _ (le_of_eq H.1) (le_of_eq H.2)) zero_le
      simp [H]

/--
lemma `restrict_def` / 引理 `restrict_def`

English:
lemma restrict_def
  given: (x : R)
  statement: v.restrict x = restrict₀ (.ofClass v) x
  proof: rfl

@[simp]

中文:
引理 restrict_def
  条件: (x : R)
  结论: v.restrict x = restrict₀ (.ofClass v) x
  证明: rfl

@[simp]
-/
lemma restrict_def (x : R) : v.restrict x = restrict₀ (.ofClass v) x := rfl

@[simp]
/--
lemma `embedding_restrict` / 引理 `embedding_restrict`

English:
lemma embedding_restrict
  given: (x : R)
  statement: embedding (v.restrict x) = v x
  proof: embedding_restrict₀ x

中文:
引理 embedding_restrict
  条件: (x : R)
  结论: embedding (v.restrict x) = v x
  证明: embedding_restrict₀ x
-/
lemma embedding_restrict (x : R) : embedding (v.restrict x) = v x :=
  embedding_restrict₀ x

/--
lemma `restrict_lt_iff_lt_embedding` / 引理 `restrict_lt_iff_lt_embedding`

English:
lemma restrict_lt_iff_lt_embedding
  given: {x : R} {g : ValueGroup₀ (.ofClass v)}
  proof: embedding_strictMono.lt_iff_lt.symm.trans (by simp)

中文:
引理 restrict_lt_iff_lt_embedding
  条件: {x : R} {g : ValueGroup₀ (.ofClass v)}
  证明: embedding_strictMono.lt_iff_lt.symm.trans (by simp)

Depends on / 依赖: embedding_strictMono, embedding_strictMono.lt_iff_lt.symm.trans, lt_iff_lt
-/
lemma restrict_lt_iff_lt_embedding {x : R} {g : ValueGroup₀ (.ofClass v)} :
    v.restrict x < g ↔ v x < embedding g :=
  embedding_strictMono.lt_iff_lt.symm.trans (by simp)

/--
lemma `restrict_le_iff_le_embedding` / 引理 `restrict_le_iff_le_embedding`

English:
lemma restrict_le_iff_le_embedding
  given: {x : R} {g : ValueGroup₀ (.ofClass v)}
  proof: embedding_strictMono.le_iff_le.symm.trans (by simp)

中文:
引理 restrict_le_iff_le_embedding
  条件: {x : R} {g : ValueGroup₀ (.ofClass v)}
  证明: embedding_strictMono.le_iff_le.symm.trans (by simp)

Depends on / 依赖: embedding_strictMono, embedding_strictMono.le_iff_le.symm.trans, le_iff_le
-/
lemma restrict_le_iff_le_embedding {x : R} {g : ValueGroup₀ (.ofClass v)} :
    v.restrict x <= g ↔ v x <= embedding g :=
  embedding_strictMono.le_iff_le.symm.trans (by simp)

/--
lemma `restrict_eq_mk` / 引理 `restrict_eq_mk`

English:
lemma restrict_eq_mk
  given: {x : R} (hx : v x != 0)
  statement: v.restrict x =
  proof: by
  simp [restrict_def, restrict₀_apply, valueGroup.mk, hx]

@[simp]

中文:
引理 restrict_eq_mk
  条件: {x : R} (hx : v x != 0)
  结论: v.restrict x =
  证明: by
  simp [restrict_def, restrict₀_apply, valueGroup.mk, hx]

@[simp]

Depends on / 依赖: restrict_def, valueGroup, valueGroup.mk
-/
lemma restrict_eq_mk {x : R} (hx : v x != 0) : v.restrict x =
    (valueGroup.mk (.ofClass v) 1 x (by simp) hx : ValueGroup₀ (.ofClass v)) := by
  simp [restrict_def, restrict₀_apply, valueGroup.mk, hx]

@[simp]
/--
lemma `restrict_pos_iff` / 引理 `restrict_pos_iff`

English:
lemma restrict_pos_iff
  given: (x : R)
  statement: 0 < v.restrict x ↔ 0 < v x
  proof: by
  simp only [restrict_def, restrict₀_apply]
  split_ifs with h <;> simpa [zero_lt_iff]

@[simp]

中文:
引理 restrict_pos_iff
  条件: (x : R)
  结论: 0 < v.restrict x ↔ 0 < v x
  证明: by
  simp only [restrict_def, restrict₀_apply]
  split_ifs with h <;> simpa [zero_lt_iff]

@[simp]

Depends on / 依赖: restrict_def, split_ifs, zero_lt_iff
-/
lemma restrict_pos_iff (x : R) : 0 < v.restrict x ↔ 0 < v x := by
  simp only [restrict_def, restrict₀_apply]
  split_ifs with h <;> simpa [zero_lt_iff]

@[simp]
/--
lemma `restrict_lt_iff` / 引理 `restrict_lt_iff`

English:
lemma restrict_lt_iff
  given: {x y : R}
  statement: v.restrict x < v.restrict y ↔ v x < v y
  proof: by
  rw [restrict_lt_iff_lt_embedding]; rw [embedding_restrict]

@[simp]

中文:
引理 restrict_lt_iff
  条件: {x y : R}
  结论: v.restrict x < v.restrict y ↔ v x < v y
  证明: by
  rw [restrict_lt_iff_lt_embedding]; rw [embedding_restrict]

@[simp]

Depends on / 依赖: embedding_restrict, restrict_lt_iff_lt_embedding
-/
lemma restrict_lt_iff {x y : R} : v.restrict x < v.restrict y ↔ v x < v y := by
  rw [restrict_lt_iff_lt_embedding]; rw [embedding_restrict]

@[simp]
/--
lemma `restrict_le_iff` / 引理 `restrict_le_iff`

English:
lemma restrict_le_iff
  given: {x y : R}
  statement: v.restrict x <= v.restrict y ↔ v x <= v y
  proof: by
  rw [restrict_le_iff_le_embedding]; rw [embedding_restrict]

@[simp]

中文:
引理 restrict_le_iff
  条件: {x y : R}
  结论: v.restrict x <= v.restrict y ↔ v x <= v y
  证明: by
  rw [restrict_le_iff_le_embedding]; rw [embedding_restrict]

@[simp]

Depends on / 依赖: embedding_restrict, restrict_le_iff_le_embedding
-/
lemma restrict_le_iff {x y : R} : v.restrict x <= v.restrict y ↔ v x <= v y := by
  rw [restrict_le_iff_le_embedding]; rw [embedding_restrict]

@[simp]
/--
lemma `restrict_inj` / 引理 `restrict_inj`

English:
lemma restrict_inj
  given: {x y : R}
  statement: v.restrict x = v.restrict y ↔ v x = v y
  proof: embedding_inj.symm.trans (by simp)

中文:
引理 restrict_inj
  条件: {x y : R}
  结论: v.restrict x = v.restrict y ↔ v x = v y
  证明: embedding_inj.symm.trans (by simp)

Depends on / 依赖: embedding_inj, embedding_inj.symm.trans
-/
lemma restrict_inj {x y : R} : v.restrict x = v.restrict y ↔ v x = v y :=
  embedding_inj.symm.trans (by simp)

/--
theorem `isEquiv_restrict` / 定理 `isEquiv_restrict`

English:
theorem isEquiv_restrict
  statement: v.IsEquiv v.restrict
  proof: fun _ _ => v.restrict_le_iff.symm

@[simp]

中文:
定理 isEquiv_restrict
  结论: v.Is等价 v.restrict
  证明: fun _ _ => v.restrict_le_iff.symm

@[simp]

Depends on / 依赖: restrict_le_iff, v.restrict_le_iff.symm
-/
theorem isEquiv_restrict : v.IsEquiv v.restrict := fun _ _ => v.restrict_le_iff.symm

@[simp]
/--
lemma `restrict_lt_one_iff` / 引理 `restrict_lt_one_iff`

English:
lemma restrict_lt_one_iff
  given: {x : R}
  statement: v.restrict x < 1 ↔ v x < 1
  proof: by
  rw [restrict_lt_iff_lt_embedding]; rw [map_one]

@[simp]

中文:
引理 restrict_lt_one_iff
  条件: {x : R}
  结论: v.restrict x < 1 ↔ v x < 1
  证明: by
  rw [restrict_lt_iff_lt_embedding]; rw [map_one]

@[simp]

Depends on / 依赖: map_one, restrict_lt_iff_lt_embedding
-/
lemma restrict_lt_one_iff {x : R} : v.restrict x < 1 ↔ v x < 1 := by
  rw [restrict_lt_iff_lt_embedding]; rw [map_one]

@[simp]
/--
lemma `restrict_le_one_iff` / 引理 `restrict_le_one_iff`

English:
lemma restrict_le_one_iff
  given: {x : R}
  statement: v.restrict x <= 1 ↔ v x <= 1
  proof: by
  rw [restrict_le_iff_le_embedding]; rw [map_one]

@[simp]

中文:
引理 restrict_le_one_iff
  条件: {x : R}
  结论: v.restrict x <= 1 ↔ v x <= 1
  证明: by
  rw [restrict_le_iff_le_embedding]; rw [map_one]

@[simp]

Depends on / 依赖: map_one, restrict_le_iff_le_embedding
-/
lemma restrict_le_one_iff {x : R} : v.restrict x <= 1 ↔ v x <= 1 := by
  rw [restrict_le_iff_le_embedding]; rw [map_one]

@[simp]
/--
lemma `restrict_eq_zero_iff` / 引理 `restrict_eq_zero_iff`

English:
lemma restrict_eq_zero_iff
  given: {x : R}
  statement: v.restrict x = 0 ↔ v x = 0
  proof: by
  simp [restrict_def, restrict₀_eq_zero_iff]

@[simp]

中文:
引理 restrict_eq_zero_iff
  条件: {x : R}
  结论: v.restrict x = 0 ↔ v x = 0
  证明: by
  simp [restrict_def, restrict₀_eq_zero_iff]

@[simp]

Depends on / 依赖: restrict_def
-/
lemma restrict_eq_zero_iff {x : R} : v.restrict x = 0 ↔ v x = 0 := by
  simp [restrict_def, restrict₀_eq_zero_iff]

@[simp]
/--
lemma `restrict_eq_one_iff` / 引理 `restrict_eq_one_iff`

English:
lemma restrict_eq_one_iff
  given: {x : R}
  statement: v.restrict x = 1 ↔ v x = 1
  proof: by
  simp [restrict_def, restrict₀_eq_one_iff]

中文:
引理 restrict_eq_one_iff
  条件: {x : R}
  结论: v.restrict x = 1 ↔ v x = 1
  证明: by
  simp [restrict_def, restrict₀_eq_one_iff]

Depends on / 依赖: restrict_def
-/
lemma restrict_eq_one_iff {x : R} : v.restrict x = 1 ↔ v x = 1 := by
  simp [restrict_def, restrict₀_eq_one_iff]

/--
lemma `exists_div_eq_of_unit` / 引理 `exists_div_eq_of_unit`

English:
lemma exists_div_eq_of_unit
  given: (γ : (ValueGroup₀ (.ofClass v))ˣ)
  proof: by
  set u := WithZero.unzero (Units.ne_zero γ) with hu_def
  obtain ⟨a, ⟨ha, x, hax⟩⟩ := (mem_valueGroup_iff_of_comm _).mp u.2
  have hx : 0 < v x := by
    rw [← restrict_pos_iff]; rw [restrict_def]; rw [WithZero.pos_iff_ne_zero]; rw [ne_eq]; rw [restrict₀_eq_zero_iff]
    aesop
  use x, a, hx, zero_lt_iff.mpr ha
  have ha0 : v.restrict a != 0 := by simpa using ha
  rw [div_eq_iff ha0]; rw [mul_comm]; rw [← embedding_strictMono.injective.eq_iff]; rw [map_mul]; rw [embedding_restrict]; rw [embedding_restrict]
  rw [← MonoidWithZeroHom.coe_ofClass]; rw [← hax]
  congr
  rw [← WithZero.coe_unzero (Units.ne_zero γ)]
  exact Eq.refl ..

中文:
引理 存在_div_eq_of_unit
  条件: (γ : (ValueGroup₀ (.ofClass v))ˣ)
  证明: by
  set u := WithZero.unzero (Units.ne_zero γ) with hu_def
  obtain ⟨a, ⟨ha, x, hax⟩⟩ := (mem_valueGroup_iff_of_comm _).mp u.2
  have hx : 0 < v x := by
    rw [← restrict_pos_iff]; rw [restrict_def]; rw [WithZero.pos_iff_ne_zero]; rw [ne_eq]; rw [restrict₀_eq_zero_iff]
    aesop
  use x, a, hx, zero_lt_iff.mpr ha
  have ha0 : v.restrict a != 0 := by simpa using ha
  rw [div_eq_iff ha0]; rw [mul_comm]; rw [← embedding_strictMono.injective.eq_iff]; rw [map_mul]; rw [embedding_restrict]; rw [embedding_restrict]
  rw [← MonoidWithZeroHom.coe_ofClass]; rw [← hax]
  congr
  rw [← WithZero.coe_unzero (Units.ne_zero γ)]
  exact Eq.refl ..

Depends on / 依赖: Units.ne_zero, WithZero, WithZero.pos_iff_ne_zero, WithZero.unzero, div_eq_iff, embedding_restrict, embedding_strictMono, embedding_strictMono.injective.eq_iff, eq_iff, hu_def, injective, map_mul, mem_valueGroup_iff_of_comm, mul_comm, ne_eq, ne_zero, pos_iff_ne_zero, restrict, restrict_def, restrict_pos_iff
-/
lemma exists_div_eq_of_unit (γ : (ValueGroup₀ (.ofClass v))ˣ) :
    exists r s, 0 < v r ∧ 0 < v s ∧ v.restrict r / v.restrict s = γ.1 := by
  set u := WithZero.unzero (Units.ne_zero γ) with hu_def
  obtain ⟨a, ⟨ha, x, hax⟩⟩ := (mem_valueGroup_iff_of_comm _).mp u.2
  have hx : 0 < v x := by
    rw [← restrict_pos_iff]; rw [restrict_def]; rw [WithZero.pos_iff_ne_zero]; rw [ne_eq]; rw [restrict₀_eq_zero_iff]
    aesop
  use x, a, hx, zero_lt_iff.mpr ha
  have ha0 : v.restrict a != 0 := by simpa using ha
  rw [div_eq_iff ha0]; rw [mul_comm]; rw [← embedding_strictMono.injective.eq_iff]; rw [map_mul]; rw [embedding_restrict]; rw [embedding_restrict]
  rw [← MonoidWithZeroHom.coe_ofClass]; rw [← hax]
  congr
  rw [← WithZero.coe_unzero (Units.ne_zero γ)]
  exact Eq.refl ..

/--
lemma `IsEquiv.restrict` / 引理 `IsEquiv.restrict`

English:
lemma IsEquiv.restrict
  statement: {Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀']
  proof: by
  simp only [IsEquiv] at h ⊢
  simp [h]

中文:
引理 Is等价.restrict
  结论: {Γ₀' : 类型} [带零LinearOrderedComm群 Γ₀']
  证明: by
  simp only [IsEquiv] at h ⊢
  simp [h]

Depends on / 依赖: IsEquiv
-/
lemma IsEquiv.restrict {Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀']
    {w : Valuation R Γ₀'} (h : v.IsEquiv w) : v.restrict.IsEquiv w.restrict := by
  simp only [IsEquiv] at h ⊢
  simp [h]

/--
Definition of `ltAddSubgroup` / `ltAddSubgroup` 的定义

English:
definition ltAddSubgroup
  signature: (v : Valuation R Γ₀) (γ : Γ₀ˣ)
  body: { x | v x < γ }
  zero_mem' := by simp
  add_mem' {x y} x_in y_in := lt_of_le_of_lt (v.map_add x y) (max_lt x_in y_in)
  neg_mem' x_in := by rwa [Set.mem_ofPred, map_neg]

中文:
定义 ltAddSubgroup
  签名: (v : 赋值 R Γ₀) (γ : Γ₀ˣ)
  定义体: { x | v x < γ }
  zero_mem' := by simp
  add_mem' {x y} x_in y_in := lt_of_le_of_lt (v.map_add x y) (max_lt x_in y_in)
  neg_mem' x_in := by rwa [Set.mem_ofPred, map_neg]
-/
@[simps] def ltAddSubgroup (v : Valuation R Γ₀) (γ : Γ₀ˣ) : AddSubgroup R where
  carrier := { x | v x < γ }
  zero_mem' := by simp
  add_mem' {x y} x_in y_in := lt_of_le_of_lt (v.map_add x y) (max_lt x_in y_in)
  neg_mem' x_in := by rwa [Set.mem_ofPred, map_neg]

/--
lemma `mem_ltAddSubgroup_iff` / 引理 `mem_ltAddSubgroup_iff`

English:
lemma mem_ltAddSubgroup_iff
  given: {v : Valuation R Γ₀} {γ x}
  proof: Iff.rfl

中文:
引理 mem_ltAddSubgroup_iff
  条件: {v : 赋值 R Γ₀} {γ x}
  证明: Iff.rfl
-/
@[simp] lemma mem_ltAddSubgroup_iff {v : Valuation R Γ₀} {γ x} :
    x in ltAddSubgroup v γ ↔ v x < γ :=
  Iff.rfl

/--
lemma `ltAddSubgroup_monotone` / 引理 `ltAddSubgroup_monotone`

English:
lemma ltAddSubgroup_monotone
  given: (v : Valuation R Γ₀)
  statement: Monotone v.ltAddSubgroup
  proof: fun _ _ h _ => (Units.val_le_val.mpr h).trans_lt'

中文:
引理 ltAddSubgroup_monotone
  条件: (v : 赋值 R Γ₀)
  结论: 递增 v.ltAddSubgroup
  证明: fun _ _ h _ => (Units.val_le_val.mpr h).trans_lt'

Depends on / 依赖: Units.val_le_val.mpr, trans_lt, val_le_val
-/
lemma ltAddSubgroup_monotone (v : Valuation R Γ₀) : Monotone v.ltAddSubgroup :=
  fun _ _ h _ => (Units.val_le_val.mpr h).trans_lt'

/--
lemma `ltAddSubgroup_le_leAddSubgroup` / 引理 `ltAddSubgroup_le_leAddSubgroup`

English:
lemma ltAddSubgroup_le_leAddSubgroup
  given: (v : Valuation R Γ₀) (γ : Γ₀ˣ)
  proof: fun _ h => h.le

@[simp]

中文:
引理 ltAddSubgroup_le_leAddSubgroup
  条件: (v : 赋值 R Γ₀) (γ : Γ₀ˣ)
  证明: fun _ h => h.le

@[simp]

Depends on / 依赖: h.le
-/
lemma ltAddSubgroup_le_leAddSubgroup (v : Valuation R Γ₀) (γ : Γ₀ˣ) :
    v.ltAddSubgroup γ <= v.leAddSubgroup γ :=
  fun _ h => h.le

@[simp]
/--
lemma `leAddSubgroup_zero` / 引理 `leAddSubgroup_zero`

English:
lemma leAddSubgroup_zero
  given: {K : Type*} [Field K] (v : Valuation K Γ₀)
  proof: by
  ext; simp

中文:
引理 leAddSubgroup_zero
  条件: {K : 类型} [域 K] (v : 赋值 K Γ₀)
  证明: by
  ext; simp
-/
lemma leAddSubgroup_zero {K : Type*} [Field K] (v : Valuation K Γ₀) :
    v.leAddSubgroup 0 = ⊥ := by
  ext; simp

end Group

end Basic

section IsNontrivial

variable [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

/--
Definition of `IsNontrivial` / `IsNontrivial` 的定义

English:
class IsNontrivial
  parameters: : Prop where
  axioms and operations (1):
    - exists_val_nontrivial : exists x : R, v x != 0 ∧ v x != 1

中文:
类 是非平凡
  参数: : 命题 where
  公理与运算 (1 个):
    - exists_val_nontrivial : 存在 x : R, v x != 0 ∧ v x != 1
-/
class IsNontrivial : Prop where
  exists_val_nontrivial : exists x : R, v x != 0 ∧ v x != 1

/--
lemma `IsNontrivial.nontrivial_codomain` / 引理 `IsNontrivial.nontrivial_codomain`

English:
lemma IsNontrivial.nontrivial_codomain
  given: [hv : IsNontrivial v]
  proof: by
  obtain ⟨x, hx0, hx1⟩ := hv.exists_val_nontrivial
  exact ⟨v x, 1, hx1⟩

中文:
引理 是非平凡.nontrivial_codomain
  条件: [hv : 是非平凡 v]
  证明: by
  obtain ⟨x, hx0, hx1⟩ := hv.exists_val_nontrivial
  exact ⟨v x, 1, hx1⟩

Depends on / 依赖: exists_val_nontrivial, hv.exists_val_nontrivial
-/
lemma IsNontrivial.nontrivial_codomain [hv : IsNontrivial v] :
    Nontrivial Γ₀ := by
  obtain ⟨x, hx0, hx1⟩ := hv.exists_val_nontrivial
  exact ⟨v x, 1, hx1⟩

/--
lemma `not_isNontrivial_one` / 引理 `not_isNontrivial_one`

English:
lemma not_isNontrivial_one
  given: [IsDomain R] [DecidablePred fun x : R => x = 0]
  proof: by
  rintro ⟨⟨x, hx, hx'⟩⟩
  rcases eq_or_ne x 0 with rfl | hx0 <;>
  simp_all [one_apply_of_ne_zero]

中文:
引理 not_isNontrivial_one
  条件: [是整环 R] [DecidablePred fun x : R => x = 0]
  证明: by
  rintro ⟨⟨x, hx, hx'⟩⟩
  rcases eq_or_ne x 0 with rfl | hx0 <;>
  simp_all [one_apply_of_ne_zero]

Depends on / 依赖: eq_or_ne, one_apply_of_ne_zero
-/
lemma not_isNontrivial_one [IsDomain R] [DecidablePred fun x : R => x = 0] :
    ¬(1 : Valuation R Γ₀).IsNontrivial := by
  rintro ⟨⟨x, hx, hx'⟩⟩
  rcases eq_or_ne x 0 with rfl | hx0 <;>
  simp_all [one_apply_of_ne_zero]

instance {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}
    [hv : v.IsNontrivial] : Nontrivial (MonoidWithZeroHom.valueMonoid (.ofClass v)) := by
  obtain ⟨x, h0, h1⟩ := hv.exists_val_nontrivial
  rw [Submonoid.nontrivial_iff_exists_ne_one]
  use (Units.mk0 (v x) h0), (MonoidWithZeroHom.ofClass v).mem_valueMonoid (Set.mem_range_self x)
  simpa [Units.ext_iff]

instance {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}
    [hv : v.IsNontrivial] : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass v)) := by
  obtain ⟨x, h0, h1⟩ := hv.exists_val_nontrivial
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  use (Units.mk0 (v x) h0), (MonoidWithZeroHom.ofClass v).mem_valueGroup (Set.mem_range_self x)
  simpa [Units.ext_iff]

section Field

variable {K : Type*} [DivisionRing K] {w : Valuation K Γ₀}

/--
lemma `isNontrivial_iff_exists_unit` / 引理 `isNontrivial_iff_exists_unit`

English:
lemma isNontrivial_iff_exists_unit
  proof: ⟨fun ⟨x, hx0, hx1⟩ =>
    have : Nontrivial Γ₀ := ⟨w x, 0, hx0⟩
    ⟨Units.mk0 x (w.ne_zero_iff.mp hx0), hx1⟩,
    fun ⟨x, hx⟩ =>
    have : Nontrivial Γ₀ := ⟨w x, 1, hx⟩
    ⟨x, w.ne_zero_iff.mpr (Units.ne_zero x), hx⟩⟩

中文:
引理 isNontrivial_iff_存在_unit
  证明: ⟨fun ⟨x, hx0, hx1⟩ =>
    have : Nontrivial Γ₀ := ⟨w x, 0, hx0⟩
    ⟨Units.mk0 x (w.ne_zero_iff.mp hx0), hx1⟩,
    fun ⟨x, hx⟩ =>
    have : Nontrivial Γ₀ := ⟨w x, 1, hx⟩
    ⟨x, w.ne_zero_iff.mpr (Units.ne_zero x), hx⟩⟩

Depends on / 依赖: Nontrivial, Units.mk0, Units.ne_zero, ne_zero, ne_zero_iff, w.ne_zero_iff.mp, w.ne_zero_iff.mpr
-/
lemma isNontrivial_iff_exists_unit :
    w.IsNontrivial ↔ exists x : Kˣ, w x != 1 :=
  ⟨fun ⟨x, hx0, hx1⟩ =>
    have : Nontrivial Γ₀ := ⟨w x, 0, hx0⟩
    ⟨Units.mk0 x (w.ne_zero_iff.mp hx0), hx1⟩,
    fun ⟨x, hx⟩ =>
    have : Nontrivial Γ₀ := ⟨w x, 1, hx⟩
    ⟨x, w.ne_zero_iff.mpr (Units.ne_zero x), hx⟩⟩

/--
lemma `IsNontrivial.exists_lt_one` / 引理 `IsNontrivial.exists_lt_one`

English:
lemma IsNontrivial.exists_lt_one
  statement: {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  proof: by
  obtain ⟨x, hx⟩ := isNontrivial_iff_exists_unit.mp hv
  rw [ne_iff_lt_or_gt] at hx
  rcases hx with hx | hx
  · use x
    simp [hx]
  · use x⁻¹
    simp [-map_inv₀, ← one_lt_val_iff, hx]

中文:
引理 是非平凡.存在_lt_one
  结论: {Γ₀ : 类型} [带零LinearOrderedComm群 Γ₀]
  证明: by
  obtain ⟨x, hx⟩ := isNontrivial_iff_exists_unit.mp hv
  rw [ne_iff_lt_or_gt] at hx
  rcases hx with hx | hx
  · use x
    simp [hx]
  · use x⁻¹
    simp [-map_inv₀, ← one_lt_val_iff, hx]

Depends on / 依赖: isNontrivial_iff_exists_unit, isNontrivial_iff_exists_unit.mp, ne_iff_lt_or_gt, one_lt_val_iff
-/
lemma IsNontrivial.exists_lt_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation K Γ₀} [hv : v.IsNontrivial] :
    exists x != 0, v x < 1 := by
  obtain ⟨x, hx⟩ := isNontrivial_iff_exists_unit.mp hv
  rw [ne_iff_lt_or_gt] at hx
  rcases hx with hx | hx
  · use x
    simp [hx]
  · use x⁻¹
    simp [-map_inv₀, ← one_lt_val_iff, hx]

/--
theorem `isNontrivial_iff_exists_lt_one` / 定理 `isNontrivial_iff_exists_lt_one`

English:
theorem isNontrivial_iff_exists_lt_one
  statement: {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  proof: ⟨fun h => by simpa using h.exists_lt_one (v := v), fun ⟨x, hx0, hx1⟩ => ⟨x, by simp [hx0, hx1.ne]⟩⟩

中文:
定理 isNontrivial_iff_存在_lt_one
  结论: {Γ₀ : 类型} [带零LinearOrderedComm群 Γ₀]
  证明: ⟨fun h => by simpa using h.exists_lt_one (v := v), fun ⟨x, hx0, hx1⟩ => ⟨x, by simp [hx0, hx1.ne]⟩⟩

Depends on / 依赖: exists_lt_one, h.exists_lt_one, hx1.ne
-/
theorem isNontrivial_iff_exists_lt_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) : v.IsNontrivial ↔ exists x != 0, v x < 1 :=
  ⟨fun h => by simpa using h.exists_lt_one (v := v), fun ⟨x, hx0, hx1⟩ => ⟨x, by simp [hx0, hx1.ne]⟩⟩

/--
lemma `IsNontrivial.exists_one_lt` / 引理 `IsNontrivial.exists_one_lt`

English:
lemma IsNontrivial.exists_one_lt
  statement: {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  proof: by
  obtain ⟨x, h0, h1⟩ := hv.exists_lt_one
  use x⁻¹
  simp [one_lt_inv₀ (zero_lt_iff.mpr (by simp [h0] : v x != 0)), h1]

中文:
引理 是非平凡.存在_one_lt
  结论: {Γ₀ : 类型} [带零LinearOrderedComm群 Γ₀]
  证明: by
  obtain ⟨x, h0, h1⟩ := hv.exists_lt_one
  use x⁻¹
  simp [one_lt_inv₀ (zero_lt_iff.mpr (by simp [h0] : v x != 0)), h1]

Depends on / 依赖: exists_lt_one, hv.exists_lt_one, zero_lt_iff, zero_lt_iff.mpr
-/
lemma IsNontrivial.exists_one_lt {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation K Γ₀} [hv : v.IsNontrivial] :
    exists x, 1 < v x := by
  obtain ⟨x, h0, h1⟩ := hv.exists_lt_one
  use x⁻¹
  simp [one_lt_inv₀ (zero_lt_iff.mpr (by simp [h0] : v x != 0)), h1]

/--
lemma `IsNontrivial_iff_exists_one_lt` / 引理 `IsNontrivial_iff_exists_one_lt`

English:
lemma IsNontrivial_iff_exists_one_lt
  statement: {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  proof: ⟨fun h => by simpa using h.exists_one_lt (v := v), fun ⟨x, hx1⟩ => ⟨x, by aesop⟩⟩

中文:
引理 IsNontrivial_iff_存在_one_lt
  结论: {Γ₀ : 类型} [带零LinearOrderedComm群 Γ₀]
  证明: ⟨fun h => by simpa using h.exists_one_lt (v := v), fun ⟨x, hx1⟩ => ⟨x, by aesop⟩⟩

Depends on / 依赖: exists_one_lt, h.exists_one_lt
-/
lemma IsNontrivial_iff_exists_one_lt {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation K Γ₀} : v.IsNontrivial ↔ exists x, 1 < v x :=
  ⟨fun h => by simpa using h.exists_one_lt (v := v), fun ⟨x, hx1⟩ => ⟨x, by aesop⟩⟩

end Field

end IsNontrivial

section IsTrivialOn

variable [LinearOrderedCommMonoidWithZero Γ₀]

/--
Definition of `IsTrivialOn` / `IsTrivialOn` 的定义

English:
class IsTrivialOn
  parameters: {B : Type*} (A : Type*) [CommSemiring A] [Ring B] [Algebra A B]
  axioms and operations (1):
    - eq_one : forall a : A, a != 0 -> v (algebraMap A B a) = 1

中文:
类 是TrivialOn
  参数: {B : 类型} (A : 类型) [交换半环 A] [环 B] [代数 A B]
  公理与运算 (1 个):
    - eq_one : 对任意 a : A, a != 0 -> v (algebraMap A B a) = 1

Depends on / 依赖: WithGeneratedByTopology, WithGeneratedByTopology.isOpen_iff, continuous_def, continuous_id, isOpen_iff
-/
class IsTrivialOn {B : Type*} (A : Type*) [CommSemiring A] [Ring B] [Algebra A B]
    (v : Valuation B Γ₀) where
  eq_one : forall a : A, a != 0 -> v (algebraMap A B a) = 1

attribute [grind =>] Valuation.IsTrivialOn.eq_one

variable {B : Type*} {A : Type*} [CommSemiring A] [Ring B] [Algebra A B] (v : Valuation B Γ₀)
  [v.IsTrivialOn A]

@[simp]
/--
theorem `IsTrivialOn.valuation_algebraMap_le_one` / 定理 `IsTrivialOn.valuation_algebraMap_le_one`

English:
theorem IsTrivialOn.valuation_algebraMap_le_one
  given: (a : A)
  statement: v (algebraMap A B a) <= 1
  proof: by
  by_cases a = 0 <;> grind [zero_le]

中文:
定理 是TrivialOn.valuation_algebraMap_le_one
  条件: (a : A)
  结论: v (algebraMap A B a) <= 1
  证明: by
  by_cases a = 0 <;> grind [zero_le]

Depends on / 依赖: zero_le
-/
theorem IsTrivialOn.valuation_algebraMap_le_one (a : A) : v (algebraMap A B a) <= 1 := by
  by_cases a = 0 <;> grind [zero_le]

end IsTrivialOn

namespace IsEquiv

variable [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]
  [LinearOrderedCommMonoidWithZero Γ''₀]
  {v : Valuation R Γ₀} {v₁ : Valuation R Γ₀} {v₂ : Valuation R Γ'₀} {v₃ : Valuation R Γ''₀}

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  statement: v.IsEquiv v
  proof: fun _ _ => Iff.refl _

@[symm]

中文:
定理 refl
  结论: v.Is等价 v
  证明: fun _ _ => Iff.refl _

@[symm]

Depends on / 依赖: Iff.refl
-/
theorem refl : v.IsEquiv v := fun _ _ => Iff.refl _

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : v₁.IsEquiv v₂)
  statement: v₂.IsEquiv v₁
  proof: fun _ _ => Iff.symm (h _ _)

@[trans]

中文:
定理 symm
  条件: (h : v₁.Is等价 v₂)
  结论: v₂.Is等价 v₁
  证明: fun _ _ => Iff.symm (h _ _)

@[trans]

Depends on / 依赖: Iff.symm
-/
theorem symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁ := fun _ _ => Iff.symm (h _ _)

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃)
  statement: v₁.IsEquiv v₃
  proof: fun _ _ =>
  Iff.trans (h₁₂ _ _) (h₂₃ _ _)

中文:
定理 trans
  条件: (h₁₂ : v₁.Is等价 v₂) (h₂₃ : v₂.Is等价 v₃)
  结论: v₁.Is等价 v₃
  证明: fun _ _ =>
  Iff.trans (h₁₂ _ _) (h₂₃ _ _)
-/
theorem trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃) : v₁.IsEquiv v₃ := fun _ _ =>
  Iff.trans (h₁₂ _ _) (h₂₃ _ _)

/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  given: {v' : Valuation R Γ₀} (h : v = v')
  statement: v.IsEquiv v'
  proof: by subst h; rfl

中文:
定理 of_eq
  条件: {v' : 赋值 R Γ₀} (h : v = v')
  结论: v.Is等价 v'
  证明: by subst h; rfl
-/
theorem of_eq {v' : Valuation R Γ₀} (h : v = v') : v.IsEquiv v' := by subst h; rfl

/--
theorem `map` / 定理 `map`

English:
theorem map
  statement: {v' : Valuation R Γ₀} (f : Γ₀ ->*₀ Γ'₀) (hf : Monotone f) (inf : Injective f)
  proof: let H : StrictMono f := hf.strictMono_of_injective inf
  fun r s =>
  calc
    f (v r) <= f (v s) ↔ v r <= v s := by rw [H.le_iff_le]
    _ ↔ v' r <= v' s := h r s
    _ ↔ f (v' r) <= f (v' s) := by rw [H.le_iff_le]

中文:
定理 map
  结论: {v' : 赋值 R Γ₀} (f : Γ₀ ->*₀ Γ'₀) (hf : 递增 f) (下确界 : 单射 f)
  证明: let H : StrictMono f := hf.strictMono_of_injective inf
  fun r s =>
  calc
    f (v r) <= f (v s) ↔ v r <= v s := by rw [H.le_iff_le]
    _ ↔ v' r <= v' s := h r s
    _ ↔ f (v' r) <= f (v' s) := by rw [H.le_iff_le]

Depends on / 依赖: H.le_iff_le, StrictMono, hf.strictMono_of_injective, le_iff_le, strictMono_of_injective
-/
theorem map {v' : Valuation R Γ₀} (f : Γ₀ ->*₀ Γ'₀) (hf : Monotone f) (inf : Injective f)
    (h : v.IsEquiv v') : (v.map f hf).IsEquiv (v'.map f hf) :=
  let H : StrictMono f := hf.strictMono_of_injective inf
  fun r s =>
  calc
    f (v r) <= f (v s) ↔ v r <= v s := by rw [H.le_iff_le]
    _ ↔ v' r <= v' s := h r s
    _ ↔ f (v' r) <= f (v' s) := by rw [H.le_iff_le]

/--
theorem `comap` / 定理 `comap`

English:
theorem comap
  given: {S : Type*} [Ring S] (f : S ->+* R) (h : v₁.IsEquiv v₂)
  proof: fun r s => h (f r) (f s)

中文:
定理 comap
  条件: {S : 类型} [环 S] (f : S ->+* R) (h : v₁.Is等价 v₂)
  证明: fun r s => h (f r) (f s)
-/
theorem comap {S : Type*} [Ring S] (f : S ->+* R) (h : v₁.IsEquiv v₂) :
    (v₁.comap f).IsEquiv (v₂.comap f) := fun r s => h (f r) (f s)

/--
theorem `eq_iff` / 定理 `eq_iff`

English:
theorem eq_iff
  given: (h : v₁.IsEquiv v₂) {r s : R}
  statement: v₁ r = v₁ s ↔ v₂ r = v₂ s
  proof: by
  simpa only [le_antisymm_iff] using and_congr (h r s) (h s r)
@[deprecated (since := "2026-03-05")] alias val_eq := eq_iff

中文:
定理 eq_iff
  条件: (h : v₁.Is等价 v₂) {r s : R}
  结论: v₁ r = v₁ s ↔ v₂ r = v₂ s
  证明: by
  simpa only [le_antisymm_iff] using and_congr (h r s) (h s r)
@[deprecated (since := "2026-03-05")] alias val_eq := eq_iff

Depends on / 依赖: and_congr, deprecated, eq_iff, le_antisymm_iff, val_eq
-/
theorem eq_iff (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = v₁ s ↔ v₂ r = v₂ s := by
  simpa only [le_antisymm_iff] using and_congr (h r s) (h s r)
@[deprecated (since := "2026-03-05")] alias val_eq := eq_iff

/--
theorem `eq_zero` / 定理 `eq_zero`

English:
theorem eq_zero
  given: (h : v₁.IsEquiv v₂) {r : R}
  statement: v₁ r = 0 ↔ v₂ r = 0
  proof: by
  have : v₁ r = v₁ 0 ↔ v₂ r = v₂ 0 := h.eq_iff
  rwa [v₁.map_zero, v₂.map_zero] at this

中文:
定理 eq_zero
  条件: (h : v₁.Is等价 v₂) {r : R}
  结论: v₁ r = 0 ↔ v₂ r = 0
  证明: by
  have : v₁ r = v₁ 0 ↔ v₂ r = v₂ 0 := h.eq_iff
  rwa [v₁.map_zero, v₂.map_zero] at this

Depends on / 依赖: eq_iff, h.eq_iff, map_zero
-/
theorem eq_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r = 0 ↔ v₂ r = 0 := by
  have : v₁ r = v₁ 0 ↔ v₂ r = v₂ 0 := h.eq_iff
  rwa [v₁.map_zero, v₂.map_zero] at this

/--
lemma `ofClass_eq_zero` / 引理 `ofClass_eq_zero`

English:
lemma ofClass_eq_zero
  given: (h : v₁.IsEquiv v₂) {r : R}
  statement: (MonoidWithZeroHom.ofClass v₁) r = 0 ↔
  proof: eq_zero h

@[deprecated "use `(eq_zero _).ne` instead." (since := "2026-01-05")]

中文:
引理 ofClass_eq_zero
  条件: (h : v₁.Is等价 v₂) {r : R}
  结论: (带零幺半群态射.ofClass v₁) r = 0 ↔
  证明: eq_zero h

@[deprecated "use `(eq_zero _).ne` instead." (since := "2026-01-05")]

Depends on / 依赖: eq_zero
-/
lemma ofClass_eq_zero (h : v₁.IsEquiv v₂) {r : R} : (MonoidWithZeroHom.ofClass v₁) r = 0 ↔
  (MonoidWithZeroHom.ofClass v₂) r = 0 := eq_zero h

@[deprecated "use `(eq_zero _).ne` instead." (since := "2026-01-05")]
/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: (h : v₁.IsEquiv v₂) {r : R}
  statement: v₁ r != 0 ↔ v₂ r != 0
  proof: (eq_zero h).ne

中文:
定理 ne_zero
  条件: (h : v₁.Is等价 v₂) {r : R}
  结论: v₁ r != 0 ↔ v₂ r != 0
  证明: (eq_zero h).ne

Depends on / 依赖: eq_zero
-/
theorem ne_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r != 0 ↔ v₂ r != 0 :=
  (eq_zero h).ne

/--
lemma `pos_iff` / 引理 `pos_iff`

English:
lemma pos_iff
  given: (h : v₁.IsEquiv v₂) {x : R}
  statement: 0 < v₁ x ↔ 0 < v₂ x
  proof: by
  rw [zero_lt_iff]; rw [zero_lt_iff]; rw [h.eq_zero.ne]

中文:
引理 pos_iff
  条件: (h : v₁.Is等价 v₂) {x : R}
  结论: 0 < v₁ x ↔ 0 < v₂ x
  证明: by
  rw [zero_lt_iff]; rw [zero_lt_iff]; rw [h.eq_zero.ne]

Depends on / 依赖: eq_zero, h.eq_zero.ne, zero_lt_iff
-/
lemma pos_iff (h : v₁.IsEquiv v₂) {x : R} : 0 < v₁ x ↔ 0 < v₂ x := by
  rw [zero_lt_iff]; rw [zero_lt_iff]; rw [h.eq_zero.ne]

/--
lemma `le_iff_le` / 引理 `le_iff_le`

English:
lemma le_iff_le
  given: (h : v₁.IsEquiv v₂) {x y : R}
  proof: h x y

中文:
引理 le_iff_le
  条件: (h : v₁.Is等价 v₂) {x y : R}
  证明: h x y
-/
lemma le_iff_le (h : v₁.IsEquiv v₂) {x y : R} :
    v₁ x <= v₁ y ↔ v₂ x <= v₂ y := h x y

/--
lemma `lt_iff_lt` / 引理 `lt_iff_lt`

English:
lemma lt_iff_lt
  given: (h : v₁.IsEquiv v₂) {x y : R}
  proof: by
  rw [← le_iff_le_iff_lt_iff_lt]; rw [h]

中文:
引理 lt_iff_lt
  条件: (h : v₁.Is等价 v₂) {x y : R}
  证明: by
  rw [← le_iff_le_iff_lt_iff_lt]; rw [h]

Depends on / 依赖: le_iff_le_iff_lt_iff_lt
-/
lemma lt_iff_lt (h : v₁.IsEquiv v₂) {x y : R} :
    v₁ x < v₁ y ↔ v₂ x < v₂ y := by
  rw [← le_iff_le_iff_lt_iff_lt]; rw [h]

/--
lemma `le_one_iff_le_one` / 引理 `le_one_iff_le_one`

English:
lemma le_one_iff_le_one
  given: (h : v₁.IsEquiv v₂) {x : R}
  proof: by
  rw [← v₁.map_one]; rw [h]; rw [map_one]

中文:
引理 le_one_iff_le_one
  条件: (h : v₁.Is等价 v₂) {x : R}
  证明: by
  rw [← v₁.map_one]; rw [h]; rw [map_one]

Depends on / 依赖: map_one
-/
lemma le_one_iff_le_one (h : v₁.IsEquiv v₂) {x : R} :
    v₁ x <= 1 ↔ v₂ x <= 1 := by
  rw [← v₁.map_one]; rw [h]; rw [map_one]

/--
lemma `one_le_iff_one_le` / 引理 `one_le_iff_one_le`

English:
lemma one_le_iff_one_le
  given: (h : v₁.IsEquiv v₂) {x : R}
  proof: by
  rw [← v₁.map_one]; rw [h]; rw [map_one]

中文:
引理 one_le_iff_one_le
  条件: (h : v₁.Is等价 v₂) {x : R}
  证明: by
  rw [← v₁.map_one]; rw [h]; rw [map_one]

Depends on / 依赖: map_one
-/
lemma one_le_iff_one_le (h : v₁.IsEquiv v₂) {x : R} :
    1 <= v₁ x ↔ 1 <= v₂ x := by
  rw [← v₁.map_one]; rw [h]; rw [map_one]

/--
lemma `eq_one_iff_eq_one` / 引理 `eq_one_iff_eq_one`

English:
lemma eq_one_iff_eq_one
  given: (h : v₁.IsEquiv v₂) {x : R}
  proof: by
  rw [← v₁.map_one]; rw [h.eq_iff]; rw [map_one]

中文:
引理 eq_one_iff_eq_one
  条件: (h : v₁.Is等价 v₂) {x : R}
  证明: by
  rw [← v₁.map_one]; rw [h.eq_iff]; rw [map_one]

Depends on / 依赖: eq_iff, h.eq_iff, map_one
-/
lemma eq_one_iff_eq_one (h : v₁.IsEquiv v₂) {x : R} :
    v₁ x = 1 ↔ v₂ x = 1 := by
  rw [← v₁.map_one]; rw [h.eq_iff]; rw [map_one]

/--
lemma `lt_one_iff_lt_one` / 引理 `lt_one_iff_lt_one`

English:
lemma lt_one_iff_lt_one
  given: (h : v₁.IsEquiv v₂) {x : R}
  proof: by
  rw [← v₁.map_one]; rw [h.lt_iff_lt]; rw [map_one]

中文:
引理 lt_one_iff_lt_one
  条件: (h : v₁.Is等价 v₂) {x : R}
  证明: by
  rw [← v₁.map_one]; rw [h.lt_iff_lt]; rw [map_one]

Depends on / 依赖: h.lt_iff_lt, lt_iff_lt, map_one
-/
lemma lt_one_iff_lt_one (h : v₁.IsEquiv v₂) {x : R} :
    v₁ x < 1 ↔ v₂ x < 1 := by
  rw [← v₁.map_one]; rw [h.lt_iff_lt]; rw [map_one]

/--
lemma `one_lt_iff_one_lt` / 引理 `one_lt_iff_one_lt`

English:
lemma one_lt_iff_one_lt
  given: (h : v₁.IsEquiv v₂) {x : R}
  proof: by
  rw [← v₁.map_one]; rw [h.lt_iff_lt]; rw [map_one]

中文:
引理 one_lt_iff_one_lt
  条件: (h : v₁.Is等价 v₂) {x : R}
  证明: by
  rw [← v₁.map_one]; rw [h.lt_iff_lt]; rw [map_one]

Depends on / 依赖: h.lt_iff_lt, lt_iff_lt, map_one
-/
lemma one_lt_iff_one_lt (h : v₁.IsEquiv v₂) {x : R} :
    1 < v₁ x ↔ 1 < v₂ x := by
  rw [← v₁.map_one]; rw [h.lt_iff_lt]; rw [map_one]

/--
theorem `isTrivialOn` / 定理 `isTrivialOn`

English:
theorem isTrivialOn
  statement: {A : Type*} [CommSemiring A] [Algebra A R] (h : v₁.IsEquiv v₂)
  proof: h.eq_one_iff_eq_one.mp (IsTrivialOn.eq_one _ ha)

中文:
定理 isTrivialOn
  结论: {A : 类型} [交换半环 A] [代数 A R] (h : v₁.Is等价 v₂)
  证明: h.eq_one_iff_eq_one.mp (IsTrivialOn.eq_one _ ha)

Depends on / 依赖: IsTrivialOn, IsTrivialOn.eq_one, eq_one, eq_one_iff_eq_one, h.eq_one_iff_eq_one.mp
-/
theorem isTrivialOn {A : Type*} [CommSemiring A] [Algebra A R] (h : v₁.IsEquiv v₂)
    (h₁ : IsTrivialOn A v₁) : IsTrivialOn A v₂ where
  eq_one _ ha := h.eq_one_iff_eq_one.mp (IsTrivialOn.eq_one _ ha)

/--
theorem `isTrivialOn_iff` / 定理 `isTrivialOn_iff`

English:
theorem isTrivialOn_iff
  given: {A : Type*} [CommSemiring A] [Algebra A R] (h : v₁.IsEquiv v₂)
  proof: ⟨fun h₁ => h.isTrivialOn h₁, fun h₂ => h.symm.isTrivialOn h₂⟩

中文:
定理 isTrivialOn_iff
  条件: {A : 类型} [交换半环 A] [代数 A R] (h : v₁.Is等价 v₂)
  证明: ⟨fun h₁ => h.isTrivialOn h₁, fun h₂ => h.symm.isTrivialOn h₂⟩

Depends on / 依赖: h.isTrivialOn, h.symm.isTrivialOn, isTrivialOn
-/
theorem isTrivialOn_iff {A : Type*} [CommSemiring A] [Algebra A R] (h : v₁.IsEquiv v₂) :
    IsTrivialOn A v₁ ↔ IsTrivialOn A v₂ :=
  ⟨fun h₁ => h.isTrivialOn h₁, fun h₂ => h.symm.isTrivialOn h₂⟩

end IsEquiv

section LinearOrderedCommMonoidWithZero

variable [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]
  {v : Valuation R Γ₀} {v' : Valuation R Γ'₀}

/--
theorem `isEquiv_map_self_of_strictMono` / 定理 `isEquiv_map_self_of_strictMono`

English:
theorem isEquiv_map_self_of_strictMono
  given: (f : Γ₀ ->*₀ Γ'₀) (H : StrictMono f)
  proof: fun _x _y =>
  ⟨H.le_iff_le.mp, fun h => H.monotone h⟩

中文:
定理 isEquiv_map_self_of_strictMono
  条件: (f : Γ₀ ->*₀ Γ'₀) (H : 严格递增 f)
  证明: fun _x _y =>
  ⟨H.le_iff_le.mp, fun h => H.monotone h⟩
-/
theorem isEquiv_map_self_of_strictMono (f : Γ₀ ->*₀ Γ'₀) (H : StrictMono f) :
    IsEquiv (v.map f H.monotone) v := fun _x _y =>
  ⟨H.le_iff_le.mp, fun h => H.monotone h⟩

/--
theorem `isEquiv_iff_val_lt_val` / 定理 `isEquiv_iff_val_lt_val`

English:
theorem isEquiv_iff_val_lt_val
  statement: v.IsEquiv v' ↔ forall {x y : R}, v x < v y ↔ v' x < v' y
  proof: by
  simp only [IsEquiv, le_iff_le_iff_lt_iff_lt]
  exact forall_comm

中文:
定理 isEquiv_iff_val_lt_val
  结论: v.Is等价 v' ↔ 对任意 {x y : R}, v x < v y ↔ v' x < v' y
  证明: by
  simp only [IsEquiv, le_iff_le_iff_lt_iff_lt]
  exact forall_comm

Depends on / 依赖: IsEquiv, forall_comm, le_iff_le_iff_lt_iff_lt
-/
theorem isEquiv_iff_val_lt_val : v.IsEquiv v' ↔ forall {x y : R}, v x < v y ↔ v' x < v' y := by
  simp only [IsEquiv, le_iff_le_iff_lt_iff_lt]
  exact forall_comm

/--
theorem `isNontrivial_of_isEquiv` / 定理 `isNontrivial_of_isEquiv`

English:
theorem isNontrivial_of_isEquiv
  given: (h : v.IsEquiv v') (hv : v.IsNontrivial)
  statement: v'.IsNontrivial
  proof: by
  obtain ⟨x, hx⟩ := hv
  use x
  simpa [← Valuation.IsEquiv.eq_one_iff_eq_one h, ← Valuation.IsEquiv.eq_zero h]

中文:
定理 isNontrivial_of_isEquiv
  条件: (h : v.Is等价 v') (hv : v.是非平凡)
  结论: v'.是非平凡
  证明: by
  obtain ⟨x, hx⟩ := hv
  use x
  simpa [← Valuation.IsEquiv.eq_one_iff_eq_one h, ← Valuation.IsEquiv.eq_zero h]

Depends on / 依赖: IsEquiv, Valuation, Valuation.IsEquiv.eq_one_iff_eq_one, Valuation.IsEquiv.eq_zero, eq_one_iff_eq_one, eq_zero
-/
theorem isNontrivial_of_isEquiv (h : v.IsEquiv v') (hv : v.IsNontrivial) : v'.IsNontrivial := by
  obtain ⟨x, hx⟩ := hv
  use x
  simpa [← Valuation.IsEquiv.eq_one_iff_eq_one h, ← Valuation.IsEquiv.eq_zero h]

/--
theorem `IsEquiv.isNontrivial_iff` / 定理 `IsEquiv.isNontrivial_iff`

English:
theorem IsEquiv.isNontrivial_iff
  given: (h : v.IsEquiv v')
  proof: ⟨fun hv => isNontrivial_of_isEquiv h hv, fun hv => isNontrivial_of_isEquiv h.symm hv⟩

中文:
定理 Is等价.isNontrivial_iff
  条件: (h : v.Is等价 v')
  证明: ⟨fun hv => isNontrivial_of_isEquiv h hv, fun hv => isNontrivial_of_isEquiv h.symm hv⟩

Depends on / 依赖: h.symm, isNontrivial_of_isEquiv
-/
theorem IsEquiv.isNontrivial_iff (h : v.IsEquiv v') :
    v.IsNontrivial ↔ v'.IsNontrivial :=
  ⟨fun hv => isNontrivial_of_isEquiv h hv, fun hv => isNontrivial_of_isEquiv h.symm hv⟩

end LinearOrderedCommMonoidWithZero

section LinearOrderedCommGroupWithZero

variable [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ'₀]
  [LinearOrderedCommGroupWithZero Γ''₀]

section Ring

variable [Ring R] {v : Valuation R Γ₀} {w : Valuation R Γ'₀} {u : Valuation R Γ''₀}

namespace IsEquiv

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

/--
Definition of `valueGroup₀Fun` / `valueGroup₀Fun` 的定义

English:
definition valueGroup₀Fun
  signature: (h : v.IsEquiv w) (x : ValueGroup₀ (.ofClass v))
  body: if hx : x = 0 then 0 else
    haveI c := (x.zero_or_exists_mk'.resolve_left hx).choose
    valueGroup.mk (.ofClass w) c.1.1 c.1.2 (h.eq_zero.ne.mp c.2.1) (h.eq_zero.ne.mp c.2.2)

中文:
定义 valueGroup₀Fun
  签名: (h : v.Is等价 w) (x : ValueGroup₀ (.ofClass v))
  定义体: if hx : x = 0 then 0 else
    haveI c := (x.zero_or_exists_mk'.resolve_left hx).choose
    valueGroup.mk (.ofClass w) c.1.1 c.1.2 (h.eq_zero.ne.mp c.2.1) (h.eq_zero.ne.mp c.2.2)

Depends on / 依赖: eq_zero, h.eq_zero.ne.mp, ofClass, resolve_left, valueGroup, valueGroup.mk, x.zero_or_exists_mk, zero_or_exists_mk
-/
noncomputable def valueGroup₀Fun (h : v.IsEquiv w) (x : ValueGroup₀ (.ofClass v)) :
    ValueGroup₀ (.ofClass w) :=
  if hx : x = 0 then 0 else
    haveI c := (x.zero_or_exists_mk'.resolve_left hx).choose
    valueGroup.mk (.ofClass w) c.1.1 c.1.2 (h.eq_zero.ne.mp c.2.1) (h.eq_zero.ne.mp c.2.2)

/--
theorem `valueGroup₀Fun_spec` / 定理 `valueGroup₀Fun_spec`

English:
theorem valueGroup₀Fun_spec
  statement: (h : v.IsEquiv w) {r s : R} (hr : (MonoidWithZeroHom.ofClass v) r != 0)
  proof: by
  rw [valueGroup₀Fun]; rw [dif_neg (by simp)]
  generalize_proofs _ _ _ _ H _
  have c_spec := H.choose_spec
  simp only [MonoidWithZeroHom.coe_ofClass, ne_eq, WithZero.coe_inj, valueGroup.mk_inj] at c_spec ⊢
  rwa [← h.eq_iff, eq_comm]

中文:
定理 valueGroup₀Fun_spec
  结论: (h : v.Is等价 w) {r s : R} (hr : (带零幺半群态射.ofClass v) r != 0)
  证明: by
  rw [valueGroup₀Fun]; rw [dif_neg (by simp)]
  generalize_proofs _ _ _ _ H _
  have c_spec := H.choose_spec
  simp only [MonoidWithZeroHom.coe_ofClass, ne_eq, WithZero.coe_inj, valueGroup.mk_inj] at c_spec ⊢
  rwa [← h.eq_iff, eq_comm]

Depends on / 依赖: h.ofClass_eq_zero.ne, ofClass_eq_zero
-/
theorem valueGroup₀Fun_spec (h : v.IsEquiv w) {r s : R} (hr : (MonoidWithZeroHom.ofClass v) r != 0)
    (hs : (MonoidWithZeroHom.ofClass v) s != 0)
    (hr' : (MonoidWithZeroHom.ofClass w) r != 0 := h.ofClass_eq_zero.ne.1 hr)
    (hs' : (MonoidWithZeroHom.ofClass w) s != 0 := h.ofClass_eq_zero.ne.1 hs) :
    valueGroup₀Fun h (valueGroup.mk (.ofClass v) r s hr hs) =
      valueGroup.mk (.ofClass w) r s hr' hs' := by
  rw [valueGroup₀Fun]; rw [dif_neg (by simp)]
  generalize_proofs _ _ _ _ H _
  have c_spec := H.choose_spec
  simp only [MonoidWithZeroHom.coe_ofClass, ne_eq, WithZero.coe_inj, valueGroup.mk_inj] at c_spec ⊢
  rwa [← h.eq_iff, eq_comm]

/--
theorem `valueGroup₀Fun_zero` / 定理 `valueGroup₀Fun_zero`

English:
theorem valueGroup₀Fun_zero
  given: (h : v.IsEquiv w)
  statement: valueGroup₀Fun h 0 = 0
  proof: by simp [valueGroup₀Fun]

中文:
定理 valueGroup₀Fun_zero
  条件: (h : v.Is等价 w)
  结论: valueGroup₀Fun h 0 = 0
  证明: by simp [valueGroup₀Fun]
-/
theorem valueGroup₀Fun_zero (h : v.IsEquiv w) : valueGroup₀Fun h 0 = 0 := by simp [valueGroup₀Fun]

/--
Definition of `orderMonoidIso` / `orderMonoidIso` 的定义

English:
definition orderMonoidIso
  signature: (h : v.IsEquiv w)
  body: valueGroup₀Fun h
  invFun := valueGroup₀Fun h.symm
  map_mul' x y := by
    obtain _ | ⟨r₁, s₁, hr₁, hs₁, rfl⟩ := x.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    obtain _ | ⟨r₂, s₂, hr₂, hs₂, rfl⟩ := y.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    simp [← WithZero.coe_mul, valueGroup.mk_mul, valueGroup₀Fun_spec h]
  left_inv x := by
    obtain _ | ⟨r₁, s₁, hr₁, hs₁, rfl⟩ := x.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    rw [valueGroup₀Fun_spec h]; rw [valueGroup₀Fun_spec h.symm]
  right_inv x := by
    obtain _ | ⟨r₁, s₁, hr₁, hs₁, rfl⟩ := x.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    rw [valueGroup₀Fun_spec h.symm]; rw [valueGroup₀Fun_spec h]
  map_le_map_iff' {x} {y} := by
    simp only [valueGroup₀Fun, ne_eq]
    split_ifs with hx0 hy0 hy0
    · simp [hx0, hy0]
    · simp [hx0]
    · simp [hx0, hy0]
    · generalize_proofs _ _ _ _ hx _ _ hy
      conv_rhs => rw [hx.choose_spec, hy.choose_spec]
      simp only [valueGroup.mk, WithZero.coe_le_coe, Subtype.mk_le_mk]
      nth_rw 2 [mul_comm]
      rw [le_mul_inv_iff_mul_le]; rw [mul_assoc]; rw [mul_comm]; rw [← le_mul_inv_iff_mul_le]; rw [inv_inv]
      nth_rw 4 [mul_comm]
      conv_rhs =>
        rw [le_mul_inv_iff_mul_le]; rw [mul_assoc]; rw [mul_comm]; rw [← le_mul_inv_iff_mul_le]; rw [inv_inv]
      generalize_proofs _ hx' hx20 hy' hy10 hx10 hy20
      rw [← Units.mk0_mul _ _ (mul_ne_zero hx10 hy20)]; rw [← Units.mk0_mul _ _ (mul_ne_zero hx20 hy10)]; rw [← Units.mk0_mul]; rw [← Units.mk0_mul]
      · simp only [← Units.val_le_val]
        repeat rw [Units.val_mk0]
        simp only [MonoidWithZeroHom.coe_ofClass, ← map_mul w, ← h.le_iff_le]
        simp
      · simpa only [MonoidWithZeroHom.coe_ofClass, ← map_mul v, ne_eq, h.eq_zero, map_mul w]
          using mul_ne_zero hx10 hy20
      · simpa only [MonoidWithZeroHom.coe_ofClass, ← map_mul v, ne_eq, h.eq_zero, map_mul w]
          using mul_ne_zero hx20 hy10

@[simp]

中文:
定义 orderMonoidIso
  签名: (h : v.Is等价 w)
  定义体: valueGroup₀Fun h
  invFun := valueGroup₀Fun h.symm
  map_mul' x y := by
    obtain _ | ⟨r₁, s₁, hr₁, hs₁, rfl⟩ := x.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    obtain _ | ⟨r₂, s₂, hr₂, hs₂, rfl⟩ := y.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    simp [← WithZero.coe_mul, valueGroup.mk_mul, valueGroup₀Fun_spec h]
  left_inv x := by
    obtain _ | ⟨r₁, s₁, hr₁, hs₁, rfl⟩ := x.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    rw [valueGroup₀Fun_spec h]; rw [valueGroup₀Fun_spec h.symm]
  right_inv x := by
    obtain _ | ⟨r₁, s₁, hr₁, hs₁, rfl⟩ := x.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    rw [valueGroup₀Fun_spec h.symm]; rw [valueGroup₀Fun_spec h]
  map_le_map_iff' {x} {y} := by
    simp only [valueGroup₀Fun, ne_eq]
    split_ifs with hx0 hy0 hy0
    · simp [hx0, hy0]
    · simp [hx0]
    · simp [hx0, hy0]
    · generalize_proofs _ _ _ _ hx _ _ hy
      conv_rhs => rw [hx.choose_spec, hy.choose_spec]
      simp only [valueGroup.mk, WithZero.coe_le_coe, Subtype.mk_le_mk]
      nth_rw 2 [mul_comm]
      rw [le_mul_inv_iff_mul_le]; rw [mul_assoc]; rw [mul_comm]; rw [← le_mul_inv_iff_mul_le]; rw [inv_inv]
      nth_rw 4 [mul_comm]
      conv_rhs =>
        rw [le_mul_inv_iff_mul_le]; rw [mul_assoc]; rw [mul_comm]; rw [← le_mul_inv_iff_mul_le]; rw [inv_inv]
      generalize_proofs _ hx' hx20 hy' hy10 hx10 hy20
      rw [← Units.mk0_mul _ _ (mul_ne_zero hx10 hy20)]; rw [← Units.mk0_mul _ _ (mul_ne_zero hx20 hy10)]; rw [← Units.mk0_mul]; rw [← Units.mk0_mul]
      · simp only [← Units.val_le_val]
        repeat rw [Units.val_mk0]
        simp only [MonoidWithZeroHom.coe_ofClass, ← map_mul w, ← h.le_iff_le]
        simp
      · simpa only [MonoidWithZeroHom.coe_ofClass, ← map_mul v, ne_eq, h.eq_zero, map_mul w]
          using mul_ne_zero hx10 hy20
      · simpa only [MonoidWithZeroHom.coe_ofClass, ← map_mul v, ne_eq, h.eq_zero, map_mul w]
          using mul_ne_zero hx20 hy10

@[simp]
-/
noncomputable def orderMonoidIso (h : v.IsEquiv w) :
    ValueGroup₀ (.ofClass v) ≃*o ValueGroup₀ (.ofClass w) where
  toFun := valueGroup₀Fun h
  invFun := valueGroup₀Fun h.symm
  map_mul' x y := by
    obtain _ | ⟨r₁, s₁, hr₁, hs₁, rfl⟩ := x.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    obtain _ | ⟨r₂, s₂, hr₂, hs₂, rfl⟩ := y.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    simp [← WithZero.coe_mul, valueGroup.mk_mul, valueGroup₀Fun_spec h]
  left_inv x := by
    obtain _ | ⟨r₁, s₁, hr₁, hs₁, rfl⟩ := x.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    rw [valueGroup₀Fun_spec h]; rw [valueGroup₀Fun_spec h.symm]
  right_inv x := by
    obtain _ | ⟨r₁, s₁, hr₁, hs₁, rfl⟩ := x.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    rw [valueGroup₀Fun_spec h.symm]; rw [valueGroup₀Fun_spec h]
  map_le_map_iff' {x} {y} := by
    simp only [valueGroup₀Fun, ne_eq]
    split_ifs with hx0 hy0 hy0
    · simp [hx0, hy0]
    · simp [hx0]
    · simp [hx0, hy0]
    · generalize_proofs _ _ _ _ hx _ _ hy
      conv_rhs => rw [hx.choose_spec, hy.choose_spec]
      simp only [valueGroup.mk, WithZero.coe_le_coe, Subtype.mk_le_mk]
      nth_rw 2 [mul_comm]
      rw [le_mul_inv_iff_mul_le]; rw [mul_assoc]; rw [mul_comm]; rw [← le_mul_inv_iff_mul_le]; rw [inv_inv]
      nth_rw 4 [mul_comm]
      conv_rhs =>
        rw [le_mul_inv_iff_mul_le]; rw [mul_assoc]; rw [mul_comm]; rw [← le_mul_inv_iff_mul_le]; rw [inv_inv]
      generalize_proofs _ hx' hx20 hy' hy10 hx10 hy20
      rw [← Units.mk0_mul _ _ (mul_ne_zero hx10 hy20)]; rw [← Units.mk0_mul _ _ (mul_ne_zero hx20 hy10)]; rw [← Units.mk0_mul]; rw [← Units.mk0_mul]
      · simp only [← Units.val_le_val]
        repeat rw [Units.val_mk0]
        simp only [MonoidWithZeroHom.coe_ofClass, ← map_mul w, ← h.le_iff_le]
        simp
      · simpa only [MonoidWithZeroHom.coe_ofClass, ← map_mul v, ne_eq, h.eq_zero, map_mul w]
          using mul_ne_zero hx10 hy20
      · simpa only [MonoidWithZeroHom.coe_ofClass, ← map_mul v, ne_eq, h.eq_zero, map_mul w]
          using mul_ne_zero hx20 hy10

@[simp]
/--
theorem `orderMonoidIso_spec` / 定理 `orderMonoidIso_spec`

English:
theorem orderMonoidIso_spec
  given: (h : v.IsEquiv w) (a : R)
  proof: by
  have h_res := h.restrict
  by_cases ha : v a = 0
  · rw [← restrict_eq_zero_iff] at ha
    rwa [ha, map_zero, Eq.comm, ← h_res.eq_zero]
  · rw [(v.restrict_eq_mk ha)]
    simp [orderMonoidIso, valueGroup₀Fun_spec h (hs := ha),
      w.restrict_eq_mk ((eq_zero h.symm).ne.mpr ha)]

中文:
定理 orderMonoidIso_spec
  条件: (h : v.Is等价 w) (a : R)
  证明: by
  have h_res := h.restrict
  by_cases ha : v a = 0
  · rw [← restrict_eq_zero_iff] at ha
    rwa [ha, map_zero, Eq.comm, ← h_res.eq_zero]
  · rw [(v.restrict_eq_mk ha)]
    simp [orderMonoidIso, valueGroup₀Fun_spec h (hs := ha),
      w.restrict_eq_mk ((eq_zero h.symm).ne.mpr ha)]

Depends on / 依赖: Eq.comm, eq_zero, h.restrict, h.symm, h_res, h_res.eq_zero, map_zero, ne.mpr, orderMonoidIso, restrict, restrict_eq_mk, restrict_eq_zero_iff, v.restrict_eq_mk, w.restrict_eq_mk
-/
theorem orderMonoidIso_spec (h : v.IsEquiv w) (a : R) :
    h.orderMonoidIso (v.restrict a) = w.restrict a := by
  have h_res := h.restrict
  by_cases ha : v a = 0
  · rw [← restrict_eq_zero_iff] at ha
    rwa [ha, map_zero, Eq.comm, ← h_res.eq_zero]
  · rw [(v.restrict_eq_mk ha)]
    simp [orderMonoidIso, valueGroup₀Fun_spec h (hs := ha),
      w.restrict_eq_mk ((eq_zero h.symm).ne.mpr ha)]

/--
lemma `orderMonoidIso_spec₀` / 引理 `orderMonoidIso_spec₀`

English:
lemma orderMonoidIso_spec₀
  given: (h : v.IsEquiv w) (a : R)
  proof: orderMonoidIso_spec h a

中文:
引理 orderMonoidIso_spec₀
  条件: (h : v.Is等价 w) (a : R)
  证明: orderMonoidIso_spec h a

Depends on / 依赖: orderMonoidIso_spec
-/
lemma orderMonoidIso_spec₀ (h : v.IsEquiv w) (a : R) :
    h.orderMonoidIso (restrict₀ (.ofClass v) a) = restrict₀ (.ofClass w) a :=
  orderMonoidIso_spec h a

/--
theorem `orderMonoidIso_symm` / 定理 `orderMonoidIso_symm`

English:
theorem orderMonoidIso_symm
  given: (h : v.IsEquiv w) (h' : w.IsEquiv v)
  proof: by
  rfl

@[simp]

中文:
定理 orderMonoidIso_symm
  条件: (h : v.Is等价 w) (h' : w.Is等价 v)
  证明: by
  rfl

@[simp]
-/
theorem orderMonoidIso_symm (h : v.IsEquiv w) (h' : w.IsEquiv v) :
    h.orderMonoidIso.symm = h'.orderMonoidIso := by
  rfl

@[simp]
/--
theorem `orderMonoidIso_eq_refl` / 定理 `orderMonoidIso_eq_refl`

English:
theorem orderMonoidIso_eq_refl
  given: (h : v.IsEquiv v)
  proof: by
  ext x
  obtain (rfl | ⟨x, y, _, _, rfl⟩) := x.zero_or_exists_mk
  · simp
  · simp [orderMonoidIso, valueGroup₀Fun_spec h]

@[simp]

中文:
定理 orderMonoidIso_eq_refl
  条件: (h : v.Is等价 v)
  证明: by
  ext x
  obtain (rfl | ⟨x, y, _, _, rfl⟩) := x.zero_or_exists_mk
  · simp
  · simp [orderMonoidIso, valueGroup₀Fun_spec h]

@[simp]

Depends on / 依赖: orderMonoidIso, x.zero_or_exists_mk, zero_or_exists_mk
-/
theorem orderMonoidIso_eq_refl (h : v.IsEquiv v) :
    h.orderMonoidIso = .refl _ := by
  ext x
  obtain (rfl | ⟨x, y, _, _, rfl⟩) := x.zero_or_exists_mk
  · simp
  · simp [orderMonoidIso, valueGroup₀Fun_spec h]

@[simp]
/--
theorem `orderMonoidIso_trans` / 定理 `orderMonoidIso_trans`

English:
theorem orderMonoidIso_trans
  given: (h : v.IsEquiv w) (h' : w.IsEquiv u)
  proof: by
  ext x
  obtain (rfl | ⟨x, y, _, _, rfl⟩) := x.zero_or_exists_mk
  · simp
  · simp [orderMonoidIso, valueGroup₀Fun_spec h, valueGroup₀Fun_spec h',
      valueGroup₀Fun_spec (trans h h')]

中文:
定理 orderMonoidIso_trans
  条件: (h : v.Is等价 w) (h' : w.Is等价 u)
  证明: by
  ext x
  obtain (rfl | ⟨x, y, _, _, rfl⟩) := x.zero_or_exists_mk
  · simp
  · simp [orderMonoidIso, valueGroup₀Fun_spec h, valueGroup₀Fun_spec h',
      valueGroup₀Fun_spec (trans h h')]

Depends on / 依赖: orderMonoidIso, x.zero_or_exists_mk, zero_or_exists_mk
-/
theorem orderMonoidIso_trans (h : v.IsEquiv w) (h' : w.IsEquiv u) :
    h.orderMonoidIso.trans h'.orderMonoidIso = (h.trans h').orderMonoidIso := by
  ext x
  obtain (rfl | ⟨x, y, _, _, rfl⟩) := x.zero_or_exists_mk
  · simp
  · simp [orderMonoidIso, valueGroup₀Fun_spec h, valueGroup₀Fun_spec h',
      valueGroup₀Fun_spec (trans h h')]

end IsEquiv

end Ring

section DivisionRing

variable {v : Valuation K Γ₀} {v' : Valuation K Γ'₀}

/--
theorem `isEquiv_of_val_le_one` / 定理 `isEquiv_of_val_le_one`

English:
theorem isEquiv_of_val_le_one
  given: (h : forall x, v x <= 1 ↔ v' x <= 1)
  statement: v.IsEquiv v'
  proof: by
  intro x y
  obtain rfl | hy := eq_or_ne y 0
  · simp
  · rw [← div_le_one₀, ← v.map_div, h, v'.map_div, div_le_one₀] <;>
      rwa [zero_lt_iff, ne_zero_iff]

中文:
定理 isEquiv_of_val_le_one
  条件: (h : 对任意 x, v x <= 1 ↔ v' x <= 1)
  结论: v.Is等价 v'
  证明: by
  intro x y
  obtain rfl | hy := eq_or_ne y 0
  · simp
  · rw [← div_le_one₀, ← v.map_div, h, v'.map_div, div_le_one₀] <;>
      rwa [zero_lt_iff, ne_zero_iff]

Depends on / 依赖: eq_or_ne, map_div, ne_zero_iff, v.map_div, zero_lt_iff
-/
theorem isEquiv_of_val_le_one (h : forall x, v x <= 1 ↔ v' x <= 1) : v.IsEquiv v' := by
  intro x y
  obtain rfl | hy := eq_or_ne y 0
  · simp
  · rw [← div_le_one₀, ← v.map_div, h, v'.map_div, div_le_one₀] <;>
      rwa [zero_lt_iff, ne_zero_iff]

/--
theorem `isEquiv_iff_val_le_one` / 定理 `isEquiv_iff_val_le_one`

English:
theorem isEquiv_iff_val_le_one
  statement: v.IsEquiv v' ↔ forall {x}, v x <= 1 ↔ v' x <= 1
  proof: ⟨IsEquiv.le_one_iff_le_one, isEquiv_of_val_le_one⟩

中文:
定理 isEquiv_iff_val_le_one
  结论: v.Is等价 v' ↔ 对任意 {x}, v x <= 1 ↔ v' x <= 1
  证明: ⟨IsEquiv.le_one_iff_le_one, isEquiv_of_val_le_one⟩

Depends on / 依赖: IsEquiv, IsEquiv.le_one_iff_le_one, isEquiv_of_val_le_one, le_one_iff_le_one
-/
theorem isEquiv_iff_val_le_one : v.IsEquiv v' ↔ forall {x}, v x <= 1 ↔ v' x <= 1 :=
  ⟨IsEquiv.le_one_iff_le_one, isEquiv_of_val_le_one⟩

/--
theorem `isEquiv_iff_val_eq_one` / 定理 `isEquiv_iff_val_eq_one`

English:
theorem isEquiv_iff_val_eq_one
  statement: v.IsEquiv v' ↔ forall {x}, v x = 1 ↔ v' x = 1
  proof: by
  constructor
  · intro h x
    rw [h.eq_one_iff_eq_one]
  · intro h
    apply isEquiv_of_val_le_one
    intro x
    constructor
    · intro hx
      rcases lt_or_eq_of_le hx with hx' | hx'
      · have : v (1 + x) = 1 := by
          rw [← v.map_one]
          apply map_add_eq_of_lt_left
          simpa
        rw [h] at this
        rw [show x = -1 + (1 + x) by simp]
        refine le_trans (v'.map_add _ _) ?_
        simp [this]
      · rw [h] at hx'
        exact le_of_eq hx'
    · intro hx
      rcases lt_or_eq_of_le hx with hx' | hx'
      · have : v' (1 + x) = 1 := by
          rw [← v'.map_one]
          apply map_add_eq_of_lt_left
          simpa
        rw [← h] at this
        rw [show x = -1 + (1 + x) by simp]
        refine le_trans (v.map_add _ _) ?_
        simp [this]
      · rw [← h] at hx'
        exact le_of_eq hx'

中文:
定理 isEquiv_iff_val_eq_one
  结论: v.Is等价 v' ↔ 对任意 {x}, v x = 1 ↔ v' x = 1
  证明: by
  constructor
  · intro h x
    rw [h.eq_one_iff_eq_one]
  · intro h
    apply isEquiv_of_val_le_one
    intro x
    constructor
    · intro hx
      rcases lt_or_eq_of_le hx with hx' | hx'
      · have : v (1 + x) = 1 := by
          rw [← v.map_one]
          apply map_add_eq_of_lt_left
          simpa
        rw [h] at this
        rw [show x = -1 + (1 + x) by simp]
        refine le_trans (v'.map_add _ _) ?_
        simp [this]
      · rw [h] at hx'
        exact le_of_eq hx'
    · intro hx
      rcases lt_or_eq_of_le hx with hx' | hx'
      · have : v' (1 + x) = 1 := by
          rw [← v'.map_one]
          apply map_add_eq_of_lt_left
          simpa
        rw [← h] at this
        rw [show x = -1 + (1 + x) by simp]
        refine le_trans (v.map_add _ _) ?_
        simp [this]
      · rw [← h] at hx'
        exact le_of_eq hx'

Depends on / 依赖: eq_one_iff_eq_one, h.eq_one_iff_eq_one, isEquiv_of_val_le_one, le_of_eq, le_trans, lt_or_eq_of_le, map_add, map_add_eq_of_lt_left, map_one, v.map_one
-/
theorem isEquiv_iff_val_eq_one : v.IsEquiv v' ↔ forall {x}, v x = 1 ↔ v' x = 1 := by
  constructor
  · intro h x
    rw [h.eq_one_iff_eq_one]
  · intro h
    apply isEquiv_of_val_le_one
    intro x
    constructor
    · intro hx
      rcases lt_or_eq_of_le hx with hx' | hx'
      · have : v (1 + x) = 1 := by
          rw [← v.map_one]
          apply map_add_eq_of_lt_left
          simpa
        rw [h] at this
        rw [show x = -1 + (1 + x) by simp]
        refine le_trans (v'.map_add _ _) ?_
        simp [this]
      · rw [h] at hx'
        exact le_of_eq hx'
    · intro hx
      rcases lt_or_eq_of_le hx with hx' | hx'
      · have : v' (1 + x) = 1 := by
          rw [← v'.map_one]
          apply map_add_eq_of_lt_left
          simpa
        rw [← h] at this
        rw [show x = -1 + (1 + x) by simp]
        refine le_trans (v.map_add _ _) ?_
        simp [this]
      · rw [← h] at hx'
        exact le_of_eq hx'

/--
theorem `isEquiv_iff_val_lt_one` / 定理 `isEquiv_iff_val_lt_one`

English:
theorem isEquiv_iff_val_lt_one
  statement: v.IsEquiv v' ↔ forall {x}, v x < 1 ↔ v' x < 1
  proof: by
  constructor
  · intro h x
    rw [h.lt_one_iff_lt_one]
  · rw [isEquiv_iff_val_eq_one]
    intro h x
    by_cases hx : x = 0
    · simp only [(zero_iff _).2 hx, zero_ne_one]
    constructor
    · intro hh
      by_contra h_1
      cases ne_iff_lt_or_gt.1 h_1 with
      | inl h_2 => simpa [hh, lt_self_iff_false] using h.2 h_2
      | inr h_2 =>
          rw [← inv_one]; rw [← inv_eq_iff_eq_inv]; rw [← map_inv₀] at hh
          exact hh.not_lt (h.2 ((one_lt_val_iff v' hx).1 h_2))
    · intro hh
      by_contra h_1
      cases ne_iff_lt_or_gt.1 h_1 with
      | inl h_2 => simpa [hh, lt_self_iff_false] using h.1 h_2
      | inr h_2 =>
        rw [← inv_one]; rw [← inv_eq_iff_eq_inv]; rw [← map_inv₀] at hh
        exact hh.not_lt (h.1 ((one_lt_val_iff v hx).1 h_2))

中文:
定理 isEquiv_iff_val_lt_one
  结论: v.Is等价 v' ↔ 对任意 {x}, v x < 1 ↔ v' x < 1
  证明: by
  constructor
  · intro h x
    rw [h.lt_one_iff_lt_one]
  · rw [isEquiv_iff_val_eq_one]
    intro h x
    by_cases hx : x = 0
    · simp only [(zero_iff _).2 hx, zero_ne_one]
    constructor
    · intro hh
      by_contra h_1
      cases ne_iff_lt_or_gt.1 h_1 with
      | inl h_2 => simpa [hh, lt_self_iff_false] using h.2 h_2
      | inr h_2 =>
          rw [← inv_one]; rw [← inv_eq_iff_eq_inv]; rw [← map_inv₀] at hh
          exact hh.not_lt (h.2 ((one_lt_val_iff v' hx).1 h_2))
    · intro hh
      by_contra h_1
      cases ne_iff_lt_or_gt.1 h_1 with
      | inl h_2 => simpa [hh, lt_self_iff_false] using h.1 h_2
      | inr h_2 =>
        rw [← inv_one]; rw [← inv_eq_iff_eq_inv]; rw [← map_inv₀] at hh
        exact hh.not_lt (h.1 ((one_lt_val_iff v hx).1 h_2))

Depends on / 依赖: h.lt_one_iff_lt_one, hh.not_lt, inv_eq_iff_eq_inv, inv_one, isEquiv_iff_val_eq_one, lt_one_iff_lt_one, lt_s, lt_self_iff_false, ne_iff_lt_or_gt, not_lt, one_lt_val_iff, zero_iff, zero_ne_one
-/
theorem isEquiv_iff_val_lt_one : v.IsEquiv v' ↔ forall {x}, v x < 1 ↔ v' x < 1 := by
  constructor
  · intro h x
    rw [h.lt_one_iff_lt_one]
  · rw [isEquiv_iff_val_eq_one]
    intro h x
    by_cases hx : x = 0
    · simp only [(zero_iff _).2 hx, zero_ne_one]
    constructor
    · intro hh
      by_contra h_1
      cases ne_iff_lt_or_gt.1 h_1 with
      | inl h_2 => simpa [hh, lt_self_iff_false] using h.2 h_2
      | inr h_2 =>
          rw [← inv_one]; rw [← inv_eq_iff_eq_inv]; rw [← map_inv₀] at hh
          exact hh.not_lt (h.2 ((one_lt_val_iff v' hx).1 h_2))
    · intro hh
      by_contra h_1
      cases ne_iff_lt_or_gt.1 h_1 with
      | inl h_2 => simpa [hh, lt_self_iff_false] using h.1 h_2
      | inr h_2 =>
        rw [← inv_one]; rw [← inv_eq_iff_eq_inv]; rw [← map_inv₀] at hh
        exact hh.not_lt (h.1 ((one_lt_val_iff v hx).1 h_2))

/--
theorem `isEquiv_iff_val_sub_one_lt_one` / 定理 `isEquiv_iff_val_sub_one_lt_one`

English:
theorem isEquiv_iff_val_sub_one_lt_one
  proof: by
  rw [isEquiv_iff_val_lt_one]
  exact (Equiv.subRight 1).surjective.forall

alias ⟨IsEquiv.val_sub_one_lt_one_iff, _⟩ := isEquiv_iff_val_sub_one_lt_one

中文:
定理 isEquiv_iff_val_sub_one_lt_one
  证明: by
  rw [isEquiv_iff_val_lt_one]
  exact (Equiv.subRight 1).surjective.forall

alias ⟨IsEquiv.val_sub_one_lt_one_iff, _⟩ := isEquiv_iff_val_sub_one_lt_one

Depends on / 依赖: Equiv.subRight, isEquiv_iff_val_lt_one, subRight, surjective, surjective.forall
-/
theorem isEquiv_iff_val_sub_one_lt_one :
    v.IsEquiv v' ↔ forall {x}, v (x - 1) < 1 ↔ v' (x - 1) < 1 := by
  rw [isEquiv_iff_val_lt_one]
  exact (Equiv.subRight 1).surjective.forall

alias ⟨IsEquiv.val_sub_one_lt_one_iff, _⟩ := isEquiv_iff_val_sub_one_lt_one

variable (v v') in
/--
theorem `isEquiv_tfae` / 定理 `isEquiv_tfae`

English:
theorem isEquiv_tfae
  proof: by
  tfae_have 1 ↔ 2 := isEquiv_iff_val_lt_val
  tfae_have 1 ↔ 3 := isEquiv_iff_val_le_one
  tfae_have 1 ↔ 4 := isEquiv_iff_val_eq_one
  tfae_have 1 ↔ 5 := isEquiv_iff_val_lt_one
  tfae_have 1 ↔ 6 := isEquiv_iff_val_sub_one_lt_one
  tfae_finish

中文:
定理 isEquiv_tfae
  证明: by
  tfae_have 1 ↔ 2 := isEquiv_iff_val_lt_val
  tfae_have 1 ↔ 3 := isEquiv_iff_val_le_one
  tfae_have 1 ↔ 4 := isEquiv_iff_val_eq_one
  tfae_have 1 ↔ 5 := isEquiv_iff_val_lt_one
  tfae_have 1 ↔ 6 := isEquiv_iff_val_sub_one_lt_one
  tfae_finish

Depends on / 依赖: isEquiv_iff_val_eq_one, isEquiv_iff_val_le_one, isEquiv_iff_val_lt_one, isEquiv_iff_val_lt_val, isEquiv_iff_val_sub_one_lt_one, tfae_finish, tfae_have
-/
theorem isEquiv_tfae :
    [ v.IsEquiv v',
      forall {x y}, v x < v y ↔ v' x < v' y,
      forall {x}, v x <= 1 ↔ v' x <= 1,
      forall {x}, v x = 1 ↔ v' x = 1,
      forall {x}, v x < 1 ↔ v' x < 1,
      forall {x}, v (x - 1) < 1 ↔ v' (x - 1) < 1 ].TFAE := by
  tfae_have 1 ↔ 2 := isEquiv_iff_val_lt_val
  tfae_have 1 ↔ 3 := isEquiv_iff_val_le_one
  tfae_have 1 ↔ 4 := isEquiv_iff_val_eq_one
  tfae_have 1 ↔ 5 := isEquiv_iff_val_lt_one
  tfae_have 1 ↔ 6 := isEquiv_iff_val_sub_one_lt_one
  tfae_finish

end DivisionRing

end LinearOrderedCommGroupWithZero

section Supp

variable [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

/--
Definition of `supp` / `supp` 的定义

English:
definition supp
  signature: : Ideal R where
  body: { x | v x = 0 }
  zero_mem' := map_zero v
add_mem' {x y} hx hy := le_zero_iff.mp
    calc
      v (x + y) <= max (v x) (v y) := v.map_add x y
      _ <= 0 := max_le (le_zero_iff.mpr hx) (le_zero_iff.mpr hy)
  smul_mem' c x hx :=
    calc
      v (c * x) = v c * v x := map_mul v c x
      _ = v c * 0 := congr_arg _ hx
      _ = 0 := mul_zero _

@[simp]

中文:
定义 supp
  签名: : 理想 R where
  定义体: { x | v x = 0 }
  zero_mem' := map_zero v
add_mem' {x y} hx hy := le_zero_iff.mp
    calc
      v (x + y) <= max (v x) (v y) := v.map_add x y
      _ <= 0 := max_le (le_zero_iff.mpr hx) (le_zero_iff.mpr hy)
  smul_mem' c x hx :=
    calc
      v (c * x) = v c * v x := map_mul v c x
      _ = v c * 0 := congr_arg _ hx
      _ = 0 := mul_zero _

@[simp]
-/
def supp : Ideal R where
  carrier := { x | v x = 0 }
  zero_mem' := map_zero v
add_mem' {x y} hx hy := le_zero_iff.mp
    calc
      v (x + y) <= max (v x) (v y) := v.map_add x y
      _ <= 0 := max_le (le_zero_iff.mpr hx) (le_zero_iff.mpr hy)
  smul_mem' c x hx :=
    calc
      v (c * x) = v c * v x := map_mul v c x
      _ = v c * 0 := congr_arg _ hx
      _ = 0 := mul_zero _

@[simp]
/--
theorem `mem_supp_iff` / 定理 `mem_supp_iff`

English:
theorem mem_supp_iff
  given: (x : R)
  statement: x in supp v ↔ v x = 0
  proof: Iff.rfl

中文:
定理 mem_supp_iff
  条件: (x : R)
  结论: x in supp v ↔ v x = 0
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_supp_iff (x : R) : x in supp v ↔ v x = 0 :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: Γ₀] [NoZeroDivisors Γ₀] : Ideal.IsPrime (supp v)
  body: ⟨fun h =>
one_ne_zero (α := Γ₀)
      calc
        1 = v 1 := v.map_one.symm
        _ = 0 := by rw [← mem_supp_iff, h]; exact Submodule.mem_top,
   fun {x y} hxy => by
    simp only [mem_supp_iff] at hxy ⊢
    rw [v.map_mul x y] at hxy
    exact eq_zero_or_eq_zero_of_mul_eq_zero hxy⟩

中文:
实例 [非平凡
  签名: Γ₀] [无零因子 Γ₀] : 理想.是素 (supp v)
  定义体: ⟨fun h =>
one_ne_zero (α := Γ₀)
      calc
        1 = v 1 := v.map_one.symm
        _ = 0 := by rw [← mem_supp_iff, h]; exact Submodule.mem_top,
   fun {x y} hxy => by
    simp only [mem_supp_iff] at hxy ⊢
    rw [v.map_mul x y] at hxy
    exact eq_zero_or_eq_zero_of_mul_eq_zero hxy⟩

Depends on / 依赖: Submodule, Submodule.mem_top, eq_zero_or_eq_zero_of_mul_eq_zero, map_mul, map_one, mem_supp_iff, mem_top, one_ne_zero, v.map_mul, v.map_one.symm
-/
instance [Nontrivial Γ₀] [NoZeroDivisors Γ₀] : Ideal.IsPrime (supp v) :=
  ⟨fun h =>
one_ne_zero (α := Γ₀)
      calc
        1 = v 1 := v.map_one.symm
        _ = 0 := by rw [← mem_supp_iff, h]; exact Submodule.mem_top,
   fun {x y} hxy => by
    simp only [mem_supp_iff] at hxy ⊢
    rw [v.map_mul x y] at hxy
    exact eq_zero_or_eq_zero_of_mul_eq_zero hxy⟩

/--
theorem `map_add_supp` / 定理 `map_add_supp`

English:
theorem map_add_supp
  given: (a : R) {s : R} (h : s in supp v)
  statement: v (a + s) = v a
  proof: by
  have aux : forall a s, v s = 0 -> v (a + s) <= v a := by
    intro a' s' h'
    refine le_trans (v.map_add a' s') (max_le le_rfl ?_)
    simp [h']
  apply le_antisymm (aux a s h)
  calc
    v a = v (a + s + -s) := by simp
    _ <= v (a + s) := aux (a + s) (-s) (by rwa [← Ideal.neg_mem_iff] at h)

中文:
定理 map_add_supp
  条件: (a : R) {s : R} (h : s in supp v)
  结论: v (a + s) = v a
  证明: by
  have aux : forall a s, v s = 0 -> v (a + s) <= v a := by
    intro a' s' h'
    refine le_trans (v.map_add a' s') (max_le le_rfl ?_)
    simp [h']
  apply le_antisymm (aux a s h)
  calc
    v a = v (a + s + -s) := by simp
    _ <= v (a + s) := aux (a + s) (-s) (by rwa [← Ideal.neg_mem_iff] at h)

Depends on / 依赖: Ideal.neg_mem_iff, le_antisymm, le_rfl, le_trans, map_add, max_le, neg_mem_iff, v.map_add
-/
theorem map_add_supp (a : R) {s : R} (h : s in supp v) : v (a + s) = v a := by
  have aux : forall a s, v s = 0 -> v (a + s) <= v a := by
    intro a' s' h'
    refine le_trans (v.map_add a' s') (max_le le_rfl ?_)
    simp [h']
  apply le_antisymm (aux a s h)
  calc
    v a = v (a + s + -s) := by simp
    _ <= v (a + s) := aux (a + s) (-s) (by rwa [← Ideal.neg_mem_iff] at h)

/--
theorem `comap_supp` / 定理 `comap_supp`

English:
theorem comap_supp
  given: {S : Type*} [CommRing S] (f : S ->+* R)
  proof: Ideal.ext fun x => by rw [mem_supp_iff, Ideal.mem_comap, mem_supp_iff, comap_apply]

中文:
定理 comap_supp
  条件: {S : 类型} [交换环 S] (f : S ->+* R)
  证明: Ideal.ext fun x => by rw [mem_supp_iff, Ideal.mem_comap, mem_supp_iff, comap_apply]

Depends on / 依赖: Ideal.ext, Ideal.mem_comap, comap_apply, mem_comap, mem_supp_iff
-/
theorem comap_supp {S : Type*} [CommRing S] (f : S ->+* R) :
    supp (v.comap f) = Ideal.comap f v.supp :=
  Ideal.ext fun x => by rw [mem_supp_iff, Ideal.mem_comap, mem_supp_iff, comap_apply]

end Supp

end Valuation

section AddMonoid

variable (R) [Ring R] (Γ₀ : Type*) [LinearOrderedAddCommMonoidWithTop Γ₀]

/--
Definition of `AddValuation` / `AddValuation` 的定义

English:
definition AddValuation
  body: Valuation R (Multiplicative Γ₀ᵒᵈ)

中文:
定义 AddValuation
  定义体: Valuation R (Multiplicative Γ₀ᵒᵈ)

Depends on / 依赖: Multiplicative, Valuation
-/
def AddValuation :=
  Valuation R (Multiplicative Γ₀ᵒᵈ)

end AddMonoid

namespace AddValuation

variable {Γ₀ : Type*} {Γ'₀ : Type*}

section Basic

section Monoid
variable [Ring R] [LinearOrderedAddCommMonoidWithTop Γ₀] [LinearOrderedAddCommMonoidWithTop Γ'₀]
  (v : AddValuation R Γ₀)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (AddValuation R Γ₀) R Γ₀
  body: inferInstanceAs FunLike (Valuation R <| Multiplicative Γ₀ᵒᵈ) R Multiplicative Γ₀ᵒᵈ

中文:
实例 :
  签名: 函数状 (AddValuation R Γ₀) R Γ₀
  定义体: inferInstanceAs FunLike (Valuation R <| Multiplicative Γ₀ᵒᵈ) R Multiplicative Γ₀ᵒᵈ

Depends on / 依赖: FunLike, Multiplicative, Valuation
-/
instance : FunLike (AddValuation R Γ₀) R Γ₀ :=
inferInstanceAs FunLike (Valuation R <| Multiplicative Γ₀ᵒᵈ) R Multiplicative Γ₀ᵒᵈ

section

variable (f : R -> Γ₀) (h0 : f 0 = ⊤) (h1 : f 1 = 0)
variable (hadd : forall x y, min (f x) (f y) <= f (x + y)) (hmul : forall x y, f (x * y) = f x + f y)

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : AddValuation R Γ₀ where
  body: f
  map_one' := h1
  map_zero' := h0
  map_add_le_max' := hadd
  map_mul' := hmul

中文:
定义 of
  签名: : AddValuation R Γ₀ where
  定义体: f
  map_one' := h1
  map_zero' := h0
  map_add_le_max' := hadd
  map_mul' := hmul
-/
def of : AddValuation R Γ₀ where
  toFun := f
  map_one' := h1
  map_zero' := h0
  map_add_le_max' := hadd
  map_mul' := hmul

variable {h0} {h1} {hadd} {hmul} {r : R}

@[simp]
/--
theorem `of_apply` / 定理 `of_apply`

English:
theorem of_apply
  statement: (of f h0 h1 hadd hmul) r = f r
  proof: rfl

中文:
定理 of_apply
  结论: (of f h0 h1 hadd hmul) r = f r
  证明: rfl
-/
theorem of_apply : (of f h0 h1 hadd hmul) r = f r := rfl

/--
Definition of `toValuation` / `toValuation` 的定义

English:
definition toValuation
  signature: : AddValuation R Γ₀ ≃ Valuation R (Multiplicative Γ₀ᵒᵈ)
  body: Equiv.refl _

中文:
定义 toValuation
  签名: : AddValuation R Γ₀ ≃ 赋值 R (Multiplicative Γ₀ᵒᵈ)
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def toValuation : AddValuation R Γ₀ ≃ Valuation R (Multiplicative Γ₀ᵒᵈ) :=
  Equiv.refl _

/--
Definition of `ofValuation` / `ofValuation` 的定义

English:
definition ofValuation
  signature: : Valuation R (Multiplicative Γ₀ᵒᵈ) ≃ AddValuation R Γ₀
  body: Equiv.refl _

@[simp]

中文:
定义 ofValuation
  签名: : 赋值 R (Multiplicative Γ₀ᵒᵈ) ≃ AddValuation R Γ₀
  定义体: Equiv.refl _

@[simp]

Depends on / 依赖: Equiv.refl
-/
def ofValuation : Valuation R (Multiplicative Γ₀ᵒᵈ) ≃ AddValuation R Γ₀ :=
  Equiv.refl _

@[simp]
/--
lemma `ofValuation_symm_eq` / 引理 `ofValuation_symm_eq`

English:
lemma ofValuation_symm_eq
  statement: ofValuation.symm = toValuation (R := R) (Γ₀ := Γ₀)
  proof: rfl

@[simp]

中文:
引理 ofValuation_symm_eq
  结论: ofValuation.symm = toValuation (R := R) (Γ₀ := Γ₀)
  证明: rfl

@[simp]
-/
lemma ofValuation_symm_eq : ofValuation.symm = toValuation (R := R) (Γ₀ := Γ₀) := rfl

@[simp]
/--
lemma `toValuation_symm_eq` / 引理 `toValuation_symm_eq`

English:
lemma toValuation_symm_eq
  statement: toValuation.symm = ofValuation (R := R) (Γ₀ := Γ₀)
  proof: rfl

@[simp]

中文:
引理 toValuation_symm_eq
  结论: toValuation.symm = ofValuation (R := R) (Γ₀ := Γ₀)
  证明: rfl

@[simp]
-/
lemma toValuation_symm_eq : toValuation.symm = ofValuation (R := R) (Γ₀ := Γ₀) := rfl

@[simp]
/--
lemma `ofValuation_toValuation` / 引理 `ofValuation_toValuation`

English:
lemma ofValuation_toValuation
  statement: ofValuation (toValuation v) = v
  proof: rfl

@[simp]

中文:
引理 ofValuation_toValuation
  结论: ofValuation (toValuation v) = v
  证明: rfl

@[simp]
-/
lemma ofValuation_toValuation : ofValuation (toValuation v) = v := rfl

@[simp]
/--
lemma `toValuation_ofValuation` / 引理 `toValuation_ofValuation`

English:
lemma toValuation_ofValuation
  given: (v : Valuation R (Multiplicative Γ₀ᵒᵈ))
  proof: rfl

@[simp]

中文:
引理 toValuation_ofValuation
  条件: (v : 赋值 R (Multiplicative Γ₀ᵒᵈ))
  证明: rfl

@[simp]
-/
lemma toValuation_ofValuation (v : Valuation R (Multiplicative Γ₀ᵒᵈ)) :
    toValuation (ofValuation v) = v := rfl

@[simp]
/--
theorem `toValuation_apply` / 定理 `toValuation_apply`

English:
theorem toValuation_apply
  given: (r : R)
  proof: rfl

@[simp]

中文:
定理 toValuation_apply
  条件: (r : R)
  证明: rfl

@[simp]
-/
theorem toValuation_apply (r : R) :
    toValuation v r = Multiplicative.ofAdd (OrderDual.toDual (v r)) :=
  rfl

@[simp]
/--
theorem `ofValuation_apply` / 定理 `ofValuation_apply`

English:
theorem ofValuation_apply
  given: (v : Valuation R (Multiplicative Γ₀ᵒᵈ)) (r : R)
  proof: rfl

中文:
定理 ofValuation_apply
  条件: (v : 赋值 R (Multiplicative Γ₀ᵒᵈ)) (r : R)
  证明: rfl
-/
theorem ofValuation_apply (v : Valuation R (Multiplicative Γ₀ᵒᵈ)) (r : R) :
    ofValuation v r = OrderDual.ofDual (Multiplicative.toAdd (v r)) :=
  rfl

end

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: v 0 = (⊤ : Γ₀)
  proof: Valuation.map_zero v

@[simp]

中文:
定理 map_zero
  结论: v 0 = (⊤ : Γ₀)
  证明: Valuation.map_zero v

@[simp]
-/
theorem map_zero : v 0 = (⊤ : Γ₀) :=
  Valuation.map_zero v

@[simp]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  statement: v 1 = (0 : Γ₀)
  proof: Valuation.map_one v

@[simp]

中文:
定理 map_one
  结论: v 1 = (0 : Γ₀)
  证明: Valuation.map_one v

@[simp]
-/
theorem map_one : v 1 = (0 : Γ₀) :=
  Valuation.map_one v

@[simp]
/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  statement: forall (x y : R), v (x * y) = v x + v y
  proof: Valuation.map_mul v

中文:
定理 map_mul
  结论: 对任意 (x y : R), v (x * y) = v x + v y
  证明: Valuation.map_mul v
-/
theorem map_mul : forall (x y : R), v (x * y) = v x + v y :=
  Valuation.map_mul v

-- `simp`-normal form is `map_add'`
/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  statement: forall (x y : R), min (v x) (v y) <= v (x + y)
  proof: Valuation.map_add v

@[simp]

中文:
定理 map_add
  结论: 对任意 (x y : R), 最小值 (v x) (v y) <= v (x + y)
  证明: Valuation.map_add v

@[simp]
-/
theorem map_add : forall (x y : R), min (v x) (v y) <= v (x + y) :=
  Valuation.map_add v

@[simp]
/--
theorem `map_add'` / 定理 `map_add'`

English:
theorem map_add'
  statement: forall (x y : R), v x <= v (x + y) ∨ v y <= v (x + y)
  proof: by
  intro x y
  rw [← min_le_iff]
  apply map_add

中文:
定理 map_add'
  结论: 对任意 (x y : R), v x <= v (x + y) ∨ v y <= v (x + y)
  证明: by
  intro x y
  rw [← min_le_iff]
  apply map_add

Depends on / 依赖: map_add, min_le_iff
-/
theorem map_add' : forall (x y : R), v x <= v (x + y) ∨ v y <= v (x + y) := by
  intro x y
  rw [← min_le_iff]
  apply map_add

/--
theorem `map_le_add` / 定理 `map_le_add`

English:
theorem map_le_add
  given: {x y : R} {g : Γ₀} (hx : g <= v x) (hy : g <= v y)
  statement: g <= v (x + y)
  proof: Valuation.map_add_le v hx hy

中文:
定理 map_le_add
  条件: {x y : R} {g : Γ₀} (hx : g <= v x) (hy : g <= v y)
  结论: g <= v (x + y)
  证明: Valuation.map_add_le v hx hy

Depends on / 依赖: Valuation, Valuation.map_add_le, map_add_le
-/
theorem map_le_add {x y : R} {g : Γ₀} (hx : g <= v x) (hy : g <= v y) : g <= v (x + y) :=
  Valuation.map_add_le v hx hy

/--
theorem `map_lt_add` / 定理 `map_lt_add`

English:
theorem map_lt_add
  given: {x y : R} {g : Γ₀} (hx : g < v x) (hy : g < v y)
  statement: g < v (x + y)
  proof: Valuation.map_add_lt v hx hy

中文:
定理 map_lt_add
  条件: {x y : R} {g : Γ₀} (hx : g < v x) (hy : g < v y)
  结论: g < v (x + y)
  证明: Valuation.map_add_lt v hx hy

Depends on / 依赖: Valuation, Valuation.map_add_lt, map_add_lt
-/
theorem map_lt_add {x y : R} {g : Γ₀} (hx : g < v x) (hy : g < v y) : g < v (x + y) :=
  Valuation.map_add_lt v hx hy

/--
theorem `map_le_sum` / 定理 `map_le_sum`

English:
theorem map_le_sum
  given: {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hf : forall i in s, g <= v (f i))
  proof: v.map_sum_le hf

中文:
定理 map_le_sum
  条件: {ι : 类型} {s : 有限集 ι} {f : ι -> R} {g : Γ₀} (hf : 对任意 i in s, g <= v (f i))
  证明: v.map_sum_le hf

Depends on / 依赖: map_sum_le, v.map_sum_le
-/
theorem map_le_sum {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hf : forall i in s, g <= v (f i)) :
    g <= v (∑ i in s, f i) :=
  v.map_sum_le hf

/--
theorem `map_lt_sum` / 定理 `map_lt_sum`

English:
theorem map_lt_sum
  statement: {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hg : g != ⊤)
  proof: v.map_sum_lt hg hf

中文:
定理 map_lt_sum
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> R} {g : Γ₀} (hg : g != ⊤)
  证明: v.map_sum_lt hg hf

Depends on / 依赖: map_sum_lt, v.map_sum_lt
-/
theorem map_lt_sum {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hg : g != ⊤)
    (hf : forall i in s, g < v (f i)) : g < v (∑ i in s, f i) :=
  v.map_sum_lt hg hf

/--
theorem `map_lt_sum'` / 定理 `map_lt_sum'`

English:
theorem map_lt_sum'
  statement: {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hg : g < ⊤)
  proof: v.map_sum_lt' hg hf

@[simp]

中文:
定理 map_lt_sum'
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> R} {g : Γ₀} (hg : g < ⊤)
  证明: v.map_sum_lt' hg hf

@[simp]

Depends on / 依赖: map_sum_lt, v.map_sum_lt
-/
theorem map_lt_sum' {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hg : g < ⊤)
    (hf : forall i in s, g < v (f i)) : g < v (∑ i in s, f i) :=
  v.map_sum_lt' hg hf

@[simp]
/--
theorem `map_pow` / 定理 `map_pow`

English:
theorem map_pow
  statement: forall (x : R) (n : Nat), v (x ^ n) = n • (v x)
  proof: Valuation.map_pow v

@[ext]

中文:
定理 map_pow
  结论: 对任意 (x : R) (n : 自然数), v (x ^ n) = n • (v x)
  证明: Valuation.map_pow v

@[ext]

Depends on / 依赖: Valuation, Valuation.map_pow, map_pow
-/
theorem map_pow : forall (x : R) (n : Nat), v (x ^ n) = n • (v x) :=
  Valuation.map_pow v

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {v₁ v₂ : AddValuation R Γ₀} (h : forall r, v₁ r = v₂ r)
  statement: v₁ = v₂
  proof: Valuation.ext h

中文:
定理 ext
  条件: {v₁ v₂ : AddValuation R Γ₀} (h : 对任意 r, v₁ r = v₂ r)
  结论: v₁ = v₂
  证明: Valuation.ext h

Depends on / 依赖: Valuation, Valuation.ext
-/
theorem ext {v₁ v₂ : AddValuation R Γ₀} (h : forall r, v₁ r = v₂ r) : v₁ = v₂ :=
  Valuation.ext h

-- The following definition is not an instance, because we have more than one `v` on a given `R`.
-- In addition, type class inference would not be able to infer `v`.
/-- A valuation gives a preorder on the underlying ring. -/
@[instance_reducible]
/--
Definition of `toPreorder` / `toPreorder` 的定义

English:
definition toPreorder
  signature: : Preorder R
  body: Preorder.lift v

中文:
定义 toPreorder
  签名: : 预序 R
  定义体: Preorder.lift v

Depends on / 依赖: Preorder, Preorder.lift
-/
def toPreorder : Preorder R :=
  Preorder.lift v

/-- If `v` is an additive valuation on a division ring then `v(x) = ⊤` iff `x = 0`. -/
@[simp]
/--
theorem `top_iff` / 定理 `top_iff`

English:
theorem top_iff
  given: [Nontrivial Γ₀] (v : AddValuation K Γ₀) {x : K}
  statement: v x = (⊤ : Γ₀) ↔ x = 0
  proof: v.zero_iff

中文:
定理 top_iff
  条件: [非平凡 Γ₀] (v : AddValuation K Γ₀) {x : K}
  结论: v x = (⊤ : Γ₀) ↔ x = 0
  证明: v.zero_iff

Depends on / 依赖: v.zero_iff, zero_iff
-/
theorem top_iff [Nontrivial Γ₀] (v : AddValuation K Γ₀) {x : K} : v x = (⊤ : Γ₀) ↔ x = 0 :=
  v.zero_iff

/--
theorem `ne_top_iff` / 定理 `ne_top_iff`

English:
theorem ne_top_iff
  given: [Nontrivial Γ₀] (v : AddValuation K Γ₀) {x : K}
  statement: v x != (⊤ : Γ₀) ↔ x != 0
  proof: v.ne_zero_iff

中文:
定理 ne_top_iff
  条件: [非平凡 Γ₀] (v : AddValuation K Γ₀) {x : K}
  结论: v x != (⊤ : Γ₀) ↔ x != 0
  证明: v.ne_zero_iff

Depends on / 依赖: ne_zero_iff, v.ne_zero_iff
-/
theorem ne_top_iff [Nontrivial Γ₀] (v : AddValuation K Γ₀) {x : K} : v x != (⊤ : Γ₀) ↔ x != 0 :=
  v.ne_zero_iff

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: {S : Type*} [Ring S] (f : S ->+* R) (v : AddValuation R Γ₀)
  body: Valuation.comap f v

@[simp]

中文:
定义 comap
  签名: {S : 类型} [环 S] (f : S ->+* R) (v : AddValuation R Γ₀)
  定义体: Valuation.comap f v

@[simp]

Depends on / 依赖: Valuation, Valuation.comap
-/
def comap {S : Type*} [Ring S] (f : S ->+* R) (v : AddValuation R Γ₀) : AddValuation S Γ₀ :=
  Valuation.comap f v

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  statement: v.comap (RingHom.id R) = v
  proof: Valuation.comap_id v

中文:
定理 comap_id
  结论: v.comap (环态射.id R) = v
  证明: Valuation.comap_id v

Depends on / 依赖: Valuation, Valuation.comap_id, comap_id
-/
theorem comap_id : v.comap (RingHom.id R) = v :=
  Valuation.comap_id v

/--
theorem `comap_comp` / 定理 `comap_comp`

English:
theorem comap_comp
  given: {S₁ : Type*} {S₂ : Type*} [Ring S₁] [Ring S₂] (f : S₁ ->+* S₂) (g : S₂ ->+* R)
  proof: Valuation.comap_comp v f g

中文:
定理 comap_comp
  条件: {S₁ : 类型} {S₂ : 类型} [环 S₁] [环 S₂] (f : S₁ ->+* S₂) (g : S₂ ->+* R)
  证明: Valuation.comap_comp v f g

Depends on / 依赖: Valuation, Valuation.comap_comp, comap_comp
-/
theorem comap_comp {S₁ : Type*} {S₂ : Type*} [Ring S₁] [Ring S₂] (f : S₁ ->+* S₂) (g : S₂ ->+* R) :
    v.comap (g.comp f) = (v.comap g).comap f :=
  Valuation.comap_comp v f g

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : Γ₀ ->+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f) (v : AddValuation R Γ₀)
  body: @Valuation.map R (Multiplicative Γ₀ᵒᵈ) (Multiplicative Γ'₀ᵒᵈ) _ _ _
    { toFun := f
      map_mul' := f.map_add
      map_one' := f.map_zero
      map_zero' := ht } (fun _ _ h => hf h) v

@[simp]

中文:
定义 map
  签名: (f : Γ₀ ->+ Γ'₀) (ht : f ⊤ = ⊤) (hf : 递增 f) (v : AddValuation R Γ₀)
  定义体: @Valuation.map R (Multiplicative Γ₀ᵒᵈ) (Multiplicative Γ'₀ᵒᵈ) _ _ _
    { toFun := f
      map_mul' := f.map_add
      map_one' := f.map_zero
      map_zero' := ht } (fun _ _ h => hf h) v

@[simp]

Depends on / 依赖: Multiplicative, Valuation, Valuation.map, f.map_add, f.map_zero, map_add, map_mul, map_one, map_zero
-/
def map (f : Γ₀ ->+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f) (v : AddValuation R Γ₀) :
    AddValuation R Γ'₀ :=
  @Valuation.map R (Multiplicative Γ₀ᵒᵈ) (Multiplicative Γ'₀ᵒᵈ) _ _ _
    { toFun := f
      map_mul' := f.map_add
      map_one' := f.map_zero
      map_zero' := ht } (fun _ _ h => hf h) v

@[simp]
/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  given: (f : Γ₀ ->+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f) (v : AddValuation R Γ₀) (r : R)
  proof: rfl

中文:
引理 map_apply
  条件: (f : Γ₀ ->+ Γ'₀) (ht : f ⊤ = ⊤) (hf : 递增 f) (v : AddValuation R Γ₀) (r : R)
  证明: rfl
-/
lemma map_apply (f : Γ₀ ->+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f) (v : AddValuation R Γ₀) (r : R) :
    v.map f ht hf r = f (v r) := rfl

/--
Definition of `IsEquiv` / `IsEquiv` 的定义

English:
definition IsEquiv
  signature: (v₁ : AddValuation R Γ₀) (v₂ : AddValuation R Γ'₀)
  body: Valuation.IsEquiv v₁ v₂

@[simp]

中文:
定义 Is等价
  签名: (v₁ : AddValuation R Γ₀) (v₂ : AddValuation R Γ'₀)
  定义体: Valuation.IsEquiv v₁ v₂

@[simp]

Depends on / 依赖: IsEquiv, Valuation, Valuation.IsEquiv
-/
def IsEquiv (v₁ : AddValuation R Γ₀) (v₂ : AddValuation R Γ'₀) : Prop :=
  Valuation.IsEquiv v₁ v₂

@[simp]
/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: (x : R)
  statement: v (-x) = v x
  proof: Valuation.map_neg v x

中文:
定理 map_neg
  条件: (x : R)
  结论: v (-x) = v x
  证明: Valuation.map_neg v x

Depends on / 依赖: Valuation, Valuation.map_neg, map_neg
-/
theorem map_neg (x : R) : v (-x) = v x :=
  Valuation.map_neg v x

/--
theorem `map_sub_swap` / 定理 `map_sub_swap`

English:
theorem map_sub_swap
  given: (x y : R)
  statement: v (x - y) = v (y - x)
  proof: Valuation.map_sub_swap v x y

中文:
定理 map_sub_swap
  条件: (x y : R)
  结论: v (x - y) = v (y - x)
  证明: Valuation.map_sub_swap v x y

Depends on / 依赖: Valuation, Valuation.map_sub_swap, map_sub_swap
-/
theorem map_sub_swap (x y : R) : v (x - y) = v (y - x) :=
  Valuation.map_sub_swap v x y

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (x y : R)
  statement: min (v x) (v y) <= v (x - y)
  proof: Valuation.map_sub v x y

中文:
定理 map_sub
  条件: (x y : R)
  结论: 最小值 (v x) (v y) <= v (x - y)
  证明: Valuation.map_sub v x y

Depends on / 依赖: Valuation, Valuation.map_sub, map_sub
-/
theorem map_sub (x y : R) : min (v x) (v y) <= v (x - y) :=
  Valuation.map_sub v x y

/--
theorem `map_le_sub` / 定理 `map_le_sub`

English:
theorem map_le_sub
  given: {x y : R} {g : Γ₀} (hx : g <= v x) (hy : g <= v y)
  statement: g <= v (x - y)
  proof: Valuation.map_sub_le v hx hy

中文:
定理 map_le_sub
  条件: {x y : R} {g : Γ₀} (hx : g <= v x) (hy : g <= v y)
  结论: g <= v (x - y)
  证明: Valuation.map_sub_le v hx hy

Depends on / 依赖: Valuation, Valuation.map_sub_le, map_sub_le
-/
theorem map_le_sub {x y : R} {g : Γ₀} (hx : g <= v x) (hy : g <= v y) : g <= v (x - y) :=
  Valuation.map_sub_le v hx hy

variable {x y : R}

/--
theorem `map_add_of_distinct_val` / 定理 `map_add_of_distinct_val`

English:
theorem map_add_of_distinct_val
  given: (h : v x != v y)
  statement: v (x + y) = @Min.min Γ₀ _ (v x) (v y)
  proof: Valuation.map_add_of_distinct_val v h

中文:
定理 map_add_of_distinct_val
  条件: (h : v x != v y)
  结论: v (x + y) = @最小值.最小值 Γ₀ _ (v x) (v y)
  证明: Valuation.map_add_of_distinct_val v h

Depends on / 依赖: Valuation, Valuation.map_add_of_distinct_val, map_add_of_distinct_val
-/
theorem map_add_of_distinct_val (h : v x != v y) : v (x + y) = @Min.min Γ₀ _ (v x) (v y) :=
  Valuation.map_add_of_distinct_val v h

/--
theorem `map_add_eq_of_lt_left` / 定理 `map_add_eq_of_lt_left`

English:
theorem map_add_eq_of_lt_left
  given: {x y : R} (h : v x < v y)
  proof: by
  rw [map_add_of_distinct_val _ h.ne]; rw [min_eq_left h.le]

中文:
定理 map_add_eq_of_lt_left
  条件: {x y : R} (h : v x < v y)
  证明: by
  rw [map_add_of_distinct_val _ h.ne]; rw [min_eq_left h.le]

Depends on / 依赖: h.le, h.ne, map_add_of_distinct_val, min_eq_left
-/
theorem map_add_eq_of_lt_left {x y : R} (h : v x < v y) :
    v (x + y) = v x := by
  rw [map_add_of_distinct_val _ h.ne]; rw [min_eq_left h.le]

/--
theorem `map_add_eq_of_lt_right` / 定理 `map_add_eq_of_lt_right`

English:
theorem map_add_eq_of_lt_right
  given: {x y : R} (hx : v y < v x)
  proof: add_comm y x ▸ map_add_eq_of_lt_left v hx

中文:
定理 map_add_eq_of_lt_right
  条件: {x y : R} (hx : v y < v x)
  证明: add_comm y x ▸ map_add_eq_of_lt_left v hx

Depends on / 依赖: add_comm, map_add_eq_of_lt_left
-/
theorem map_add_eq_of_lt_right {x y : R} (hx : v y < v x) :
    v (x + y) = v y := add_comm y x ▸ map_add_eq_of_lt_left v hx

/--
theorem `map_sub_eq_of_lt_left` / 定理 `map_sub_eq_of_lt_left`

English:
theorem map_sub_eq_of_lt_left
  given: {x y : R} (hx : v x < v y)
  proof: by
  rw [sub_eq_add_neg]
  apply map_add_eq_of_lt_left
  rwa [map_neg]

中文:
定理 map_sub_eq_of_lt_left
  条件: {x y : R} (hx : v x < v y)
  证明: by
  rw [sub_eq_add_neg]
  apply map_add_eq_of_lt_left
  rwa [map_neg]

Depends on / 依赖: map_add_eq_of_lt_left, map_neg, sub_eq_add_neg
-/
theorem map_sub_eq_of_lt_left {x y : R} (hx : v x < v y) :
    v (x - y) = v x := by
  rw [sub_eq_add_neg]
  apply map_add_eq_of_lt_left
  rwa [map_neg]

/--
theorem `map_sub_eq_of_lt_right` / 定理 `map_sub_eq_of_lt_right`

English:
theorem map_sub_eq_of_lt_right
  given: {x y : R} (hx : v y < v x)
  proof: map_sub_swap v x y ▸ map_sub_eq_of_lt_left v hx

中文:
定理 map_sub_eq_of_lt_right
  条件: {x y : R} (hx : v y < v x)
  证明: map_sub_swap v x y ▸ map_sub_eq_of_lt_left v hx

Depends on / 依赖: map_sub_eq_of_lt_left, map_sub_swap
-/
theorem map_sub_eq_of_lt_right {x y : R} (hx : v y < v x) :
    v (x - y) = v y := map_sub_swap v x y ▸ map_sub_eq_of_lt_left v hx

/--
theorem `map_eq_of_lt_sub` / 定理 `map_eq_of_lt_sub`

English:
theorem map_eq_of_lt_sub
  given: (h : v x < v (y - x))
  statement: v y = v x
  proof: Valuation.map_eq_of_sub_lt v h

中文:
定理 map_eq_of_lt_sub
  条件: (h : v x < v (y - x))
  结论: v y = v x
  证明: Valuation.map_eq_of_sub_lt v h

Depends on / 依赖: Valuation, Valuation.map_eq_of_sub_lt, map_eq_of_sub_lt
-/
theorem map_eq_of_lt_sub (h : v x < v (y - x)) : v y = v x :=
  Valuation.map_eq_of_sub_lt v h

end Monoid

section Group

variable [LinearOrderedAddCommGroupWithTop Γ₀] [Ring R] (v : AddValuation R Γ₀) {x y : R}

@[simp]
/--
theorem `map_inv` / 定理 `map_inv`

English:
theorem map_inv
  given: (v : AddValuation K Γ₀) {x : K}
  statement: v x⁻¹ = -(v x)
  proof: map_inv₀ (toValuation v) x

@[simp]

中文:
定理 map_inv
  条件: (v : AddValuation K Γ₀) {x : K}
  结论: v x⁻¹ = -(v x)
  证明: map_inv₀ (toValuation v) x

@[simp]

Depends on / 依赖: toValuation
-/
theorem map_inv (v : AddValuation K Γ₀) {x : K} : v x⁻¹ = -(v x) :=
  map_inv₀ (toValuation v) x

@[simp]
/--
theorem `map_div` / 定理 `map_div`

English:
theorem map_div
  given: (v : AddValuation K Γ₀) {x y : K}
  statement: v (x / y) = v x - v y
  proof: map_div₀ (toValuation v) x y

中文:
定理 map_div
  条件: (v : AddValuation K Γ₀) {x y : K}
  结论: v (x / y) = v x - v y
  证明: map_div₀ (toValuation v) x y

Depends on / 依赖: toValuation
-/
theorem map_div (v : AddValuation K Γ₀) {x y : K} : v (x / y) = v x - v y :=
  map_div₀ (toValuation v) x y

end Group

end Basic

namespace IsEquiv

variable [LinearOrderedAddCommMonoidWithTop Γ₀] [LinearOrderedAddCommMonoidWithTop Γ'₀]
  [Ring R]
  {Γ''₀ : Type*} [LinearOrderedAddCommMonoidWithTop Γ''₀]
  {v : AddValuation R Γ₀} {v₁ : AddValuation R Γ₀}
  {v₂ : AddValuation R Γ'₀} {v₃ : AddValuation R Γ''₀}

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  statement: v.IsEquiv v
  proof: Valuation.IsEquiv.refl

@[symm]

中文:
定理 refl
  结论: v.Is等价 v
  证明: Valuation.IsEquiv.refl

@[symm]

Depends on / 依赖: IsEquiv, Valuation, Valuation.IsEquiv.refl
-/
theorem refl : v.IsEquiv v :=
  Valuation.IsEquiv.refl

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : v₁.IsEquiv v₂)
  statement: v₂.IsEquiv v₁
  proof: Valuation.IsEquiv.symm h

@[trans]

中文:
定理 symm
  条件: (h : v₁.Is等价 v₂)
  结论: v₂.Is等价 v₁
  证明: Valuation.IsEquiv.symm h

@[trans]

Depends on / 依赖: IsEquiv, Valuation, Valuation.IsEquiv.symm
-/
theorem symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁ :=
  Valuation.IsEquiv.symm h

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃)
  statement: v₁.IsEquiv v₃
  proof: Valuation.IsEquiv.trans h₁₂ h₂₃

中文:
定理 trans
  条件: (h₁₂ : v₁.Is等价 v₂) (h₂₃ : v₂.Is等价 v₃)
  结论: v₁.Is等价 v₃
  证明: Valuation.IsEquiv.trans h₁₂ h₂₃

Depends on / 依赖: IsEquiv, Valuation, Valuation.IsEquiv.trans
-/
theorem trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃) : v₁.IsEquiv v₃ :=
  Valuation.IsEquiv.trans h₁₂ h₂₃

/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  given: {v' : AddValuation R Γ₀} (h : v = v')
  statement: v.IsEquiv v'
  proof: Valuation.IsEquiv.of_eq h

中文:
定理 of_eq
  条件: {v' : AddValuation R Γ₀} (h : v = v')
  结论: v.Is等价 v'
  证明: Valuation.IsEquiv.of_eq h

Depends on / 依赖: IsEquiv, Valuation, Valuation.IsEquiv.of_eq, of_eq
-/
theorem of_eq {v' : AddValuation R Γ₀} (h : v = v') : v.IsEquiv v' :=
  Valuation.IsEquiv.of_eq h

/--
theorem `map` / 定理 `map`

English:
theorem map
  statement: {v' : AddValuation R Γ₀} (f : Γ₀ ->+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f)
  proof: @Valuation.IsEquiv.map R (Multiplicative Γ₀ᵒᵈ) (Multiplicative Γ'₀ᵒᵈ) _ _ _ _ _
    { toFun := f
      map_mul' := f.map_add
      map_one' := f.map_zero
      map_zero' := ht } (fun _x _y h => hf h) inf h

中文:
定理 map
  结论: {v' : AddValuation R Γ₀} (f : Γ₀ ->+ Γ'₀) (ht : f ⊤ = ⊤) (hf : 递增 f)
  证明: @Valuation.IsEquiv.map R (Multiplicative Γ₀ᵒᵈ) (Multiplicative Γ'₀ᵒᵈ) _ _ _ _ _
    { toFun := f
      map_mul' := f.map_add
      map_one' := f.map_zero
      map_zero' := ht } (fun _x _y h => hf h) inf h

Depends on / 依赖: IsEquiv, Multiplicative, Valuation, Valuation.IsEquiv.map, f.map_add, f.map_zero, map_add, map_mul, map_one, map_zero
-/
theorem map {v' : AddValuation R Γ₀} (f : Γ₀ ->+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f)
    (inf : Injective f) (h : v.IsEquiv v') : (v.map f ht hf).IsEquiv (v'.map f ht hf) :=
  @Valuation.IsEquiv.map R (Multiplicative Γ₀ᵒᵈ) (Multiplicative Γ'₀ᵒᵈ) _ _ _ _ _
    { toFun := f
      map_mul' := f.map_add
      map_one' := f.map_zero
      map_zero' := ht } (fun _x _y h => hf h) inf h

/--
theorem `comap` / 定理 `comap`

English:
theorem comap
  given: {S : Type*} [Ring S] (f : S ->+* R) (h : v₁.IsEquiv v₂)
  proof: Valuation.IsEquiv.comap f h

中文:
定理 comap
  条件: {S : 类型} [环 S] (f : S ->+* R) (h : v₁.Is等价 v₂)
  证明: Valuation.IsEquiv.comap f h

Depends on / 依赖: IsEquiv, Valuation, Valuation.IsEquiv.comap
-/
theorem comap {S : Type*} [Ring S] (f : S ->+* R) (h : v₁.IsEquiv v₂) :
    (v₁.comap f).IsEquiv (v₂.comap f) :=
  Valuation.IsEquiv.comap f h

/--
theorem `val_eq` / 定理 `val_eq`

English:
theorem val_eq
  given: (h : v₁.IsEquiv v₂) {r s : R}
  statement: v₁ r = v₁ s ↔ v₂ r = v₂ s
  proof: Valuation.IsEquiv.eq_iff h

中文:
定理 val_eq
  条件: (h : v₁.Is等价 v₂) {r s : R}
  结论: v₁ r = v₁ s ↔ v₂ r = v₂ s
  证明: Valuation.IsEquiv.eq_iff h

Depends on / 依赖: CWComplex, CWComplex.instRelCWComplex, IsEquiv, TopologicalSpace, Valuation, Valuation.IsEquiv.eq_iff, eq_iff, instRelCWComplex
-/
theorem val_eq (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = v₁ s ↔ v₂ r = v₂ s :=
  Valuation.IsEquiv.eq_iff h

/--
theorem `ne_top` / 定理 `ne_top`

English:
theorem ne_top
  given: (h : v₁.IsEquiv v₂) {r : R}
  statement: v₁ r != (⊤ : Γ₀) ↔ v₂ r != (⊤ : Γ'₀)
  proof: (Valuation.IsEquiv.eq_zero h).ne

中文:
定理 ne_top
  条件: (h : v₁.Is等价 v₂) {r : R}
  结论: v₁ r != (⊤ : Γ₀) ↔ v₂ r != (⊤ : Γ'₀)
  证明: (Valuation.IsEquiv.eq_zero h).ne

Depends on / 依赖: IsEquiv, Valuation, Valuation.IsEquiv.eq_zero, eq_zero
-/
theorem ne_top (h : v₁.IsEquiv v₂) {r : R} : v₁ r != (⊤ : Γ₀) ↔ v₂ r != (⊤ : Γ'₀) :=
  (Valuation.IsEquiv.eq_zero h).ne

end IsEquiv

section Supp

variable [LinearOrderedAddCommMonoidWithTop Γ₀] [CommRing R] (v : AddValuation R Γ₀)

/--
Definition of `supp` / `supp` 的定义

English:
definition supp
  signature: : Ideal R
  body: Valuation.supp v

@[simp]

中文:
定义 supp
  签名: : 理想 R
  定义体: Valuation.supp v

@[simp]

Depends on / 依赖: Valuation, Valuation.supp
-/
def supp : Ideal R :=
  Valuation.supp v

@[simp]
/--
theorem `mem_supp_iff` / 定理 `mem_supp_iff`

English:
theorem mem_supp_iff
  given: (x : R)
  statement: x in supp v ↔ v x = (⊤ : Γ₀)
  proof: Valuation.mem_supp_iff v x

中文:
定理 mem_supp_iff
  条件: (x : R)
  结论: x in supp v ↔ v x = (⊤ : Γ₀)
  证明: Valuation.mem_supp_iff v x

Depends on / 依赖: Valuation, Valuation.mem_supp_iff, mem_supp_iff
-/
theorem mem_supp_iff (x : R) : x in supp v ↔ v x = (⊤ : Γ₀) :=
  Valuation.mem_supp_iff v x

/--
theorem `map_add_supp` / 定理 `map_add_supp`

English:
theorem map_add_supp
  given: (a : R) {s : R} (h : s in supp v)
  statement: v (a + s) = v a
  proof: Valuation.map_add_supp v a h

中文:
定理 map_add_supp
  条件: (a : R) {s : R} (h : s in supp v)
  结论: v (a + s) = v a
  证明: Valuation.map_add_supp v a h

Depends on / 依赖: Valuation, Valuation.map_add_supp, map_add_supp
-/
theorem map_add_supp (a : R) {s : R} (h : s in supp v) : v (a + s) = v a :=
  Valuation.map_add_supp v a h

end Supp

end AddValuation

namespace Valuation

variable {K Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]

/--
Definition of `toAddValuation` / `toAddValuation` 的定义

English:
definition toAddValuation
  signature: : Valuation R Γ₀ ≃ AddValuation R (Additive Γ₀)ᵒᵈ
  body: .trans (congr
    { toFun := fun x => .ofAdd <| .toDual <| .toDual <| .ofMul x
      invFun := fun x => x.toAdd.ofDual.ofDual.toMul
      map_mul' := fun _x _y => rfl
      map_le_map_iff' := .rfl }) (AddValuation.ofValuation (R := R) (Γ₀ := (Additive Γ₀)ᵒᵈ))

中文:
定义 toAddValuation
  签名: : 赋值 R Γ₀ ≃ AddValuation R (加性 Γ₀)ᵒᵈ
  定义体: .trans (congr
    { toFun := fun x => .ofAdd <| .toDual <| .toDual <| .ofMul x
      invFun := fun x => x.toAdd.ofDual.ofDual.toMul
      map_mul' := fun _x _y => rfl
      map_le_map_iff' := .rfl }) (AddValuation.ofValuation (R := R) (Γ₀ := (Additive Γ₀)ᵒᵈ))

Depends on / 依赖: AddValuation, AddValuation.ofValuation, Additive, invFun, map_le_map_iff, map_mul, ofDual, ofValuation, toDual, x.toAdd.ofDual.ofDual.toMul
-/
def toAddValuation : Valuation R Γ₀ ≃ AddValuation R (Additive Γ₀)ᵒᵈ :=
  .trans (congr
    { toFun := fun x => .ofAdd <| .toDual <| .toDual <| .ofMul x
      invFun := fun x => x.toAdd.ofDual.ofDual.toMul
      map_mul' := fun _x _y => rfl
      map_le_map_iff' := .rfl }) (AddValuation.ofValuation (R := R) (Γ₀ := (Additive Γ₀)ᵒᵈ))

/--
Definition of `ofAddValuation` / `ofAddValuation` 的定义

English:
definition ofAddValuation
  signature: : AddValuation R (Additive Γ₀)ᵒᵈ ≃ Valuation R Γ₀
  body: AddValuation.toValuation.trans congr
    { toFun := fun x => x.toAdd.ofDual.ofDual.toMul
invFun := fun x => .ofAdd .toDual .toDual .ofMul x
      map_mul' := fun _x _y => rfl
      map_le_map_iff' := .rfl }

@[simp]

中文:
定义 ofAddValuation
  签名: : AddValuation R (加性 Γ₀)ᵒᵈ ≃ 赋值 R Γ₀
  定义体: AddValuation.toValuation.trans congr
    { toFun := fun x => x.toAdd.ofDual.ofDual.toMul
invFun := fun x => .ofAdd .toDual .toDual .ofMul x
      map_mul' := fun _x _y => rfl
      map_le_map_iff' := .rfl }

@[simp]

Depends on / 依赖: AddValuation, AddValuation.toValuation.trans, invFun, map_le_map_iff, map_mul, ofDual, toDual, toValuation, x.toAdd.ofDual.ofDual.toMul
-/
def ofAddValuation : AddValuation R (Additive Γ₀)ᵒᵈ ≃ Valuation R Γ₀ :=
AddValuation.toValuation.trans congr
    { toFun := fun x => x.toAdd.ofDual.ofDual.toMul
invFun := fun x => .ofAdd .toDual .toDual .ofMul x
      map_mul' := fun _x _y => rfl
      map_le_map_iff' := .rfl }

@[simp]
/--
lemma `ofAddValuation_symm_eq` / 引理 `ofAddValuation_symm_eq`

English:
lemma ofAddValuation_symm_eq
  statement: ofAddValuation.symm = toAddValuation (R := R) (Γ₀ := Γ₀)
  proof: rfl

@[simp]

中文:
引理 ofAddValuation_symm_eq
  结论: ofAddValuation.symm = toAddValuation (R := R) (Γ₀ := Γ₀)
  证明: rfl

@[simp]
-/
lemma ofAddValuation_symm_eq : ofAddValuation.symm = toAddValuation (R := R) (Γ₀ := Γ₀) := rfl

@[simp]
/--
lemma `toAddValuation_symm_eq` / 引理 `toAddValuation_symm_eq`

English:
lemma toAddValuation_symm_eq
  statement: toAddValuation.symm = ofAddValuation (R := R) (Γ₀ := Γ₀)
  proof: rfl

@[simp]

中文:
引理 toAddValuation_symm_eq
  结论: toAddValuation.symm = ofAddValuation (R := R) (Γ₀ := Γ₀)
  证明: rfl

@[simp]
-/
lemma toAddValuation_symm_eq : toAddValuation.symm = ofAddValuation (R := R) (Γ₀ := Γ₀) := rfl

@[simp]
/--
lemma `ofAddValuation_toAddValuation` / 引理 `ofAddValuation_toAddValuation`

English:
lemma ofAddValuation_toAddValuation
  given: (v : Valuation R Γ₀)
  statement: ofAddValuation (toAddValuation v) = v
  proof: rfl

@[simp]

中文:
引理 ofAddValuation_toAddValuation
  条件: (v : 赋值 R Γ₀)
  结论: ofAddValuation (toAddValuation v) = v
  证明: rfl

@[simp]
-/
lemma ofAddValuation_toAddValuation (v : Valuation R Γ₀) : ofAddValuation (toAddValuation v) = v :=
  rfl

@[simp]
/--
lemma `toValuation_ofValuation` / 引理 `toValuation_ofValuation`

English:
lemma toValuation_ofValuation
  given: (v : AddValuation R (Additive Γ₀)ᵒᵈ)
  proof: rfl

@[simp]

中文:
引理 toValuation_ofValuation
  条件: (v : AddValuation R (加性 Γ₀)ᵒᵈ)
  证明: rfl

@[simp]
-/
lemma toValuation_ofValuation (v : AddValuation R (Additive Γ₀)ᵒᵈ) :
    toAddValuation (ofAddValuation v) = v := rfl

@[simp]
/--
theorem `toAddValuation_apply` / 定理 `toAddValuation_apply`

English:
theorem toAddValuation_apply
  given: (v : Valuation R Γ₀) (r : R)
  proof: rfl

@[simp]

中文:
定理 toAddValuation_apply
  条件: (v : 赋值 R Γ₀) (r : R)
  证明: rfl

@[simp]
-/
theorem toAddValuation_apply (v : Valuation R Γ₀) (r : R) :
    toAddValuation v r = OrderDual.toDual (Additive.ofMul (v r)) :=
  rfl

@[simp]
/--
theorem `ofAddValuation_apply` / 定理 `ofAddValuation_apply`

English:
theorem ofAddValuation_apply
  given: (v : AddValuation R (Additive Γ₀)ᵒᵈ) (r : R)
  proof: rfl

中文:
定理 ofAddValuation_apply
  条件: (v : AddValuation R (加性 Γ₀)ᵒᵈ) (r : R)
  证明: rfl
-/
theorem ofAddValuation_apply (v : AddValuation R (Additive Γ₀)ᵒᵈ) (r : R) :
    ofAddValuation v r = Additive.toMul (OrderDual.ofDual (v r)) :=
  rfl

instance (v : Valuation R Γ₀) : CommMonoidWithZero (MonoidHom.mrange (.ofClass v : R ->*₀ _)) :=
  inferInstanceAs (CommMonoidWithZero (MonoidHom.mrange (MonoidWithZeroHom.ofClass v)))

@[simp]
/--
lemma `val_mrange_zero` / 引理 `val_mrange_zero`

English:
lemma val_mrange_zero
  given: (v : Valuation R Γ₀)
  proof: rfl

中文:
引理 val_mrange_zero
  条件: (v : 赋值 R Γ₀)
  证明: rfl
-/
lemma val_mrange_zero (v : Valuation R Γ₀) :
    ((0 : MonoidHom.mrange (.ofClass v : R ->*₀ _)) : Γ₀) = 0 :=
  rfl

instance {Γ₀} [LinearOrderedCommGroupWithZero Γ₀] [DivisionRing K] (v : Valuation K Γ₀) :
    CommGroupWithZero (MonoidHom.mrange (.ofClass v : K ->*₀ _)) :=
  inferInstanceAs (CommGroupWithZero (MonoidHom.mrange (MonoidWithZeroHom.ofClass v)))

end Valuation
