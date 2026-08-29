/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-! # The `WithLp` type synonym

`WithLp p V` is a copy of `V` with exactly the same vector space structure, but with the Lp norm
instead of any existing norm on `V`; recall that by default `ι → R` and `R × R` are equipped with
a norm defined as the supremum of the norms of their components.

This file defines the vector space structure for all types `V`; the norm structure is built for
different specializations of `V` in downstream files.

Note that this should not be used for infinite products, as in these cases the "right" Lp spaces is
not the same as the direct product of the spaces. See the docstring in `Mathlib/Analysis/PiLp` for
more details.

## Main definitions

* `WithLp p V`: a copy of `V` to be equipped with an L`p` norm.
* `WithLp.toLp`: the canonical inclusion from `V` to `WithLp p V`.
* `WithLp.ofLp`: the canonical inclusion from `WithLp p V` to `V`.
* `WithLp.linearEquiv p K V`: the canonical `K`-module isomorphism between `WithLp p V` and `V`.

## Implementation notes

The pattern here is the same one as is used by `Lex` for order structures; it avoids having a
separate synonym for each type (`ProdLp`, `PiLp`, etc), and allows all the structure-copying code
to be shared.

TODO: is it safe to copy across the topology and uniform space structure too for all reasonable
choices of `V`?
-/

@[expose] public section


open scoped ENNReal

/--
Definition of `WithLp` / `WithLp` 的定义

English:
structure WithLp
  parameters: (p : Real>=0∞) (V : Type*)
  axioms and operations (2):
    - toLp((p)) : :
    - ofLp : V

中文:
结构 WithLp
  参数: (p : 实数>=0∞) (V : 类型)
  公理与运算 (2 个):
    - toLp((p)) : :
    - ofLp : V
-/
structure WithLp (p : Real>=0∞) (V : Type*) where
  /-- Converts an element of `V` to an element of `WithLp p V`. -/
  toLp (p) ::
  /-- Converts an element of `WithLp p V` to an element of `V`. -/
  ofLp : V

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `toLp p x` being printed as `{ ofLp := x }` by `delabStructureInstance`. -/
@[app_delab WithLp.toLp]
meta def WithLp.delabToLp : Delab := delabApp

end Notation

variable (p : Real>=0∞) (K K' : Type*) {K'' : Type*} (V : Type*) {V' V'' : Type*}

namespace WithLp

/-- `WithLp.ofLp` and `WithLp.toLp` as an equivalence. -/
@[simps]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : WithLp p V ≃ V where
  body: ofLp
  invFun := toLp p
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]

中文:
定义 equiv
  签名: : WithLp p V ≃ V where
  定义体: ofLp
  invFun := toLp p
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
-/
protected def equiv : WithLp p V ≃ V where
  toFun := ofLp
  invFun := toLp p
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
/--
lemma `equiv_symm_apply` / 引理 `equiv_symm_apply`

English:
lemma equiv_symm_apply
  statement: ⇑(WithLp.equiv p V).symm = toLp p
  proof: rfl

中文:
引理 equiv_symm_apply
  结论: ⇑(WithLp.equiv p V).symm = toLp p
  证明: rfl
-/
lemma equiv_symm_apply : ⇑(WithLp.equiv p V).symm = toLp p := rfl


/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: [Nontrivial V]
  body: (WithLp.equiv p V).nontrivial

中文:
实例 instNontrivial
  签名: [Nontrivial V]
  定义体: (WithLp.equiv p V).nontrivial

Depends on / 依赖: WithLp, WithLp.equiv, nontrivial
-/
instance instNontrivial [Nontrivial V] : Nontrivial (WithLp p V) := (WithLp.equiv p V).nontrivial
/--
Instance `instUnique` / 实例 `instUnique`

English:
instance instUnique
  signature: [Unique V]
  body: (WithLp.equiv p V).unique

中文:
实例 instUnique
  签名: [Unique V]
  定义体: (WithLp.equiv p V).unique

Depends on / 依赖: WithLp, WithLp.equiv, unique
-/
instance instUnique [Unique V] : Unique (WithLp p V) := (WithLp.equiv p V).unique
/--
Instance `instDecidableEq` / 实例 `instDecidableEq`

English:
instance instDecidableEq
  signature: [DecidableEq V]
  body: (WithLp.equiv p V).decidableEq

中文:
实例 instDecidableEq
  签名: [DecidableEq V]
  定义体: (WithLp.equiv p V).decidableEq

Depends on / 依赖: WithLp, WithLp.equiv, decidableEq
-/
instance instDecidableEq [DecidableEq V] : DecidableEq (WithLp p V) :=
  (WithLp.equiv p V).decidableEq

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: [AddCommGroup V]
  body: (WithLp.equiv p V).addCommGroup

中文:
实例 instAddCommGroup
  签名: [AddCommGroup V]
  定义体: (WithLp.equiv p V).addCommGroup

Depends on / 依赖: Monoid, MulAction, WithLp, WithLp.equiv, addCommGroup, fast_instance, instMulAction, instSMul, instance, mulAction, to_additive
-/
instance instAddCommGroup [AddCommGroup V] : AddCommGroup (WithLp p V) :=
  (WithLp.equiv p V).addCommGroup
/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: [SMul K V]
  body: (WithLp.equiv p V).smul K

中文:
实例 instSMul
  签名: [SMul K V]
  定义体: (WithLp.equiv p V).smul K
-/
@[to_additive] instance instSMul [SMul K V] : SMul K (WithLp p V) :=
  (WithLp.equiv p V).smul K
/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: [Monoid K] [MulAction K V]
  body: fast_instance% (WithLp.equiv p V).mulAction K

中文:
实例 instMulAction
  签名: [Monoid K] [MulAction K V]
  定义体: fast_instance% (WithLp.equiv p V).mulAction K
-/
@[to_additive] instance instMulAction [Monoid K] [MulAction K V] : MulAction K (WithLp p V) :=
  fast_instance% (WithLp.equiv p V).mulAction K
/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: [Monoid K] [AddCommGroup V] [DistribMulAction K V]
  body: fast_instance% (WithLp.equiv p V).distribMulAction K

中文:
实例 instDistribMulAction
  签名: [Monoid K] [AddCommGroup V] [DistribMulAction K V]
  定义体: fast_instance% (WithLp.equiv p V).distribMulAction K

Depends on / 依赖: WithLp, WithLp.equiv, distribMulAction, fast_instance
-/
instance instDistribMulAction [Monoid K] [AddCommGroup V] [DistribMulAction K V] :
    DistribMulAction K (WithLp p V) := fast_instance% (WithLp.equiv p V).distribMulAction K
/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring K] [AddCommGroup V] [Module K V]
  body: fast_instance% (WithLp.equiv p V).module K

中文:
实例 instModule
  签名: [Semiring K] [AddCommGroup V] [Module K V]
  定义体: fast_instance% (WithLp.equiv p V).module K

Depends on / 依赖: WithLp, WithLp.equiv, fast_instance, module
-/
instance instModule [Semiring K] [AddCommGroup V] [Module K V] : Module K (WithLp p V) :=
  fast_instance% (WithLp.equiv p V).module K

variable {K V}

/--
lemma `ofLp_toLp` / 引理 `ofLp_toLp`

English:
lemma ofLp_toLp
  given: (x : V)
  statement: ofLp (toLp p x) = x
  proof: rfl

中文:
引理 ofLp_toLp
  条件: (x : V)
  结论: ofLp (toLp p x) = x
  证明: rfl
-/
lemma ofLp_toLp (x : V) : ofLp (toLp p x) = x := rfl
/--
lemma `toLp_ofLp` / 引理 `toLp_ofLp`

English:
lemma toLp_ofLp
  given: (x : WithLp p V)
  statement: toLp p (ofLp x) = x
  proof: rfl

中文:
引理 toLp_ofLp
  条件: (x : WithLp p V)
  结论: toLp p (ofLp x) = x
  证明: rfl
-/
@[simp] lemma toLp_ofLp (x : WithLp p V) : toLp p (ofLp x) = x := rfl

/--
lemma `ext_iff` / 引理 `ext_iff`

English:
lemma ext_iff
  given: {x y : WithLp p V}
  statement: x = y ↔ x.ofLp = y.ofLp
  proof: (WithLp.equiv p V).injective.eq_iff.symm

中文:
引理 ext_iff
  条件: {x y : WithLp p V}
  结论: x = y ↔ x.ofLp = y.ofLp
  证明: (WithLp.equiv p V).injective.eq_iff.symm

Depends on / 依赖: WithLp, WithLp.equiv, eq_iff, injective, injective.eq_iff.symm
-/
lemma ext_iff {x y : WithLp p V} : x = y ↔ x.ofLp = y.ofLp :=
  (WithLp.equiv p V).injective.eq_iff.symm

/--
lemma `ofLp_surjective` / 引理 `ofLp_surjective`

English:
lemma ofLp_surjective
  statement: Function.Surjective (@ofLp p V)
  proof: Function.RightInverse.surjective ofLp_toLp _

中文:
引理 ofLp_surjective
  结论: Function.Surjective (@ofLp p V)
  证明: Function.RightInverse.surjective ofLp_toLp _

Depends on / 依赖: Function, Function.RightInverse.surjective, RightInverse, ofLp_toLp, surjective
-/
lemma ofLp_surjective : Function.Surjective (@ofLp p V) :=
Function.RightInverse.surjective ofLp_toLp _

/--
lemma `toLp_surjective` / 引理 `toLp_surjective`

English:
lemma toLp_surjective
  statement: Function.Surjective (@toLp p V)
  proof: Function.RightInverse.surjective toLp_ofLp _

中文:
引理 toLp_surjective
  结论: Function.Surjective (@toLp p V)
  证明: Function.RightInverse.surjective toLp_ofLp _

Depends on / 依赖: Function, Function.RightInverse.surjective, RightInverse, surjective, toLp_ofLp
-/
lemma toLp_surjective : Function.Surjective (@toLp p V) :=
Function.RightInverse.surjective toLp_ofLp _

/--
lemma `ofLp_injective` / 引理 `ofLp_injective`

English:
lemma ofLp_injective
  statement: Function.Injective (@ofLp p V)
  proof: Function.LeftInverse.injective toLp_ofLp _

中文:
引理 ofLp_injective
  结论: Function.Injective (@ofLp p V)
  证明: Function.LeftInverse.injective toLp_ofLp _

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, injective, toLp_ofLp
-/
lemma ofLp_injective : Function.Injective (@ofLp p V) :=
Function.LeftInverse.injective toLp_ofLp _

/--
lemma `toLp_injective` / 引理 `toLp_injective`

English:
lemma toLp_injective
  statement: Function.Injective (@toLp p V)
  proof: Function.LeftInverse.injective ofLp_toLp _

中文:
引理 toLp_injective
  结论: Function.Injective (@toLp p V)
  证明: Function.LeftInverse.injective ofLp_toLp _

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, injective, ofLp_toLp
-/
lemma toLp_injective : Function.Injective (@toLp p V) :=
Function.LeftInverse.injective ofLp_toLp _

/--
lemma `ofLp_bijective` / 引理 `ofLp_bijective`

English:
lemma ofLp_bijective
  statement: Function.Bijective (@ofLp p V)
  proof: ⟨ofLp_injective p, ofLp_surjective p⟩

中文:
引理 ofLp_bijective
  结论: Function.Bijective (@ofLp p V)
  证明: ⟨ofLp_injective p, ofLp_surjective p⟩

Depends on / 依赖: ofLp_injective, ofLp_surjective
-/
lemma ofLp_bijective : Function.Bijective (@ofLp p V) :=
  ⟨ofLp_injective p, ofLp_surjective p⟩

/--
lemma `toLp_bijective` / 引理 `toLp_bijective`

English:
lemma toLp_bijective
  statement: Function.Bijective (@toLp p V)
  proof: ⟨toLp_injective p, toLp_surjective p⟩

中文:
引理 toLp_bijective
  结论: Function.Bijective (@toLp p V)
  证明: ⟨toLp_injective p, toLp_surjective p⟩

Depends on / 依赖: toLp_injective, toLp_surjective
-/
lemma toLp_bijective : Function.Bijective (@toLp p V) :=
  ⟨toLp_injective p, toLp_surjective p⟩

/-- Lift a function to `WithLp`. -/
@[simp]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : V -> V') (x : WithLp p V)
  body: toLp p (f x.ofLp)

@[simp]

中文:
定义 map
  签名: (f : V -> V') (x : WithLp p V)
  定义体: toLp p (f x.ofLp)

@[simp]
-/
protected def map (f : V -> V') (x : WithLp p V) : WithLp p V' :=
  toLp p (f x.ofLp)

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: WithLp.map p (id (α := V)) = id
  proof: rfl

中文:
定理 map_id
  结论: WithLp.map p (id (α := V)) = id
  证明: rfl
-/
theorem map_id : WithLp.map p (id (α := V)) = id :=
  rfl

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (f : V' -> V'') (g : V -> V')
  proof: rfl

中文:
定理 map_comp
  条件: (f : V' -> V'') (g : V -> V')
  证明: rfl
-/
theorem map_comp (f : V' -> V'') (g : V -> V') :
    WithLp.map p (f ∘ g) = WithLp.map p f ∘ WithLp.map p g :=
  rfl

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (f : V ≃ V')
  body: (WithLp.equiv p V).trans f.trans (WithLp.equiv p V').symm

@[simp]

中文:
定义 congr
  签名: (f : V ≃ V')
  定义体: (WithLp.equiv p V).trans f.trans (WithLp.equiv p V').symm

@[simp]
-/
protected def congr (f : V ≃ V') : WithLp p V ≃ WithLp p V' :=
(WithLp.equiv p V).trans f.trans (WithLp.equiv p V').symm

@[simp]
/--
theorem `coe_congr` / 定理 `coe_congr`

English:
theorem coe_congr
  given: (f : V ≃ V')
  statement: ⇑(WithLp.congr p f) = WithLp.map p f
  proof: rfl

@[simp]

中文:
定理 coe_congr
  条件: (f : V ≃ V')
  结论: ⇑(WithLp.congr p f) = WithLp.map p f
  证明: rfl

@[simp]
-/
theorem coe_congr (f : V ≃ V') : ⇑(WithLp.congr p f) = WithLp.map p f :=
  rfl

@[simp]
/--
theorem `congr_refl` / 定理 `congr_refl`

English:
theorem congr_refl
  statement: WithLp.congr p (Equiv.refl V) = Equiv.refl _
  proof: rfl

@[simp]

中文:
定理 congr_refl
  结论: WithLp.congr p (Equiv.refl V) = Equiv.refl _
  证明: rfl

@[simp]
-/
theorem congr_refl : WithLp.congr p (Equiv.refl V) = Equiv.refl _ :=
  rfl

@[simp]
/--
theorem `congr_symm` / 定理 `congr_symm`

English:
theorem congr_symm
  given: (f : V ≃ V')
  statement: (WithLp.congr p f).symm = WithLp.congr p f.symm
  proof: rfl

中文:
定理 congr_symm
  条件: (f : V ≃ V')
  结论: (WithLp.congr p f).symm = WithLp.congr p f.symm
  证明: rfl
-/
theorem congr_symm (f : V ≃ V') : (WithLp.congr p f).symm = WithLp.congr p f.symm :=
  rfl

/--
theorem `congr_trans` / 定理 `congr_trans`

English:
theorem congr_trans
  given: (f : V ≃ V') (g : V' ≃ V'')
  proof: rfl

中文:
定理 congr_trans
  条件: (f : V ≃ V') (g : V' ≃ V'')
  证明: rfl
-/
theorem congr_trans (f : V ≃ V') (g : V' ≃ V'') :
    WithLp.congr p (f.trans g) = (WithLp.congr p f).trans (WithLp.congr p g) :=
  rfl

section AddCommGroup
variable [AddCommGroup V]

/--
lemma `toLp_zero` / 引理 `toLp_zero`

English:
lemma toLp_zero
  statement: toLp p (0 : V) = 0
  proof: rfl

中文:
引理 toLp_zero
  结论: toLp p (0 : V) = 0
  证明: rfl
-/
@[simp] lemma toLp_zero : toLp p (0 : V) = 0 := rfl
/--
lemma `ofLp_zero` / 引理 `ofLp_zero`

English:
lemma ofLp_zero
  statement: ofLp (0 : WithLp p V) = 0
  proof: rfl

中文:
引理 ofLp_zero
  结论: ofLp (0 : WithLp p V) = 0
  证明: rfl
-/
@[simp] lemma ofLp_zero : ofLp (0 : WithLp p V) = 0 := rfl

/--
lemma `toLp_add` / 引理 `toLp_add`

English:
lemma toLp_add
  given: (x y : V)
  statement: toLp p (x + y) = toLp p x + toLp p y
  proof: rfl

中文:
引理 toLp_add
  条件: (x y : V)
  结论: toLp p (x + y) = toLp p x + toLp p y
  证明: rfl
-/
@[simp] lemma toLp_add (x y : V) : toLp p (x + y) = toLp p x + toLp p y := rfl
/--
lemma `ofLp_add` / 引理 `ofLp_add`

English:
lemma ofLp_add
  given: (x y : WithLp p V)
  statement: ofLp (x + y) = ofLp x + ofLp y
  proof: rfl

中文:
引理 ofLp_add
  条件: (x y : WithLp p V)
  结论: ofLp (x + y) = ofLp x + ofLp y
  证明: rfl
-/
@[simp] lemma ofLp_add (x y : WithLp p V) : ofLp (x + y) = ofLp x + ofLp y := rfl

/--
lemma `toLp_sub` / 引理 `toLp_sub`

English:
lemma toLp_sub
  given: (x y : V)
  statement: toLp p (x - y) = toLp p x - toLp p y
  proof: rfl

中文:
引理 toLp_sub
  条件: (x y : V)
  结论: toLp p (x - y) = toLp p x - toLp p y
  证明: rfl
-/
@[simp] lemma toLp_sub (x y : V) : toLp p (x - y) = toLp p x - toLp p y := rfl
/--
lemma `ofLp_sub` / 引理 `ofLp_sub`

English:
lemma ofLp_sub
  given: (x y : WithLp p V)
  statement: ofLp (x - y) = ofLp x - ofLp y
  proof: rfl

中文:
引理 ofLp_sub
  条件: (x y : WithLp p V)
  结论: ofLp (x - y) = ofLp x - ofLp y
  证明: rfl
-/
@[simp] lemma ofLp_sub (x y : WithLp p V) : ofLp (x - y) = ofLp x - ofLp y := rfl

/--
lemma `toLp_neg` / 引理 `toLp_neg`

English:
lemma toLp_neg
  given: (x : V)
  statement: toLp p (-x) = -toLp p x
  proof: rfl

中文:
引理 toLp_neg
  条件: (x : V)
  结论: toLp p (-x) = -toLp p x
  证明: rfl
-/
@[simp] lemma toLp_neg (x : V) : toLp p (-x) = -toLp p x := rfl
/--
lemma `ofLp_neg` / 引理 `ofLp_neg`

English:
lemma ofLp_neg
  given: (x : WithLp p V)
  statement: ofLp (-x) = -ofLp x
  proof: rfl

中文:
引理 ofLp_neg
  条件: (x : WithLp p V)
  结论: ofLp (-x) = -ofLp x
  证明: rfl
-/
@[simp] lemma ofLp_neg (x : WithLp p V) : ofLp (-x) = -ofLp x := rfl

/--
lemma `toLp_eq_zero` / 引理 `toLp_eq_zero`

English:
lemma toLp_eq_zero
  given: {x : V}
  statement: toLp p x = 0 ↔ x = 0
  proof: (toLp_injective p).eq_iff

中文:
引理 toLp_eq_zero
  条件: {x : V}
  结论: toLp p x = 0 ↔ x = 0
  证明: (toLp_injective p).eq_iff
-/
@[simp] lemma toLp_eq_zero {x : V} : toLp p x = 0 ↔ x = 0 := (toLp_injective p).eq_iff
/--
lemma `ofLp_eq_zero` / 引理 `ofLp_eq_zero`

English:
lemma ofLp_eq_zero
  given: {x : WithLp p V}
  statement: ofLp x = 0 ↔ x = 0
  proof: (ofLp_injective p).eq_iff

中文:
引理 ofLp_eq_zero
  条件: {x : WithLp p V}
  结论: ofLp x = 0 ↔ x = 0
  证明: (ofLp_injective p).eq_iff
-/
@[simp] lemma ofLp_eq_zero {x : WithLp p V} : ofLp x = 0 ↔ x = 0 := (ofLp_injective p).eq_iff

end AddCommGroup

/--
lemma `toLp_smul` / 引理 `toLp_smul`

English:
lemma toLp_smul
  given: [SMul K V] (c : K) (x : V)
  statement: toLp p (c • x) = c • (toLp p x)
  proof: rfl

中文:
引理 toLp_smul
  条件: [SMul K V] (c : K) (x : V)
  结论: toLp p (c • x) = c • (toLp p x)
  证明: rfl
-/
@[simp] lemma toLp_smul [SMul K V] (c : K) (x : V) : toLp p (c • x) = c • (toLp p x) := rfl
/--
lemma `ofLp_smul` / 引理 `ofLp_smul`

English:
lemma ofLp_smul
  given: [SMul K V] (c : K) (x : WithLp p V)
  statement: ofLp (c • x) = c • ofLp x
  proof: rfl

@[to_additive]

中文:
引理 ofLp_smul
  条件: [SMul K V] (c : K) (x : WithLp p V)
  结论: ofLp (c • x) = c • ofLp x
  证明: rfl

@[to_additive]
-/
@[simp] lemma ofLp_smul [SMul K V] (c : K) (x : WithLp p V) : ofLp (c • x) = c • ofLp x := rfl

@[to_additive]
/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul K K'] [SMul K V] [SMul K' V] [IsScalarTower K K' V]
  body: (WithLp.equiv p V).isScalarTower K K'

@[to_additive]

中文:
实例 instIsScalarTower
  签名: [SMul K K'] [SMul K V] [SMul K' V] [IsScalarTower K K' V]
  定义体: (WithLp.equiv p V).isScalarTower K K'

@[to_additive]

Depends on / 依赖: WithLp, WithLp.equiv, isScalarTower
-/
instance instIsScalarTower [SMul K K'] [SMul K V] [SMul K' V] [IsScalarTower K K' V] :
    IsScalarTower K K' (WithLp p V) :=
  (WithLp.equiv p V).isScalarTower K K'

@[to_additive]
/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMul K V] [SMul K' V] [SMulCommClass K K' V]
  body: (WithLp.equiv p V).smulCommClass K K'

中文:
实例 instSMulCommClass
  签名: [SMul K V] [SMul K' V] [SMulCommClass K K' V]
  定义体: (WithLp.equiv p V).smulCommClass K K'

Depends on / 依赖: WithLp, WithLp.equiv, smulCommClass
-/
instance instSMulCommClass [SMul K V] [SMul K' V] [SMulCommClass K K' V] :
    SMulCommClass K K' (WithLp p V) :=
  (WithLp.equiv p V).smulCommClass K K'

variable (K V)

/-- `WithLp.equiv` as a group isomorphism. -/
@[simps apply symm_apply]
/--
Definition of `addEquiv` / `addEquiv` 的定义

English:
definition addEquiv
  signature: [AddCommGroup V]
  body: ofLp
  invFun := toLp p
  map_add' := ofLp_add p

中文:
定义 addEquiv
  签名: [AddCommGroup V]
  定义体: ofLp
  invFun := toLp p
  map_add' := ofLp_add p
-/
protected def addEquiv [AddCommGroup V] : WithLp p V ≃+ V where
  toFun := ofLp
  invFun := toLp p
  map_add' := ofLp_add p

/--
lemma `coe_addEquiv` / 引理 `coe_addEquiv`

English:
lemma coe_addEquiv
  given: [AddCommGroup V]
  statement: ⇑(WithLp.addEquiv p V) = ofLp
  proof: rfl

中文:
引理 coe_addEquiv
  条件: [AddCommGroup V]
  结论: ⇑(WithLp.addEquiv p V) = ofLp
  证明: rfl
-/
lemma coe_addEquiv [AddCommGroup V] : ⇑(WithLp.addEquiv p V) = ofLp := rfl

/--
lemma `coe_symm_addEquiv` / 引理 `coe_symm_addEquiv`

English:
lemma coe_symm_addEquiv
  given: [AddCommGroup V]
  statement: ⇑(WithLp.addEquiv p V).symm = toLp p
  proof: rfl

@[simp]

中文:
引理 coe_symm_addEquiv
  条件: [AddCommGroup V]
  结论: ⇑(WithLp.addEquiv p V).symm = toLp p
  证明: rfl

@[simp]
-/
lemma coe_symm_addEquiv [AddCommGroup V] : ⇑(WithLp.addEquiv p V).symm = toLp p := rfl

@[simp]
/--
lemma `ofLp_sum` / 引理 `ofLp_sum`

English:
lemma ofLp_sum
  given: [AddCommGroup V] {ι : Type*} (s : Finset ι) (f : ι -> WithLp p V)
  proof: map_sum (WithLp.addEquiv _ _) _ _

@[simp]

中文:
引理 ofLp_sum
  条件: [AddCommGroup V] {ι : 类型} (s : Finset ι) (f : ι -> WithLp p V)
  证明: map_sum (WithLp.addEquiv _ _) _ _

@[simp]

Depends on / 依赖: WithLp, WithLp.addEquiv, addEquiv, map_sum
-/
lemma ofLp_sum [AddCommGroup V] {ι : Type*} (s : Finset ι) (f : ι -> WithLp p V) :
    (∑ i in s, f i).ofLp = ∑ i in s, (f i).ofLp :=
  map_sum (WithLp.addEquiv _ _) _ _

@[simp]
/--
lemma `toLp_sum` / 引理 `toLp_sum`

English:
lemma toLp_sum
  given: [AddCommGroup V] {ι : Type*} (s : Finset ι) (f : ι -> V)
  proof: map_sum (WithLp.addEquiv _ _).symm _ _

@[simp]

中文:
引理 toLp_sum
  条件: [AddCommGroup V] {ι : 类型} (s : Finset ι) (f : ι -> V)
  证明: map_sum (WithLp.addEquiv _ _).symm _ _

@[simp]

Depends on / 依赖: WithLp, WithLp.addEquiv, addEquiv, map_sum
-/
lemma toLp_sum [AddCommGroup V] {ι : Type*} (s : Finset ι) (f : ι -> V) :
    toLp p (∑ i in s, f i) = ∑ i in s, toLp p (f i) :=
  map_sum (WithLp.addEquiv _ _).symm _ _

@[simp]
/--
lemma `ofLp_listSum` / 引理 `ofLp_listSum`

English:
lemma ofLp_listSum
  given: [AddCommGroup V] (l : List (WithLp p V))
  proof: map_list_sum (WithLp.addEquiv _ _) _

@[simp]

中文:
引理 ofLp_listSum
  条件: [AddCommGroup V] (l : List (WithLp p V))
  证明: map_list_sum (WithLp.addEquiv _ _) _

@[simp]

Depends on / 依赖: WithLp, WithLp.addEquiv, addEquiv, map_list_sum
-/
lemma ofLp_listSum [AddCommGroup V] (l : List (WithLp p V)) :
    l.sum.ofLp = (l.map ofLp).sum :=
  map_list_sum (WithLp.addEquiv _ _) _

@[simp]
/--
lemma `toLp_listSum` / 引理 `toLp_listSum`

English:
lemma toLp_listSum
  given: [AddCommGroup V] (l : List V)
  proof: map_list_sum (WithLp.addEquiv _ _).symm _

@[simp]

中文:
引理 toLp_listSum
  条件: [AddCommGroup V] (l : List V)
  证明: map_list_sum (WithLp.addEquiv _ _).symm _

@[simp]

Depends on / 依赖: WithLp, WithLp.addEquiv, addEquiv, map_list_sum
-/
lemma toLp_listSum [AddCommGroup V] (l : List V) :
    toLp p l.sum = (l.map (toLp p)).sum :=
  map_list_sum (WithLp.addEquiv _ _).symm _

@[simp]
/--
lemma `ofLp_multisetSum` / 引理 `ofLp_multisetSum`

English:
lemma ofLp_multisetSum
  given: [AddCommGroup V] (s : Multiset (WithLp p V))
  proof: map_multiset_sum (WithLp.addEquiv _ _) _

@[simp]

中文:
引理 ofLp_multisetSum
  条件: [AddCommGroup V] (s : Multiset (WithLp p V))
  证明: map_multiset_sum (WithLp.addEquiv _ _) _

@[simp]

Depends on / 依赖: WithLp, WithLp.addEquiv, addEquiv, map_multiset_sum
-/
lemma ofLp_multisetSum [AddCommGroup V] (s : Multiset (WithLp p V)) :
    s.sum.ofLp = (s.map ofLp).sum :=
  map_multiset_sum (WithLp.addEquiv _ _) _

@[simp]
/--
lemma `toLp_multisetSum` / 引理 `toLp_multisetSum`

English:
lemma toLp_multisetSum
  given: [AddCommGroup V] (s : Multiset V)
  proof: map_multiset_sum (WithLp.addEquiv _ _).symm _

中文:
引理 toLp_multisetSum
  条件: [AddCommGroup V] (s : Multiset V)
  证明: map_multiset_sum (WithLp.addEquiv _ _).symm _

Depends on / 依赖: WithLp, WithLp.addEquiv, addEquiv, map_multiset_sum
-/
lemma toLp_multisetSum [AddCommGroup V] (s : Multiset V) :
    toLp p s.sum = (s.map (toLp p)).sum :=
  map_multiset_sum (WithLp.addEquiv _ _).symm _

/-- `WithLp.equiv` as a linear equivalence. -/
@[simps apply symm_apply]
/--
Definition of `linearEquiv` / `linearEquiv` 的定义

English:
definition linearEquiv
  signature: [Semiring K] [AddCommGroup V] [Module K V]
  body: WithLp.addEquiv p V
  map_smul' _ _ := rfl

中文:
定义 linearEquiv
  签名: [Semiring K] [AddCommGroup V] [Module K V]
  定义体: WithLp.addEquiv p V
  map_smul' _ _ := rfl
-/
protected def linearEquiv [Semiring K] [AddCommGroup V] [Module K V] : WithLp p V ≃ₗ[K] V where
  __ := WithLp.addEquiv p V
  map_smul' _ _ := rfl

/--
lemma `coe_linearEquiv` / 引理 `coe_linearEquiv`

English:
lemma coe_linearEquiv
  given: [Semiring K] [AddCommGroup V] [Module K V]
  proof: rfl

中文:
引理 coe_linearEquiv
  条件: [Semiring K] [AddCommGroup V] [Module K V]
  证明: rfl
-/
lemma coe_linearEquiv [Semiring K] [AddCommGroup V] [Module K V] :
    ⇑(WithLp.linearEquiv p K V) = ofLp := rfl

/--
lemma `coe_symm_linearEquiv` / 引理 `coe_symm_linearEquiv`

English:
lemma coe_symm_linearEquiv
  given: [Semiring K] [AddCommGroup V] [Module K V]
  proof: rfl

@[simp]

中文:
引理 coe_symm_linearEquiv
  条件: [Semiring K] [AddCommGroup V] [Module K V]
  证明: rfl

@[simp]
-/
lemma coe_symm_linearEquiv [Semiring K] [AddCommGroup V] [Module K V] :
    ⇑(WithLp.linearEquiv p K V).symm = toLp p := rfl

@[simp]
/--
lemma `toAddEquiv_linearEquiv` / 引理 `toAddEquiv_linearEquiv`

English:
lemma toAddEquiv_linearEquiv
  given: [Semiring K] [AddCommGroup V] [Module K V]
  proof: rfl

中文:
引理 toAddEquiv_linearEquiv
  条件: [Semiring K] [AddCommGroup V] [Module K V]
  证明: rfl
-/
lemma toAddEquiv_linearEquiv [Semiring K] [AddCommGroup V] [Module K V] :
    (WithLp.linearEquiv p K V).toAddEquiv = WithLp.addEquiv p V := rfl

/--
Instance `instModuleFinite` / 实例 `instModuleFinite`

English:
instance instModuleFinite
  body: Module.Finite.equiv (WithLp.linearEquiv p K V).symm

中文:
实例 instModuleFinite
  定义体: Module.Finite.equiv (WithLp.linearEquiv p K V).symm

Depends on / 依赖: Finite, Module, Module.Finite.equiv, WithLp, WithLp.linearEquiv, linearEquiv
-/
instance instModuleFinite
    [Semiring K] [AddCommGroup V] [Module K V] [Module.Finite K V] :
    Module.Finite K (WithLp p V) :=
  Module.Finite.equiv (WithLp.linearEquiv p K V).symm

end WithLp

section

variable {K K' V} [Semiring K] [Semiring K'] [Semiring K'']
  {σ : K ->+* K'} {σ' : K' ->+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  {τ : K' ->+* K''} {τ' : K'' ->+* K'} [RingHomInvPair τ τ'] [RingHomInvPair τ' τ]
  {ρ : K ->+* K''} {ρ' : K'' ->+* K} [RingHomInvPair ρ ρ'] [RingHomInvPair ρ' ρ]
  [RingHomCompTriple σ τ ρ] [RingHomCompTriple τ' σ' ρ']
  [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K' V'] [AddCommGroup V''] [Module K'' V'']

namespace LinearMap

/--
Definition of `withLpMap` / `withLpMap` 的定义

English:
definition withLpMap
  signature: (f : V ->ₛₗ[σ] V')
  body: (WithLp.linearEquiv p K' V').symm.toLinearMap ∘ₛₗ f ∘ₛₗ (WithLp.linearEquiv p K V).toLinearMap

@[simp]

中文:
定义 withLpMap
  签名: (f : V ->ₛₗ[σ] V')
  定义体: (WithLp.linearEquiv p K' V').symm.toLinearMap ∘ₛₗ f ∘ₛₗ (WithLp.linearEquiv p K V).toLinearMap

@[simp]

Depends on / 依赖: WithLp, WithLp.linearEquiv, linearEquiv, symm.toLinearMap, toLinearMap
-/
def withLpMap (f : V ->ₛₗ[σ] V') : WithLp p V ->ₛₗ[σ] WithLp p V' :=
  (WithLp.linearEquiv p K' V').symm.toLinearMap ∘ₛₗ f ∘ₛₗ (WithLp.linearEquiv p K V).toLinearMap

@[simp]
/--
theorem `coe_withLpMap` / 定理 `coe_withLpMap`

English:
theorem coe_withLpMap
  given: (f : V ->ₛₗ[σ] V')
  statement: ⇑(withLpMap p f) = WithLp.map p f
  proof: rfl

@[simp]

中文:
定理 coe_withLpMap
  条件: (f : V ->ₛₗ[σ] V')
  结论: ⇑(withLpMap p f) = WithLp.map p f
  证明: rfl

@[simp]
-/
theorem coe_withLpMap (f : V ->ₛₗ[σ] V') : ⇑(withLpMap p f) = WithLp.map p f :=
  rfl

@[simp]
/--
theorem `withLpMap_id` / 定理 `withLpMap_id`

English:
theorem withLpMap_id
  statement: withLpMap p (LinearMap.id (R := K) (M := V)) = LinearMap.id
  proof: rfl

@[simp]

中文:
定理 withLpMap_id
  结论: withLpMap p (LinearMap.id (R := K) (M := V)) = LinearMap.id
  证明: rfl

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id
-/
theorem withLpMap_id : withLpMap p (LinearMap.id (R := K) (M := V)) = LinearMap.id :=
  rfl

@[simp]
/--
theorem `withLpMap_comp` / 定理 `withLpMap_comp`

English:
theorem withLpMap_comp
  given: (f : V' ->ₛₗ[τ] V'') (g : V ->ₛₗ[σ] V')
  proof: rfl

中文:
定理 withLpMap_comp
  条件: (f : V' ->ₛₗ[τ] V'') (g : V ->ₛₗ[σ] V')
  证明: rfl
-/
theorem withLpMap_comp (f : V' ->ₛₗ[τ] V'') (g : V ->ₛₗ[σ] V') :
    withLpMap p (f ∘ₛₗ g) = withLpMap p f ∘ₛₗ withLpMap p g :=
  rfl

end LinearMap

namespace LinearEquiv

/--
Definition of `withLpCongr` / `withLpCongr` 的定义

English:
definition withLpCongr
  signature: (f : V ≃ₛₗ[σ] V')
  body: (WithLp.linearEquiv p K V).trans f.trans (WithLp.linearEquiv p K' V').symm

@[simp]

中文:
定义 withLpCongr
  签名: (f : V ≃ₛₗ[σ] V')
  定义体: (WithLp.linearEquiv p K V).trans f.trans (WithLp.linearEquiv p K' V').symm

@[simp]

Depends on / 依赖: WithLp, WithLp.linearEquiv, f.trans, linearEquiv
-/
def withLpCongr (f : V ≃ₛₗ[σ] V') : WithLp p V ≃ₛₗ[σ] WithLp p V' :=
(WithLp.linearEquiv p K V).trans f.trans (WithLp.linearEquiv p K' V').symm

@[simp]
/--
theorem `coe_withLpCongr` / 定理 `coe_withLpCongr`

English:
theorem coe_withLpCongr
  given: (f : V ≃ₛₗ[σ] V')
  statement: ⇑(withLpCongr p f) = WithLp.map p f
  proof: rfl

@[simp]

中文:
定理 coe_withLpCongr
  条件: (f : V ≃ₛₗ[σ] V')
  结论: ⇑(withLpCongr p f) = WithLp.map p f
  证明: rfl

@[simp]
-/
theorem coe_withLpCongr (f : V ≃ₛₗ[σ] V') : ⇑(withLpCongr p f) = WithLp.map p f :=
  rfl

@[simp]
/--
theorem `withLpCongr_symm` / 定理 `withLpCongr_symm`

English:
theorem withLpCongr_symm
  given: (f : V ≃ₛₗ[σ] V')
  statement: (withLpCongr p f).symm = withLpCongr p f.symm
  proof: rfl

@[simp]

中文:
定理 withLpCongr_symm
  条件: (f : V ≃ₛₗ[σ] V')
  结论: (withLpCongr p f).symm = withLpCongr p f.symm
  证明: rfl

@[simp]
-/
theorem withLpCongr_symm (f : V ≃ₛₗ[σ] V') : (withLpCongr p f).symm = withLpCongr p f.symm :=
  rfl

@[simp]
/--
theorem `withLpCongr_refl` / 定理 `withLpCongr_refl`

English:
theorem withLpCongr_refl
  proof: rfl

中文:
定理 withLpCongr_refl
  证明: rfl
-/
theorem withLpCongr_refl :
    withLpCongr p (LinearEquiv.refl K V) = LinearEquiv.refl K _ :=
  rfl

/--
theorem `withLpCongr_trans` / 定理 `withLpCongr_trans`

English:
theorem withLpCongr_trans
  given: (f : V ≃ₛₗ[σ] V') (g : V' ≃ₛₗ[τ] V'')
  proof: rfl

中文:
定理 withLpCongr_trans
  条件: (f : V ≃ₛₗ[σ] V') (g : V' ≃ₛₗ[τ] V'')
  证明: rfl
-/
theorem withLpCongr_trans (f : V ≃ₛₗ[σ] V') (g : V' ≃ₛₗ[τ] V'') :
    withLpCongr p (f.trans g) = (withLpCongr p f).trans (withLpCongr p g) :=
  rfl

end LinearEquiv

end
