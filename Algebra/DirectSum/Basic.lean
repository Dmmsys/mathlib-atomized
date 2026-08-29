/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Data.DFinsupp.Sigma
public import Mathlib.Data.DFinsupp.Submonoid

/-!
# Direct sum

This file defines the direct sum of abelian groups, indexed by a discrete type.

## Notation

`⨁ i, β i` is the n-ary direct sum `DirectSum`.
This notation is in the `DirectSum` locale, accessible after `open DirectSum`.

## References

* https://en.wikipedia.org/wiki/Direct_sum
-/

@[expose] public section

open Function

universe u v w u₁

variable (ι : Type v) (β : ι -> Type w)

/-- `DirectSum ι β` is the direct sum of a family of additive commutative monoids `β i`.

Note: `open DirectSum` will enable the notation `⨁ i, β i` for `DirectSum ι β`. -/
@[implicit_reducible]
/--
Definition of `DirectSum` / `DirectSum` 的定义

English:
definition DirectSum
  signature: [forall i, AddCommMonoid (β i)]
  body: Π₀ i, β i

中文:
定义 DirectSum
  签名: [对任意 i, AddCommMonoid (β i)]
  定义体: Π₀ i, β i
-/
def DirectSum [forall i, AddCommMonoid (β i)] : Type _ :=
  Π₀ i, β i

set_option backward.inferInstanceAs.wrap.data false in
deriving instance CoeFun for DirectSum

/-- `⨁ i, f i` is notation for `DirectSum _ f` and equals the direct sum of `fun i ↦ f i`.
Taking the direct sum over multiple arguments is possible, e.g. `⨁ (i) (j), f i j`. -/
scoped[DirectSum] notation3 "⨁ "(...)", "r:(scoped f => DirectSum _ f) => r

-- Porting note: The below recreates some of the lean3 notation, not fully yet
-- section
-- open Batteries.ExtendedBinder
-- syntax (name := bigdirectsum) "⨁ " extBinders ", " term : term
-- macro_rules (kind := bigdirectsum)
-- | `(⨁ $_:ident, $y:ident → $z:ident) => `(DirectSum _ (fun $y ↦ $z))
-- | `(⨁ $x:ident, $p) => `(DirectSum _ (fun $x ↦ $p))
-- | `(⨁ $_:ident : $t:ident, $p) => `(DirectSum _ (fun $t ↦ $p))
-- | `(⨁ ($x:ident) ($y:ident), $p) => `(DirectSum _ (fun $x ↦ fun $y ↦ $p))
-- end

namespace DirectSum

variable {ι β}

-- This instance exists to avoid nsmul and zsmul diamonds.
instance {R : Type u} [Semiring R] [forall i, AddCommMonoid (β i)] [forall i, Module R (β i)] :
SMul R (⨁ i, β i) := inferInstanceAs SMul R (Π₀ (i : ι), β i)

deriving instance AddCommMonoid, Inhabited, DFunLike for DirectSum

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: ι] [forall i, AddCommMonoid (β i)] [forall i, DecidableEq (β i)] :
  body: inferInstanceAs DecidableEq (Π₀ i, β i)

中文:
实例 [DecidableEq
  签名: ι] [对任意 i, AddCommMonoid (β i)] [对任意 i, DecidableEq (β i)] :
  定义体: inferInstanceAs DecidableEq (Π₀ i, β i)

Depends on / 依赖: DecidableEq
-/
instance [DecidableEq ι] [forall i, AddCommMonoid (β i)] [forall i, DecidableEq (β i)] :
    DecidableEq (DirectSum ι β) :=
inferInstanceAs DecidableEq (Π₀ i, β i)

variable (β) in
/--
Definition of `coeFnAddMonoidHom` / `coeFnAddMonoidHom` 的定义

English:
definition coeFnAddMonoidHom
  signature: [forall i, AddCommMonoid (β i)]
  body: x
  __ := DFinsupp.coeFnAddMonoidHom

@[simp]

中文:
定义 coeFnAddMonoidHom
  签名: [对任意 i, AddCommMonoid (β i)]
  定义体: x
  __ := DFinsupp.coeFnAddMonoidHom

@[simp]
-/
def coeFnAddMonoidHom [forall i, AddCommMonoid (β i)] : (⨁ i, β i) ->+ (Π i, β i) where
  toFun x := x
  __ := DFinsupp.coeFnAddMonoidHom

@[simp]
/--
lemma `coeFnAddMonoidHom_apply` / 引理 `coeFnAddMonoidHom_apply`

English:
lemma coeFnAddMonoidHom_apply
  given: [forall i, AddCommMonoid (β i)] (v : ⨁ i, β i)
  proof: rfl

中文:
引理 coeFnAddMonoidHom_apply
  条件: [对任意 i, AddCommMonoid (β i)] (v : ⨁ i, β i)
  证明: rfl
-/
lemma coeFnAddMonoidHom_apply [forall i, AddCommMonoid (β i)] (v : ⨁ i, β i) :
    coeFnAddMonoidHom β v = v :=
  rfl

section AddCommGroup

variable [forall i, AddCommGroup (β i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (DirectSum ι β)
  body: inferInstanceAs (AddCommGroup (Π₀ i, β i))

@[simp]

中文:
实例 :
  签名: AddCommGroup (DirectSum ι β)
  定义体: inferInstanceAs (AddCommGroup (Π₀ i, β i))

@[simp]

Depends on / 依赖: AddCommGroup
-/
instance : AddCommGroup (DirectSum ι β) :=
  inferInstanceAs (AddCommGroup (Π₀ i, β i))

@[simp]
/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: (g₁ g₂ : ⨁ i, β i) (i : ι)
  statement: (g₁ - g₂) i = g₁ i - g₂ i
  proof: rfl

中文:
定理 sub_apply
  条件: (g₁ g₂ : ⨁ i, β i) (i : ι)
  结论: (g₁ - g₂) i = g₁ i - g₂ i
  证明: rfl
-/
theorem sub_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
  rfl

end AddCommGroup

variable [forall i, AddCommMonoid (β i)]

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {x y : DirectSum ι β} (w : forall i, x i = y i)
  statement: x = y
  proof: DFunLike.ext _ _ w

@[simp]

中文:
定理 ext
  条件: {x y : DirectSum ι β} (w : 对任意 i, x i = y i)
  结论: x = y
  证明: DFunLike.ext _ _ w

@[simp]
-/
@[ext] theorem ext {x y : DirectSum ι β} (w : forall i, x i = y i) : x = y :=
  DFunLike.ext _ _ w

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (i : ι)
  statement: (0 : ⨁ i, β i) i = 0
  proof: rfl

@[simp]

中文:
定理 zero_apply
  条件: (i : ι)
  结论: (0 : ⨁ i, β i) i = 0
  证明: rfl

@[simp]
-/
theorem zero_apply (i : ι) : (0 : ⨁ i, β i) i = 0 :=
  rfl

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: (g₁ g₂ : ⨁ i, β i) (i : ι)
  statement: (g₁ + g₂) i = g₁ i + g₂ i
  proof: rfl

@[simp]

中文:
定理 add_apply
  条件: (g₁ g₂ : ⨁ i, β i) (i : ι)
  结论: (g₁ + g₂) i = g₁ i + g₂ i
  证明: rfl

@[simp]
-/
theorem add_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ + g₂) i = g₁ i + g₂ i :=
  rfl

@[simp]
/--
theorem `sum_apply` / 定理 `sum_apply`

English:
theorem sum_apply
  given: {α} (s : Finset α) (g : α -> ⨁ i, β i) (i : ι)
  proof: DFinsupp.finsetSum_apply s g i

中文:
定理 sum_apply
  条件: {α} (s : Finset α) (g : α -> ⨁ i, β i) (i : ι)
  证明: DFinsupp.finsetSum_apply s g i

Depends on / 依赖: DFinsupp, DFinsupp.finsetSum_apply, finsetSum_apply
-/
theorem sum_apply {α} (s : Finset α) (g : α -> ⨁ i, β i) (i : ι) :
    (∑ a in s, g a) i = ∑ a in s, g a i :=
  DFinsupp.finsetSum_apply s g i

section DecidableEq

variable [DecidableEq ι]

variable (β)

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (s : Finset ι)
  body: DFinsupp.mk s
  map_add' _ _ := DFinsupp.mk_add
  map_zero' := DFinsupp.mk_zero

中文:
定义 mk
  签名: (s : Finset ι)
  定义体: DFinsupp.mk s
  map_add' _ _ := DFinsupp.mk_add
  map_zero' := DFinsupp.mk_zero

Depends on / 依赖: DFinsupp, DFinsupp.mk
-/
def mk (s : Finset ι) : (forall i : (↑s : Set ι), β i.1) ->+ ⨁ i, β i where
  toFun := DFinsupp.mk s
  map_add' _ _ := DFinsupp.mk_add
  map_zero' := DFinsupp.mk_zero

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (i : ι)
  body: DFinsupp.singleAddHom β i

中文:
定义 of
  签名: (i : ι)
  定义体: DFinsupp.singleAddHom β i

Depends on / 依赖: DFinsupp, DFinsupp.singleAddHom, singleAddHom
-/
def of (i : ι) : β i ->+ ⨁ i, β i :=
  DFinsupp.singleAddHom β i

variable {β}

@[simp]
/--
theorem `of_eq_same` / 定理 `of_eq_same`

English:
theorem of_eq_same
  given: (i : ι) (x : β i)
  statement: (of _ i x) i = x
  proof: DFinsupp.single_eq_same

中文:
定理 of_eq_same
  条件: (i : ι) (x : β i)
  结论: (of _ i x) i = x
  证明: DFinsupp.single_eq_same

Depends on / 依赖: DFinsupp, DFinsupp.single_eq_same, single_eq_same
-/
theorem of_eq_same (i : ι) (x : β i) : (of _ i x) i = x :=
  DFinsupp.single_eq_same

/--
theorem `of_eq_of_ne` / 定理 `of_eq_of_ne`

English:
theorem of_eq_of_ne
  given: (i j : ι) (x : β i) (h : j != i)
  statement: (of _ i x) j = 0
  proof: DFinsupp.single_eq_of_ne h

中文:
定理 of_eq_of_ne
  条件: (i j : ι) (x : β i) (h : j != i)
  结论: (of _ i x) j = 0
  证明: DFinsupp.single_eq_of_ne h

Depends on / 依赖: DFinsupp, DFinsupp.single_eq_of_ne, single_eq_of_ne
-/
theorem of_eq_of_ne (i j : ι) (x : β i) (h : j != i) : (of _ i x) j = 0 :=
  DFinsupp.single_eq_of_ne h

/--
lemma `of_apply` / 引理 `of_apply`

English:
lemma of_apply
  given: {i : ι} (j : ι) (x : β i)
  statement: of β i x j = if h : i = j then Eq.recOn h x else 0
  proof: DFinsupp.single_apply

中文:
引理 of_apply
  条件: {i : ι} (j : ι) (x : β i)
  结论: of β i x j = if h : i = j then Eq.recOn h x else 0
  证明: DFinsupp.single_apply

Depends on / 依赖: DFinsupp, DFinsupp.single_apply, single_apply
-/
lemma of_apply {i : ι} (j : ι) (x : β i) : of β i x j = if h : i = j then Eq.recOn h x else 0 :=
  DFinsupp.single_apply

/--
theorem `mk_apply_of_mem` / 定理 `mk_apply_of_mem`

English:
theorem mk_apply_of_mem
  given: {s : Finset ι} {f : forall i : (↑s : Set ι), β i.val} {n : ι} (hn : n in s)
  proof: DFinsupp.mk_of_mem hn

中文:
定理 mk_apply_of_mem
  条件: {s : Finset ι} {f : 对任意 i : (↑s : Set ι), β i.val} {n : ι} (hn : n in s)
  证明: DFinsupp.mk_of_mem hn

Depends on / 依赖: DFinsupp, DFinsupp.mk_of_mem, mk_of_mem
-/
theorem mk_apply_of_mem {s : Finset ι} {f : forall i : (↑s : Set ι), β i.val} {n : ι} (hn : n in s) :
    mk β s f n = f ⟨n, hn⟩ :=
  DFinsupp.mk_of_mem hn

/--
theorem `mk_apply_of_notMem` / 定理 `mk_apply_of_notMem`

English:
theorem mk_apply_of_notMem
  given: {s : Finset ι} {f : forall i : (↑s : Set ι), β i.val} {n : ι} (hn : n ∉ s)
  proof: DFinsupp.mk_of_notMem hn

@[simp]

中文:
定理 mk_apply_of_notMem
  条件: {s : Finset ι} {f : 对任意 i : (↑s : Set ι), β i.val} {n : ι} (hn : n ∉ s)
  证明: DFinsupp.mk_of_notMem hn

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.mk_of_notMem, mk_of_notMem
-/
theorem mk_apply_of_notMem {s : Finset ι} {f : forall i : (↑s : Set ι), β i.val} {n : ι} (hn : n ∉ s) :
    mk β s f n = 0 :=
  DFinsupp.mk_of_notMem hn

@[simp]
/--
theorem `support_zero` / 定理 `support_zero`

English:
theorem support_zero
  given: [forall (i : ι) (x : β i), Decidable (x != 0)]
  statement: (0 : ⨁ i, β i).support = ∅
  proof: DFinsupp.support_zero

@[simp]

中文:
定理 support_zero
  条件: [对任意 (i : ι) (x : β i), Decidable (x != 0)]
  结论: (0 : ⨁ i, β i).support = ∅
  证明: DFinsupp.support_zero

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.support_zero, support_zero
-/
theorem support_zero [forall (i : ι) (x : β i), Decidable (x != 0)] : (0 : ⨁ i, β i).support = ∅ :=
  DFinsupp.support_zero

@[simp]
/--
theorem `support_of` / 定理 `support_of`

English:
theorem support_of
  given: [forall (i : ι) (x : β i), Decidable (x != 0)] (i : ι) (x : β i) (h : x != 0)
  proof: DFinsupp.support_single h

中文:
定理 support_of
  条件: [对任意 (i : ι) (x : β i), Decidable (x != 0)] (i : ι) (x : β i) (h : x != 0)
  证明: DFinsupp.support_single h

Depends on / 依赖: DFinsupp, DFinsupp.support_single, support_single
-/
theorem support_of [forall (i : ι) (x : β i), Decidable (x != 0)] (i : ι) (x : β i) (h : x != 0) :
    (of _ i x).support = {i} :=
  DFinsupp.support_single h

/--
theorem `support_of_subset` / 定理 `support_of_subset`

English:
theorem support_of_subset
  given: [forall (i : ι) (x : β i), Decidable (x != 0)] {i : ι} {b : β i}
  proof: DFinsupp.support_single_subset

中文:
定理 support_of_subset
  条件: [对任意 (i : ι) (x : β i), Decidable (x != 0)] {i : ι} {b : β i}
  证明: DFinsupp.support_single_subset

Depends on / 依赖: DFinsupp, DFinsupp.support_single_subset, support_single_subset
-/
theorem support_of_subset [forall (i : ι) (x : β i), Decidable (x != 0)] {i : ι} {b : β i} :
    (of _ i b).support subseteq {i} :=
  DFinsupp.support_single_subset

/--
theorem `sum_support_of` / 定理 `sum_support_of`

English:
theorem sum_support_of
  given: [forall (i : ι) (x : β i), Decidable (x != 0)] (x : ⨁ i, β i)
  proof: DFinsupp.sum_single

中文:
定理 sum_support_of
  条件: [对任意 (i : ι) (x : β i), Decidable (x != 0)] (x : ⨁ i, β i)
  证明: DFinsupp.sum_single

Depends on / 依赖: DFinsupp, DFinsupp.sum_single, sum_single
-/
theorem sum_support_of [forall (i : ι) (x : β i), Decidable (x != 0)] (x : ⨁ i, β i) :
    (∑ i in x.support, of β i (x i)) = x :=
  DFinsupp.sum_single

/--
theorem `sum_univ_of` / 定理 `sum_univ_of`

English:
theorem sum_univ_of
  given: [Fintype ι] (x : ⨁ i, β i)
  proof: by
  ext i
  simp [of_apply]

中文:
定理 sum_univ_of
  条件: [Fintype ι] (x : ⨁ i, β i)
  证明: by
  ext i
  simp [of_apply]

Depends on / 依赖: of_apply
-/
theorem sum_univ_of [Fintype ι] (x : ⨁ i, β i) :
    ∑ i in Finset.univ, of β i (x i) = x := by
  ext i
  simp [of_apply]

/--
theorem `mk_injective` / 定理 `mk_injective`

English:
theorem mk_injective
  given: (s : Finset ι)
  statement: Function.Injective (mk β s)
  proof: DFinsupp.mk_injective s

中文:
定理 mk_injective
  条件: (s : Finset ι)
  结论: Function.Injective (mk β s)
  证明: DFinsupp.mk_injective s

Depends on / 依赖: DFinsupp, DFinsupp.mk_injective, mk_injective
-/
theorem mk_injective (s : Finset ι) : Function.Injective (mk β s) :=
  DFinsupp.mk_injective s

/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  given: (i : ι)
  statement: Function.Injective (of β i)
  proof: DFinsupp.single_injective

@[elab_as_elim]

中文:
定理 of_injective
  条件: (i : ι)
  结论: Function.Injective (of β i)
  证明: DFinsupp.single_injective

@[elab_as_elim]

Depends on / 依赖: DFinsupp, DFinsupp.single_injective, single_injective
-/
theorem of_injective (i : ι) : Function.Injective (of β i) :=
  DFinsupp.single_injective

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {motive : (⨁ i, β i) -> Prop} (x : ⨁ i, β i) (zero : motive 0)
  proof: by
  apply DFinsupp.induction x zero
  intro i b f h1 h2 ih
  solve_by_elim

中文:
定理 induction_on
  结论: {motive : (⨁ i, β i) -> 命题} (x : ⨁ i, β i) (zero : motive 0)
  证明: by
  apply DFinsupp.induction x zero
  intro i b f h1 h2 ih
  solve_by_elim
-/
protected theorem induction_on {motive : (⨁ i, β i) -> Prop} (x : ⨁ i, β i) (zero : motive 0)
    (of : forall (i : ι) (x : β i), motive (of β i x))
    (add : forall x y, motive x -> motive y -> motive (x + y)) : motive x := by
  apply DFinsupp.induction x zero
  intro i b f h1 h2 ih
  solve_by_elim

/-- An alternative induction, where the addition assumption is restricted to singles. -/
@[elab_as_elim]
/--
theorem `induction_on'` / 定理 `induction_on'`

English:
theorem induction_on'
  statement: {motive : (⨁ i, β i) -> Prop} (f : ⨁ i, β i) (h0 : motive 0)
  proof: DFinsupp.induction f h0 hadd

中文:
定理 induction_on'
  结论: {motive : (⨁ i, β i) -> 命题} (f : ⨁ i, β i) (h0 : motive 0)
  证明: DFinsupp.induction f h0 hadd
-/
protected theorem induction_on' {motive : (⨁ i, β i) -> Prop} (f : ⨁ i, β i) (h0 : motive 0)
    (hadd : forall (i b) (f : ⨁ i, β i), f i = 0 -> b != 0 -> motive f -> motive (of β i b + f)) :
    motive f :=
  DFinsupp.induction f h0 hadd

/--
theorem `addHom_ext` / 定理 `addHom_ext`

English:
theorem addHom_ext
  given: {γ : Type*} [AddZeroClass γ] ⦃f g
  statement: (⨁ i, β i) ->+ γ⦄
  proof: DFinsupp.addHom_ext H

中文:
定理 addHom_ext
  条件: {γ : 类型} [AddZeroClass γ] ⦃f g
  结论: (⨁ i, β i) ->+ γ⦄
  证明: DFinsupp.addHom_ext H

Depends on / 依赖: DFinsupp, DFinsupp.addHom_ext, addHom_ext
-/
theorem addHom_ext {γ : Type*} [AddZeroClass γ] ⦃f g : (⨁ i, β i) ->+ γ⦄
    (H : forall (i : ι) (y : β i), f (of _ i y) = g (of _ i y)) : f = g :=
  DFinsupp.addHom_ext H

/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext high]
/--
theorem `addHom_ext'` / 定理 `addHom_ext'`

English:
theorem addHom_ext'
  given: {γ : Type*} [AddZeroClass γ] ⦃f g
  statement: (⨁ i, β i) ->+ γ⦄
  proof: addHom_ext fun i => DFunLike.congr_fun H i

中文:
定理 addHom_ext'
  条件: {γ : 类型} [AddZeroClass γ] ⦃f g
  结论: (⨁ i, β i) ->+ γ⦄
  证明: addHom_ext fun i => DFunLike.congr_fun H i

Depends on / 依赖: DFunLike, DFunLike.congr_fun, addHom_ext, congr_fun
-/
theorem addHom_ext' {γ : Type*} [AddZeroClass γ] ⦃f g : (⨁ i, β i) ->+ γ⦄
    (H : forall i : ι, f.comp (of _ i) = g.comp (of _ i)) : f = g :=
addHom_ext fun i => DFunLike.congr_fun H i

variable {γ : Type u₁} [AddCommMonoid γ]

section ToAddMonoid

variable (φ : forall i, β i ->+ γ) (ψ : (⨁ i, β i) ->+ γ)

-- Porting note: The elaborator is struggling with `liftAddHom`. Passing it `β` explicitly helps.
-- This applies to roughly the remainder of the file.

/--
Definition of `toAddMonoid` / `toAddMonoid` 的定义

English:
definition toAddMonoid
  signature: : (⨁ i, β i) ->+ γ
  body: DFinsupp.liftAddHom (β := β) φ

@[simp]

中文:
定义 toAddMonoid
  签名: : (⨁ i, β i) ->+ γ
  定义体: DFinsupp.liftAddHom (β := β) φ

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.liftAddHom, liftAddHom
-/
def toAddMonoid : (⨁ i, β i) ->+ γ :=
  DFinsupp.liftAddHom (β := β) φ

@[simp]
/--
theorem `toAddMonoid_of` / 定理 `toAddMonoid_of`

English:
theorem toAddMonoid_of
  given: (i) (x : β i)
  statement: toAddMonoid φ (of β i x) = φ i x
  proof: DFinsupp.liftAddHom_apply_single φ i x

中文:
定理 toAddMonoid_of
  条件: (i) (x : β i)
  结论: toAddMonoid φ (of β i x) = φ i x
  证明: DFinsupp.liftAddHom_apply_single φ i x

Depends on / 依赖: DFinsupp, DFinsupp.liftAddHom_apply_single, liftAddHom_apply_single
-/
theorem toAddMonoid_of (i) (x : β i) : toAddMonoid φ (of β i x) = φ i x :=
  DFinsupp.liftAddHom_apply_single φ i x

/--
theorem `toAddMonoid.unique` / 定理 `toAddMonoid.unique`

English:
theorem toAddMonoid.unique
  given: (f : ⨁ i, β i)
  statement: ψ f = toAddMonoid (fun i => ψ.comp (of β i)) f
  proof: by
  congr
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` applies addHom_ext' here, which isn't what we want.
  apply DFinsupp.addHom_ext'
  intro
  simp [toAddMonoid]
  rfl

中文:
定理 toAddMonoid.unique
  条件: (f : ⨁ i, β i)
  结论: ψ f = toAddMonoid (fun i => ψ.comp (of β i)) f
  证明: by
  congr
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` applies addHom_ext' here, which isn't what we want.
  apply DFinsupp.addHom_ext'
  intro
  simp [toAddMonoid]
  rfl
-/
theorem toAddMonoid.unique (f : ⨁ i, β i) : ψ f = toAddMonoid (fun i => ψ.comp (of β i)) f := by
  congr
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` applies addHom_ext' here, which isn't what we want.
  apply DFinsupp.addHom_ext'
  intro
  simp [toAddMonoid]
  rfl

/--
lemma `toAddMonoid_injective` / 引理 `toAddMonoid_injective`

English:
lemma toAddMonoid_injective
  statement: Injective (toAddMonoid : (forall i, β i ->+ γ) -> (⨁ i, β i) ->+ γ)
  proof: DFinsupp.liftAddHom.injective

中文:
引理 toAddMonoid_injective
  结论: Injective (toAddMonoid : (对任意 i, β i ->+ γ) -> (⨁ i, β i) ->+ γ)
  证明: DFinsupp.liftAddHom.injective

Depends on / 依赖: DFinsupp, DFinsupp.liftAddHom.injective, injective, liftAddHom
-/
lemma toAddMonoid_injective : Injective (toAddMonoid : (forall i, β i ->+ γ) -> (⨁ i, β i) ->+ γ) :=
  DFinsupp.liftAddHom.injective

/--
lemma `toAddMonoid_inj` / 引理 `toAddMonoid_inj`

English:
lemma toAddMonoid_inj
  given: {f g : forall i, β i ->+ γ}
  statement: toAddMonoid f = toAddMonoid g ↔ f = g
  proof: toAddMonoid_injective.eq_iff

中文:
引理 toAddMonoid_inj
  条件: {f g : 对任意 i, β i ->+ γ}
  结论: toAddMonoid f = toAddMonoid g ↔ f = g
  证明: toAddMonoid_injective.eq_iff
-/
@[simp] lemma toAddMonoid_inj {f g : forall i, β i ->+ γ} : toAddMonoid f = toAddMonoid g ↔ f = g :=
  toAddMonoid_injective.eq_iff

end ToAddMonoid

section FromAddMonoid

/--
Definition of `fromAddMonoid` / `fromAddMonoid` 的定义

English:
definition fromAddMonoid
  signature: : (⨁ i, γ ->+ β i) ->+ γ ->+ ⨁ i, β i
  body: toAddMonoid fun i => AddMonoidHom.compHom (of β i)

@[simp]

中文:
定义 fromAddMonoid
  签名: : (⨁ i, γ ->+ β i) ->+ γ ->+ ⨁ i, β i
  定义体: toAddMonoid fun i => AddMonoidHom.compHom (of β i)

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.compHom, compHom, toAddMonoid
-/
def fromAddMonoid : (⨁ i, γ ->+ β i) ->+ γ ->+ ⨁ i, β i :=
  toAddMonoid fun i => AddMonoidHom.compHom (of β i)

@[simp]
/--
theorem `fromAddMonoid_of` / 定理 `fromAddMonoid_of`

English:
theorem fromAddMonoid_of
  given: (i : ι) (f : γ ->+ β i)
  statement: fromAddMonoid (of _ i f) = (of _ i).comp f
  proof: by
  rw [fromAddMonoid]; rw [toAddMonoid_of]
  rfl

中文:
定理 fromAddMonoid_of
  条件: (i : ι) (f : γ ->+ β i)
  结论: fromAddMonoid (of _ i f) = (of _ i).comp f
  证明: by
  rw [fromAddMonoid]; rw [toAddMonoid_of]
  rfl

Depends on / 依赖: fromAddMonoid, toAddMonoid_of
-/
theorem fromAddMonoid_of (i : ι) (f : γ ->+ β i) : fromAddMonoid (of _ i f) = (of _ i).comp f := by
  rw [fromAddMonoid]; rw [toAddMonoid_of]
  rfl

/--
theorem `fromAddMonoid_of_apply` / 定理 `fromAddMonoid_of_apply`

English:
theorem fromAddMonoid_of_apply
  given: (i : ι) (f : γ ->+ β i) (x : γ)
  proof: by
      rw [fromAddMonoid_of]; rw [AddMonoidHom.coe_comp]; rw [Function.comp]

中文:
定理 fromAddMonoid_of_apply
  条件: (i : ι) (f : γ ->+ β i) (x : γ)
  证明: by
      rw [fromAddMonoid_of]; rw [AddMonoidHom.coe_comp]; rw [Function.comp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_comp, Function, Function.comp, coe_comp, fromAddMonoid_of
-/
theorem fromAddMonoid_of_apply (i : ι) (f : γ ->+ β i) (x : γ) :
    fromAddMonoid (of _ i f) x = of _ i (f x) := by
      rw [fromAddMonoid_of]; rw [AddMonoidHom.coe_comp]; rw [Function.comp]

end FromAddMonoid

variable (β)

-- TODO: generalize this to remove the assumption `S ⊆ T`.
/--
Definition of `setToSet` / `setToSet` 的定义

English:
definition setToSet
  signature: (S T : Set ι) (H : S subseteq T)
  body: toAddMonoid fun i => of (fun i : T => β i) ⟨↑i, H i.2⟩

中文:
定义 setToSet
  签名: (S T : Set ι) (H : S subseteq T)
  定义体: toAddMonoid fun i => of (fun i : T => β i) ⟨↑i, H i.2⟩

Depends on / 依赖: toAddMonoid
-/
def setToSet (S T : Set ι) (H : S subseteq T) : (⨁ i : S, β i) ->+ ⨁ i : T, β i :=
  toAddMonoid fun i => of (fun i : T => β i) ⟨↑i, H i.2⟩

end DecidableEq

/--
Instance `unique` / 实例 `unique`

English:
instance unique
  signature: [forall i, Subsingleton (β i)]
  body: DFinsupp.unique

中文:
实例 unique
  签名: [对任意 i, Subsingleton (β i)]
  定义体: DFinsupp.unique

Depends on / 依赖: DFinsupp, DFinsupp.unique, unique
-/
instance unique [forall i, Subsingleton (β i)] : Unique (⨁ i, β i) :=
  DFinsupp.unique

/--
Instance `uniqueOfIsEmpty` / 实例 `uniqueOfIsEmpty`

English:
instance uniqueOfIsEmpty
  signature: [IsEmpty ι]
  body: DFinsupp.uniqueOfIsEmpty

中文:
实例 uniqueOfIsEmpty
  签名: [IsEmpty ι]
  定义体: DFinsupp.uniqueOfIsEmpty

Depends on / 依赖: DFinsupp, DFinsupp.uniqueOfIsEmpty, uniqueOfIsEmpty
-/
instance uniqueOfIsEmpty [IsEmpty ι] : Unique (⨁ i, β i) :=
  DFinsupp.uniqueOfIsEmpty

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (M : Type v) (ι : Type* := PUnit) [AddCommMonoid M] [Unique ι]
  body: { DirectSum.toAddMonoid fun _ => AddMonoidHom.id M with
    toFun := DirectSum.toAddMonoid fun _ => AddMonoidHom.id M
    invFun := of (fun _ => M) default
    left_inv x :=
      DirectSum.induction_on x
        (by rw [map_zero, map_zero])
        (fun p x => by rw [Unique.default_eq p, toAddMonoi

中文:
定义 id
  签名: (M : 类型v) (ι : 类型 := PUnit) [AddCommMonoid M] [Unique ι]
  定义体: { DirectSum.toAddMonoid fun _ => AddMonoidHom.id M with
    toFun := DirectSum.toAddMonoid fun _ => AddMonoidHom.id M
    invFun := of (fun _ => M) default
    left_inv x :=
      DirectSum.induction_on x
        (by rw [map_zero, map_zero])
        (fun p x => by rw [Unique.default_eq p, toAddMonoi
-/
protected def id (M : Type v) (ι : Type* := PUnit) [AddCommMonoid M] [Unique ι] :
    (⨁ _ : ι, M) ≃+ M :=
  { DirectSum.toAddMonoid fun _ => AddMonoidHom.id M with
    toFun := DirectSum.toAddMonoid fun _ => AddMonoidHom.id M
    invFun := of (fun _ => M) default
    left_inv x :=
      DirectSum.induction_on x
        (by rw [map_zero, map_zero])
        (fun p x => by rw [Unique.default_eq p, toAddMonoid_of, AddMonoidHom.id_apply])
        (fun x y ihx ihy => by grind)
    right_inv _ := toAddMonoid_of _ _ _ }

/--
lemma `id_symm_apply` / 引理 `id_symm_apply`

English:
lemma id_symm_apply
  given: {M : Type v} {ι : Type*} [AddCommMonoid M] [Unique ι] (x : M)
  proof: rfl

中文:
引理 id_symm_apply
  条件: {M : 类型v} {ι : 类型} [AddCommMonoid M] [Unique ι] (x : M)
  证明: rfl
-/
@[simp] lemma id_symm_apply {M : Type v} {ι : Type*} [AddCommMonoid M] [Unique ι] (x : M) :
    (DirectSum.id M ι).symm x = of _ default x :=
  rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: {M : Type v} {ι : Type*} [AddCommMonoid M] [Unique ι] (x : ⨁ _ : ι, M)
  proof: by
  rw [← AddEquiv.eq_symm_apply]; rw [id_symm_apply]; rw [eq_comm]
  induction x using DirectSum.induction_on <;> simp [Unique.eq_default, *]

中文:
引理 id_apply
  条件: {M : 类型v} {ι : 类型} [AddCommMonoid M] [Unique ι] (x : ⨁ _ : ι, M)
  证明: by
  rw [← AddEquiv.eq_symm_apply]; rw [id_symm_apply]; rw [eq_comm]
  induction x using DirectSum.induction_on <;> simp [Unique.eq_default, *]
-/
@[simp] lemma id_apply {M : Type v} {ι : Type*} [AddCommMonoid M] [Unique ι] (x : ⨁ _ : ι, M) :
    DirectSum.id M ι x = x default := by
  rw [← AddEquiv.eq_symm_apply]; rw [id_symm_apply]; rw [eq_comm]
  induction x using DirectSum.induction_on <;> simp [Unique.eq_default, *]

section CongrLeft

variable {κ : Type*}

/--
Definition of `equivCongrLeft` / `equivCongrLeft` 的定义

English:
definition equivCongrLeft
  signature: (h : ι ≃ κ)
  body: { DFinsupp.equivCongrLeft h with map_add' := DFinsupp.comapDomain'_add _ h.right_inv }

@[simp]

中文:
定义 equivCongrLeft
  签名: (h : ι ≃ κ)
  定义体: { DFinsupp.equivCongrLeft h with map_add' := DFinsupp.comapDomain'_add _ h.right_inv }

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.comapDomain, DFinsupp.equivCongrLeft, _add, comapDomain, equivCongrLeft, h.right_inv, map_add, right_inv
-/
def equivCongrLeft (h : ι ≃ κ) : (⨁ i, β i) ≃+ ⨁ k, β (h.symm k) :=
  { DFinsupp.equivCongrLeft h with map_add' := DFinsupp.comapDomain'_add _ h.right_inv }

@[simp]
/--
theorem `equivCongrLeft_apply` / 定理 `equivCongrLeft_apply`

English:
theorem equivCongrLeft_apply
  given: (h : ι ≃ κ) (f : ⨁ i, β i) (k : κ)
  proof: DFinsupp.comapDomain'_apply _ h.right_inv _ _

@[simp]

中文:
定理 equivCongrLeft_apply
  条件: (h : ι ≃ κ) (f : ⨁ i, β i) (k : κ)
  证明: DFinsupp.comapDomain'_apply _ h.right_inv _ _

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.comapDomain, _apply, comapDomain, h.right_inv, right_inv
-/
theorem equivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ i, β i) (k : κ) :
    equivCongrLeft h f k = f (h.symm k) :=
  DFinsupp.comapDomain'_apply _ h.right_inv _ _

@[simp]
/--
theorem `equivCongrLeft_of` / 定理 `equivCongrLeft_of`

English:
theorem equivCongrLeft_of
  given: [DecidableEq ι] [DecidableEq κ] (h : ι ≃ κ) (k : κ) (x : β (h.symm k))
  proof: DFinsupp.comapDomain'_single h.symm h.right_inv _ _

中文:
定理 equivCongrLeft_of
  条件: [DecidableEq ι] [DecidableEq κ] (h : ι ≃ κ) (k : κ) (x : β (h.symm k))
  证明: DFinsupp.comapDomain'_single h.symm h.right_inv _ _

Depends on / 依赖: DFinsupp, DFinsupp.comapDomain, _single, comapDomain, h.right_inv, h.symm, right_inv
-/
theorem equivCongrLeft_of [DecidableEq ι] [DecidableEq κ] (h : ι ≃ κ) (k : κ) (x : β (h.symm k)) :
    equivCongrLeft h (of β (h.symm k) x) = of (fun k => β (h.symm k)) k x :=
  DFinsupp.comapDomain'_single h.symm h.right_inv _ _

end CongrLeft

section Option

variable {α : Option ι -> Type w} [forall i, AddCommMonoid (α i)]

/-- Isomorphism obtained by separating the term of index `none` of a direct sum over `Option ι`. -/
@[simps!]
/--
Definition of `addEquivProdDirectSum` / `addEquivProdDirectSum` 的定义

English:
definition addEquivProdDirectSum
  signature: : (⨁ i, α i) ≃+ α none × ⨁ i, α (some i)
  body: { DFinsupp.equivProdDFinsupp with map_add' := DFinsupp.equivProdDFinsupp_add }

中文:
定义 addEquivProdDirectSum
  签名: : (⨁ i, α i) ≃+ α none × ⨁ i, α (some i)
  定义体: { DFinsupp.equivProdDFinsupp with map_add' := DFinsupp.equivProdDFinsupp_add }

Depends on / 依赖: DFinsupp, DFinsupp.equivProdDFinsupp, DFinsupp.equivProdDFinsupp_add, equivProdDFinsupp, equivProdDFinsupp_add, map_add
-/
noncomputable def addEquivProdDirectSum : (⨁ i, α i) ≃+ α none × ⨁ i, α (some i) :=
  { DFinsupp.equivProdDFinsupp with map_add' := DFinsupp.equivProdDFinsupp_add }

end Option

section Sigma

variable [DecidableEq ι] {α : ι -> Type u} {δ : forall i, α i -> Type w} [forall i j, AddCommMonoid (δ i j)]

/--
Definition of `sigmaCurry` / `sigmaCurry` 的定义

English:
definition sigmaCurry
  signature: : (⨁ i : Σ _i, _, δ i.1 i.2) ->+ ⨁ (i) (j), δ i j where
  body: DFinsupp.sigmaCurry (δ := δ)
  map_zero' := DFinsupp.sigmaCurry_zero
  map_add' f g := DFinsupp.sigmaCurry_add f g

@[simp]

中文:
定义 sigmaCurry
  签名: : (⨁ i : Σ _i, _, δ i.1 i.2) ->+ ⨁ (i) (j), δ i j where
  定义体: DFinsupp.sigmaCurry (δ := δ)
  map_zero' := DFinsupp.sigmaCurry_zero
  map_add' f g := DFinsupp.sigmaCurry_add f g

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.sigmaCurry, sigmaCurry
-/
def sigmaCurry : (⨁ i : Σ _i, _, δ i.1 i.2) ->+ ⨁ (i) (j), δ i j where
  toFun := DFinsupp.sigmaCurry (δ := δ)
  map_zero' := DFinsupp.sigmaCurry_zero
  map_add' f g := DFinsupp.sigmaCurry_add f g

@[simp]
/--
theorem `sigmaCurry_apply` / 定理 `sigmaCurry_apply`

English:
theorem sigmaCurry_apply
  given: (f : ⨁ i : Σ _i, _, δ i.1 i.2) (i : ι) (j : α i)
  proof: DFinsupp.sigmaCurry_apply (δ := δ) _ i j

@[simp]

中文:
定理 sigmaCurry_apply
  条件: (f : ⨁ i : Σ _i, _, δ i.1 i.2) (i : ι) (j : α i)
  证明: DFinsupp.sigmaCurry_apply (δ := δ) _ i j

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.sigmaCurry_apply, DirectLimit, Module, Module.DirectLimit.of.zero_exact, sigmaCurry_apply, zero_exact
-/
theorem sigmaCurry_apply (f : ⨁ i : Σ _i, _, δ i.1 i.2) (i : ι) (j : α i) :
    sigmaCurry f i j = f ⟨i, j⟩ :=
  DFinsupp.sigmaCurry_apply (δ := δ) _ i j

@[simp]
/--
theorem `sigmaCurry_of` / 定理 `sigmaCurry_of`

English:
theorem sigmaCurry_of
  given: [forall i : ι, DecidableEq (α i)] (k : (i : ι) × α i) (x : δ k.1 k.2)
  proof: DFinsupp.sigmaCurry_single k x

中文:
定理 sigmaCurry_of
  条件: [对任意 i : ι, DecidableEq (α i)] (k : (i : ι) × α i) (x : δ k.1 k.2)
  证明: DFinsupp.sigmaCurry_single k x

Depends on / 依赖: DFinsupp, DFinsupp.sigmaCurry_single, sigmaCurry_single
-/
theorem sigmaCurry_of [forall i : ι, DecidableEq (α i)] (k : (i : ι) × α i) (x : δ k.1 k.2) :
    sigmaCurry (of (fun k => δ k.1 k.2) k x) =
      of (fun i' => ⨁ (j' : α i'), δ i' j') k.1 (of (fun j' => δ k.1 j') k.2 x) :=
  DFinsupp.sigmaCurry_single k x

/--
Definition of `sigmaUncurry` / `sigmaUncurry` 的定义

English:
definition sigmaUncurry
  signature: : (⨁ (i) (j), δ i j) ->+ ⨁ i : Σ _i, _, δ i.1 i.2 where
  body: DFinsupp.sigmaUncurry
  map_zero' := DFinsupp.sigmaUncurry_zero
  map_add' := DFinsupp.sigmaUncurry_add

@[simp]

中文:
定义 sigmaUncurry
  签名: : (⨁ (i) (j), δ i j) ->+ ⨁ i : Σ _i, _, δ i.1 i.2 where
  定义体: DFinsupp.sigmaUncurry
  map_zero' := DFinsupp.sigmaUncurry_zero
  map_add' := DFinsupp.sigmaUncurry_add

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.sigmaUncurry, sigmaUncurry
-/
def sigmaUncurry : (⨁ (i) (j), δ i j) ->+ ⨁ i : Σ _i, _, δ i.1 i.2 where
  toFun := DFinsupp.sigmaUncurry
  map_zero' := DFinsupp.sigmaUncurry_zero
  map_add' := DFinsupp.sigmaUncurry_add

@[simp]
/--
theorem `sigmaUncurry_apply` / 定理 `sigmaUncurry_apply`

English:
theorem sigmaUncurry_apply
  given: (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i)
  proof: DFinsupp.sigmaUncurry_apply f i j

中文:
定理 sigmaUncurry_apply
  条件: (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i)
  证明: DFinsupp.sigmaUncurry_apply f i j

Depends on / 依赖: DFinsupp, DFinsupp.sigmaUncurry_apply, sigmaUncurry_apply
-/
theorem sigmaUncurry_apply (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) :
    sigmaUncurry f ⟨i, j⟩ = f i j :=
  DFinsupp.sigmaUncurry_apply f i j

/--
Definition of `sigmaCurryEquiv` / `sigmaCurryEquiv` 的定义

English:
definition sigmaCurryEquiv
  signature: : (⨁ i : Σ _i, _, δ i.1 i.2) ≃+ ⨁ (i) (j), δ i j
  body: { sigmaCurry, DFinsupp.sigmaCurryEquiv with }

中文:
定义 sigmaCurryEquiv
  签名: : (⨁ i : Σ _i, _, δ i.1 i.2) ≃+ ⨁ (i) (j), δ i j
  定义体: { sigmaCurry, DFinsupp.sigmaCurryEquiv with }

Depends on / 依赖: DFinsupp, DFinsupp.sigmaCurryEquiv, sigmaCurry, sigmaCurryEquiv
-/
def sigmaCurryEquiv : (⨁ i : Σ _i, _, δ i.1 i.2) ≃+ ⨁ (i) (j), δ i j :=
  { sigmaCurry, DFinsupp.sigmaCurryEquiv with }

end Sigma

section SigmaFiber

variable {ι₁ ι₂ : Type v} [DecidableEq ι₂] (f : ι₁ -> ι₂)
variable {β : ι₁ -> Type w} [Π i, AddCommMonoid (β i)]

/--
Definition of `sigmaFiberAddEquiv` / `sigmaFiberAddEquiv` 的定义

English:
definition sigmaFiberAddEquiv
  signature: : (⨁ i, β i) ≃+ ⨁ (j : ι₂) (i : { i : ι₁ // f i = j}), β ↑i
  body: (equivCongrLeft (Equiv.sigmaFiberEquiv f).symm).trans
    (sigmaCurryEquiv (δ := fun j => (fun (i : { i : ι₁ // f i = j}) => β i)))

中文:
定义 sigmaFiberAddEquiv
  签名: : (⨁ i, β i) ≃+ ⨁ (j : ι₂) (i : { i : ι₁ // f i = j}), β ↑i
  定义体: (equivCongrLeft (Equiv.sigmaFiberEquiv f).symm).trans
    (sigmaCurryEquiv (δ := fun j => (fun (i : { i : ι₁ // f i = j}) => β i)))

Depends on / 依赖: Equiv.sigmaFiberEquiv, equivCongrLeft, sigmaCurryEquiv, sigmaFiberEquiv
-/
def sigmaFiberAddEquiv : (⨁ i, β i) ≃+ ⨁ (j : ι₂) (i : { i : ι₁ // f i = j}), β ↑i :=
  (equivCongrLeft (Equiv.sigmaFiberEquiv f).symm).trans
    (sigmaCurryEquiv (δ := fun j => (fun (i : { i : ι₁ // f i = j}) => β i)))

/--
theorem `sigmaFiberAddEquiv_apply` / 定理 `sigmaFiberAddEquiv_apply`

English:
theorem sigmaFiberAddEquiv_apply
  given: (x : ⨁ i, β i)
  proof: rfl

@[simp]

中文:
定理 sigmaFiberAddEquiv_apply
  条件: (x : ⨁ i, β i)
  证明: rfl

@[simp]
-/
theorem sigmaFiberAddEquiv_apply (x : ⨁ i, β i) :
    sigmaFiberAddEquiv f x = sigmaCurry (equivCongrLeft (Equiv.sigmaFiberEquiv f).symm x) := rfl

@[simp]
/--
theorem `sigmaFiberAddEquiv_apply_apply` / 定理 `sigmaFiberAddEquiv_apply_apply`

English:
theorem sigmaFiberAddEquiv_apply_apply
  given: (x : ⨁ i, β i) (j : ι₂) (i' : { i : ι₁ // f i = j})
  proof: rfl

@[simp]

中文:
定理 sigmaFiberAddEquiv_apply_apply
  条件: (x : ⨁ i, β i) (j : ι₂) (i' : { i : ι₁ // f i = j})
  证明: rfl

@[simp]
-/
theorem sigmaFiberAddEquiv_apply_apply (x : ⨁ i, β i) (j : ι₂) (i' : { i : ι₁ // f i = j}) :
    sigmaFiberAddEquiv f x j i' = x i' := rfl

@[simp]
/--
theorem `sigmaFiberAddEquiv_of` / 定理 `sigmaFiberAddEquiv_of`

English:
theorem sigmaFiberAddEquiv_of
  given: [DecidableEq ι₁] (i : ι₁) (x : β i)
  proof: let h := Equiv.sigmaFiberEquiv f
  let k : (j : ι₂) × {i₁ : ι₁ // f i₁ = j} := ⟨f i, ⟨i, rfl⟩⟩
  calc sigmaFiberAddEquiv f (of β (h k) x)
    _ = sigmaCurry (of (fun k : (j' : ι₂) × {i // f i = j'} => β k.2) k x) := by
      rw [sigmaFiberAddEquiv_apply]
      exact congrArg sigmaCurry (equivCongrLe

中文:
定理 sigmaFiberAddEquiv_of
  条件: [DecidableEq ι₁] (i : ι₁) (x : β i)
  证明: let h := Equiv.sigmaFiberEquiv f
  let k : (j : ι₂) × {i₁ : ι₁ // f i₁ = j} := ⟨f i, ⟨i, rfl⟩⟩
  calc sigmaFiberAddEquiv f (of β (h k) x)
    _ = sigmaCurry (of (fun k : (j' : ι₂) × {i // f i = j'} => β k.2) k x) := by
      rw [sigmaFiberAddEquiv_apply]
      exact congrArg sigmaCurry (equivCongrLe

Depends on / 依赖: Equiv.sigmaFiberEquiv, equivCongrLeft_of, h.symm, sigmaCurry, sigmaFiberAddEquiv, sigmaFiberAddEquiv_apply, sigmaFiberEquiv
-/
theorem sigmaFiberAddEquiv_of [DecidableEq ι₁] (i : ι₁) (x : β i) :
    sigmaFiberAddEquiv f (of _ i x) = of _ (f i) (of _ ⟨i, rfl⟩ x) :=
  let h := Equiv.sigmaFiberEquiv f
  let k : (j : ι₂) × {i₁ : ι₁ // f i₁ = j} := ⟨f i, ⟨i, rfl⟩⟩
  calc sigmaFiberAddEquiv f (of β (h k) x)
    _ = sigmaCurry (of (fun k : (j' : ι₂) × {i // f i = j'} => β k.2) k x) := by
      rw [sigmaFiberAddEquiv_apply]
      exact congrArg sigmaCurry (equivCongrLeft_of (h := h.symm) _ _)
    _ = of _ k.1 (of _ k.2 x) := by simp

end SigmaFiber

/--
Definition of `coeAddMonoidHom` / `coeAddMonoidHom` 的定义

English:
definition coeAddMonoidHom
  signature: {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
  body: toAddMonoid fun i => AddSubmonoidClass.subtype (A i)

中文:
定义 coeAddMonoidHom
  签名: {M S : 类型} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
  定义体: toAddMonoid fun i => AddSubmonoidClass.subtype (A i)
-/
protected def coeAddMonoidHom {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι -> S) : (⨁ i, A i) ->+ M :=
  toAddMonoid fun i => AddSubmonoidClass.subtype (A i)

/--
theorem `coeAddMonoidHom_eq_dfinsuppSum` / 定理 `coeAddMonoidHom_eq_dfinsuppSum`

English:
theorem coeAddMonoidHom_eq_dfinsuppSum
  statement: [DecidableEq ι]
  proof: by
  simp only [DirectSum.coeAddMonoidHom, toAddMonoid, DFinsupp.liftAddHom, AddEquiv.coe_mk]
  exact DFinsupp.sumAddHom_apply _ x

@[simp]

中文:
定理 coeAddMonoidHom_eq_dfinsuppSum
  结论: [DecidableEq ι]
  证明: by
  simp only [DirectSum.coeAddMonoidHom, toAddMonoid, DFinsupp.liftAddHom, AddEquiv.coe_mk]
  exact DFinsupp.sumAddHom_apply _ x

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.coe_mk, DFinsupp, DFinsupp.liftAddHom, DFinsupp.sumAddHom_apply, DirectSum, DirectSum.coeAddMonoidHom, coeAddMonoidHom, coe_mk, liftAddHom, sumAddHom_apply, toAddMonoid
-/
theorem coeAddMonoidHom_eq_dfinsuppSum [DecidableEq ι]
    {M S : Type*} [DecidableEq M] [AddCommMonoid M]
    [SetLike S M] [AddSubmonoidClass S M] (A : ι -> S) (x : DirectSum ι fun i => A i) :
    DirectSum.coeAddMonoidHom A x = DFinsupp.sum x fun i => (fun x : A i => ↑x) := by
  simp only [DirectSum.coeAddMonoidHom, toAddMonoid, DFinsupp.liftAddHom, AddEquiv.coe_mk]
  exact DFinsupp.sumAddHom_apply _ x

@[simp]
/--
theorem `coeAddMonoidHom_of` / 定理 `coeAddMonoidHom_of`

English:
theorem coeAddMonoidHom_of
  statement: {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
  proof: toAddMonoid_of _ _ _

中文:
定理 coeAddMonoidHom_of
  结论: {M S : 类型} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
  证明: toAddMonoid_of _ _ _

Depends on / 依赖: toAddMonoid_of
-/
theorem coeAddMonoidHom_of {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι -> S) (i : ι) (x : A i) :
    DirectSum.coeAddMonoidHom A (of (fun i => A i) i x) = x :=
  toAddMonoid_of _ _ _

/--
theorem `coe_of_apply` / 定理 `coe_of_apply`

English:
theorem coe_of_apply
  statement: {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
  proof: by
  obtain rfl | h := Decidable.eq_or_ne j i
  · rw [DirectSum.of_eq_same, if_pos rfl]
  · rw [DirectSum.of_eq_of_ne _ _ _ h, if_neg h.symm, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]

中文:
定理 coe_of_apply
  结论: {M S : 类型} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
  证明: by
  obtain rfl | h := Decidable.eq_or_ne j i
  · rw [DirectSum.of_eq_same, if_pos rfl]
  · rw [DirectSum.of_eq_of_ne _ _ _ h, if_neg h.symm, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, DirectSum, DirectSum.of_eq_of_ne, DirectSum.of_eq_same, ZeroMemClass, ZeroMemClass.coe_zero, coe_zero, eq_or_ne, h.symm, if_neg, if_pos, of_eq_of_ne, of_eq_same
-/
theorem coe_of_apply {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] {A : ι -> S} (i j : ι) (x : A i) :
    (of (fun i => {x // x in A i}) i x j : M) = if i = j then x else 0 := by
  obtain rfl | h := Decidable.eq_or_ne j i
  · rw [DirectSum.of_eq_same, if_pos rfl]
  · rw [DirectSum.of_eq_of_ne _ _ _ h, if_neg h.symm, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]

/--
Definition of `IsInternal` / `IsInternal` 的定义

English:
definition IsInternal
  signature: {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
  body: Function.Bijective (DirectSum.coeAddMonoidHom A)

中文:
定义 IsInternal
  签名: {M S : 类型} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
  定义体: Function.Bijective (DirectSum.coeAddMonoidHom A)

Depends on / 依赖: Bijective, DirectSum, DirectSum.coeAddMonoidHom, Function, Function.Bijective, coeAddMonoidHom
-/
def IsInternal {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι -> S) : Prop :=
  Function.Bijective (DirectSum.coeAddMonoidHom A)

/--
theorem `IsInternal.addSubmonoid_iSup_eq_top` / 定理 `IsInternal.addSubmonoid_iSup_eq_top`

English:
theorem IsInternal.addSubmonoid_iSup_eq_top
  statement: {M : Type*} [DecidableEq ι] [AddCommMonoid M]
  proof: by
  rw [AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom]; rw [AddMonoidHom.mrange_eq_top]
  exact Function.Bijective.surjective h

中文:
定理 IsInternal.addSubmonoid_iSup_eq_top
  结论: {M : 类型} [DecidableEq ι] [AddCommMonoid M]
  证明: by
  rw [AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom]; rw [AddMonoidHom.mrange_eq_top]
  exact Function.Bijective.surjective h

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mrange_eq_top, AddSubmonoid, AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom, Bijective, Function, Function.Bijective.surjective, iSup_eq_mrange_dfinsuppSumAddHom, mrange_eq_top, surjective
-/
theorem IsInternal.addSubmonoid_iSup_eq_top {M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (A : ι -> AddSubmonoid M) (h : IsInternal A) : iSup A = ⊤ := by
  rw [AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom]; rw [AddMonoidHom.mrange_eq_top]
  exact Function.Bijective.surjective h

variable {M S : Type*} [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `support_subset` / 定理 `support_subset`

English:
theorem support_subset
  given: [DecidableEq ι] [DecidableEq M] (A : ι -> S) (x : DirectSum ι fun i => A i)
  proof: by
  intro m
  simp only [Function.mem_support, Finset.mem_coe, DFinsupp.mem_support_toFun, not_imp_not,
    ZeroMemClass.coe_eq_zero, imp_self]

中文:
定理 support_subset
  条件: [DecidableEq ι] [DecidableEq M] (A : ι -> S) (x : DirectSum ι fun i => A i)
  证明: by
  intro m
  simp only [Function.mem_support, Finset.mem_coe, DFinsupp.mem_support_toFun, not_imp_not,
    ZeroMemClass.coe_eq_zero, imp_self]

Depends on / 依赖: DFinsupp, DFinsupp.mem_support_toFun, Finset, Finset.mem_coe, Function, Function.mem_support, ZeroMemClass, ZeroMemClass.coe_eq_zero, coe_eq_zero, imp_self, mem_coe, mem_support, mem_support_toFun, not_imp_not
-/
theorem support_subset [DecidableEq ι] [DecidableEq M] (A : ι -> S) (x : DirectSum ι fun i => A i) :
    (Function.support fun i => (x i : M)) subseteq ↑(DFinsupp.support x) := by
  intro m
  simp only [Function.mem_support, Finset.mem_coe, DFinsupp.mem_support_toFun, not_imp_not,
    ZeroMemClass.coe_eq_zero, imp_self]

/--
theorem `hasFiniteSupport` / 定理 `hasFiniteSupport`

English:
theorem hasFiniteSupport
  given: (A : ι -> S) (x : DirectSum ι fun i => A i)
  proof: by
  classical
  exact (DFinsupp.support x).finite_toSet.subset (DirectSum.support_subset _ x)

@[deprecated (since := "2026-03-03")] alias finite_support := hasFiniteSupport

中文:
定理 hasFiniteSupport
  条件: (A : ι -> S) (x : DirectSum ι fun i => A i)
  证明: by
  classical
  exact (DFinsupp.support x).finite_toSet.subset (DirectSum.support_subset _ x)

@[deprecated (since := "2026-03-03")] alias finite_support := hasFiniteSupport

Depends on / 依赖: DFinsupp, DFinsupp.support, DirectSum, DirectSum.support_subset, classical, finite_toSet, finite_toSet.subset, subset, support, support_subset
-/
theorem hasFiniteSupport (A : ι -> S) (x : DirectSum ι fun i => A i) :
    (fun i => (x i : M)).HasFiniteSupport := by
  classical
  exact (DFinsupp.support x).finite_toSet.subset (DirectSum.support_subset _ x)

@[deprecated (since := "2026-03-03")] alias finite_support := hasFiniteSupport

section map

variable {ι : Type*} {α : ι -> Type*} {β : ι -> Type*} [forall i, AddCommMonoid (α i)]
variable [forall i, AddCommMonoid (β i)] (f : forall (i : ι), α i ->+ β i)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : (⨁ i, α i) ->+ ⨁ i, β i
  body: DFinsupp.mapRange.addMonoidHom f

中文:
定义 map
  签名: : (⨁ i, α i) ->+ ⨁ i, β i
  定义体: DFinsupp.mapRange.addMonoidHom f

Depends on / 依赖: DFinsupp, DFinsupp.mapRange.addMonoidHom, addMonoidHom, mapRange
-/
def map : (⨁ i, α i) ->+ ⨁ i, β i := DFinsupp.mapRange.addMonoidHom f

/--
lemma `map_of` / 引理 `map_of`

English:
lemma map_of
  given: [DecidableEq ι] (i : ι) (x : α i)
  statement: map f (of α i x) = of β i (f i x)
  proof: DFinsupp.mapRange_single (hf := fun _ => map_zero _)

中文:
引理 map_of
  条件: [DecidableEq ι] (i : ι) (x : α i)
  结论: map f (of α i x) = of β i (f i x)
  证明: DFinsupp.mapRange_single (hf := fun _ => map_zero _)
-/
@[simp] lemma map_of [DecidableEq ι] (i : ι) (x : α i) : map f (of α i x) = of β i (f i x) :=
  DFinsupp.mapRange_single (hf := fun _ => map_zero _)

/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  given: (i : ι) (x : ⨁ i, α i)
  statement: map f x i = f i (x i)
  proof: DFinsupp.mapRange_apply (hf := fun _ => map_zero _) _ _ _

中文:
引理 map_apply
  条件: (i : ι) (x : ⨁ i, α i)
  结论: map f x i = f i (x i)
  证明: DFinsupp.mapRange_apply (hf := fun _ => map_zero _) _ _ _
-/
@[simp] lemma map_apply (i : ι) (x : ⨁ i, α i) : map f x i = f i (x i) :=
  DFinsupp.mapRange_apply (hf := fun _ => map_zero _) _ _ _

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  proof: DFinsupp.mapRange.addMonoidHom_id

中文:
引理 map_id
  证明: DFinsupp.mapRange.addMonoidHom_id
-/
@[simp] lemma map_id :
    (map (fun i => AddMonoidHom.id (α i))) = AddMonoidHom.id (⨁ i, α i) :=
  DFinsupp.mapRange.addMonoidHom_id

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  statement: {γ : ι -> Type*} [forall i, AddCommMonoid (γ i)]
  proof: DFinsupp.mapRange.addMonoidHom_comp _ _

中文:
引理 map_comp
  结论: {γ : ι -> 类型} [对任意 i, AddCommMonoid (γ i)]
  证明: DFinsupp.mapRange.addMonoidHom_comp _ _
-/
@[simp] lemma map_comp {γ : ι -> Type*} [forall i, AddCommMonoid (γ i)]
    (g : forall (i : ι), β i ->+ γ i) :
    (map (fun i => (g i).comp (f i))) = (map g).comp (map f) :=
  DFinsupp.mapRange.addMonoidHom_comp _ _

/--
lemma `map_injective` / 引理 `map_injective`

English:
lemma map_injective
  statement: Function.Injective (map f) ↔ forall i, Function.Injective (f i)
  proof: by
  exact DFinsupp.mapRange_injective (hf := fun _ => map_zero _)

中文:
引理 map_injective
  结论: Function.Injective (map f) ↔ 对任意 i, Function.Injective (f i)
  证明: by
  exact DFinsupp.mapRange_injective (hf := fun _ => map_zero _)

Depends on / 依赖: DFinsupp, DFinsupp.mapRange_injective, mapRange_injective, map_zero
-/
lemma map_injective : Function.Injective (map f) ↔ forall i, Function.Injective (f i) := by
  exact DFinsupp.mapRange_injective (hf := fun _ => map_zero _)

/--
lemma `map_surjective` / 引理 `map_surjective`

English:
lemma map_surjective
  statement: Function.Surjective (map f) ↔ (forall i, Function.Surjective (f i))
  proof: by
  exact DFinsupp.mapRange_surjective (hf := fun _ => map_zero _)

中文:
引理 map_surjective
  结论: Function.Surjective (map f) ↔ (对任意 i, Function.Surjective (f i))
  证明: by
  exact DFinsupp.mapRange_surjective (hf := fun _ => map_zero _)

Depends on / 依赖: DFinsupp, DFinsupp.mapRange_surjective, mapRange_surjective, map_zero
-/
lemma map_surjective : Function.Surjective (map f) ↔ (forall i, Function.Surjective (f i)) := by
  exact DFinsupp.mapRange_surjective (hf := fun _ => map_zero _)

/--
lemma `map_eq_iff` / 引理 `map_eq_iff`

English:
lemma map_eq_iff
  given: (x y : ⨁ i, α i)
  proof: by
  simp_rw [DirectSum.ext_iff, map_apply]

中文:
引理 map_eq_iff
  条件: (x y : ⨁ i, α i)
  证明: by
  simp_rw [DirectSum.ext_iff, map_apply]

Depends on / 依赖: DirectLimit, DirectLimit.exists_eq_zero, DirectSum, DirectSum.ext_iff, Nonempty, Nonempty.intro, apply_fun, exists_eq_zero, ext_iff, map_apply, map_zero, ringEquiv, ringEquiv_of, simp_rw
-/
lemma map_eq_iff (x y : ⨁ i, α i) :
    map f x = map f y ↔ forall i, f i (x i) = f i (y i) := by
  simp_rw [DirectSum.ext_iff, map_apply]

end map

end DirectSum

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `DirectSum.addEquivProd` / `DirectSum.addEquivProd` 的定义

English:
definition DirectSum.addEquivProd
  signature: {ι : Type*} [Fintype ι] (G : ι -> Type*) [(i : ι) -> AddCommMonoid (G i)]
  body: ⟨DFinsupp.equivFunOnFintype, fun g h => funext fun _ => by
    simp only [DFinsupp.equivFunOnFintype, Equiv.toFun_as_coe, Equiv.coe_fn_mk,
      ← DFinsupp.add_apply, Pi.add_apply]⟩

中文:
定义 DirectSum.addEquivProd
  签名: {ι : 类型} [Fintype ι] (G : ι -> 类型) [(i : ι) -> AddCommMonoid (G i)]
  定义体: ⟨DFinsupp.equivFunOnFintype, fun g h => funext fun _ => by
    simp only [DFinsupp.equivFunOnFintype, Equiv.toFun_as_coe, Equiv.coe_fn_mk,
      ← DFinsupp.add_apply, Pi.add_apply]⟩

Depends on / 依赖: DFinsupp, DFinsupp.add_apply, DFinsupp.equivFunOnFintype, Equiv.coe_fn_mk, Equiv.toFun_as_coe, Pi.add_apply, add_apply, coe_fn_mk, equivFunOnFintype, toFun_as_coe
-/
def DirectSum.addEquivProd {ι : Type*} [Fintype ι] (G : ι -> Type*) [(i : ι) -> AddCommMonoid (G i)] :
    DirectSum ι G ≃+ ((i : ι) -> G i) :=
  ⟨DFinsupp.equivFunOnFintype, fun g h => funext fun _ => by
    simp only [DFinsupp.equivFunOnFintype, Equiv.toFun_as_coe, Equiv.coe_fn_mk,
      ← DFinsupp.add_apply, Pi.add_apply]⟩
