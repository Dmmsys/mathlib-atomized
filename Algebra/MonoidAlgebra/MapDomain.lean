/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Maps of monoid algebras

This file defines maps of monoid algebras along both the ring and monoid arguments.
-/

assert_not_exists NonUnitalAlgHom AlgEquiv

@[expose] public noncomputable section

open Function
open Finsupp hiding single mapDomain

variable {ι F R S T M N O : Type*}

namespace MonoidAlgebra
section Semiring
variable [Semiring R] [Semiring S] [Semiring T] {f : M -> N} {a : M} {r : R}

/-- Given a function `f : M → N` between magmas, return the corresponding map `R[M] → R[N]` obtained
by summing the coefficients along each fiber of `f`. -/
@[to_additive (attr := simps)
/-- Given a function `f : M → N` between magmas, return the corresponding map `R[M] → R[N]` obtained
by summing the coefficients along each fiber of `f`. -/]
/--
Definition of `mapDomain` / `mapDomain` 的定义

English:
definition mapDomain
  signature: (f : M -> N) (x : R[M])
  body: .ofCoeff Finsupp.mapDomain f x.coeff

@[to_additive (attr := simp)]

中文:
定义 mapDomain
  签名: (f : M -> N) (x : R[M])
  定义体: .ofCoeff Finsupp.mapDomain f x.coeff

@[to_additive (attr := simp)]

Depends on / 依赖: Finsupp, Finsupp.mapDomain, mapDomain, ofCoeff, x.coeff
-/
def mapDomain (f : M -> N) (x : R[M]) : R[N] := .ofCoeff Finsupp.mapDomain f x.coeff

@[to_additive (attr := simp)]
/--
lemma `mapDomain_zero` / 引理 `mapDomain_zero`

English:
lemma mapDomain_zero
  given: (f : M -> N)
  statement: mapDomain f (0 : R[M]) = 0
  proof: by ext; simp

@[to_additive]

中文:
引理 mapDomain_zero
  条件: (f : M -> N)
  结论: mapDomain f (0 : R[M]) = 0
  证明: by ext; simp

@[to_additive]
-/
lemma mapDomain_zero (f : M -> N) : mapDomain f (0 : R[M]) = 0 := by ext; simp

@[to_additive]
/--
lemma `mapDomain_add` / 引理 `mapDomain_add`

English:
lemma mapDomain_add
  given: (f : M -> N) (x y : R[M])
  proof: by
  ext; simp [Finsupp.mapDomain_add]

@[to_additive]

中文:
引理 mapDomain_add
  条件: (f : M -> N) (x y : R[M])
  证明: by
  ext; simp [Finsupp.mapDomain_add]

@[to_additive]

Depends on / 依赖: Finsupp, Finsupp.mapDomain_add, mapDomain_add
-/
lemma mapDomain_add (f : M -> N) (x y : R[M]) :
    mapDomain f (x + y) = mapDomain f x + mapDomain f y := by
  ext; simp [Finsupp.mapDomain_add]

@[to_additive]
/--
lemma `mapDomain_sum` / 引理 `mapDomain_sum`

English:
lemma mapDomain_sum
  given: (f : M -> N) (x : S[M]) (v : M -> S -> R[M])
  proof: by
  ext; simp [Finsupp.mapDomain_sum]

@[to_additive (attr := simp)]

中文:
引理 mapDomain_sum
  条件: (f : M -> N) (x : S[M]) (v : M -> S -> R[M])
  证明: by
  ext; simp [Finsupp.mapDomain_sum]

@[to_additive (attr := simp)]

Depends on / 依赖: Finsupp, Finsupp.mapDomain_sum, mapDomain_sum
-/
lemma mapDomain_sum (f : M -> N) (x : S[M]) (v : M -> S -> R[M]) :
    mapDomain f (x.coeff.sum v) = x.coeff.sum fun a b => mapDomain f (v a b) := by
  ext; simp [Finsupp.mapDomain_sum]

@[to_additive (attr := simp)]
/--
lemma `mapDomain_single` / 引理 `mapDomain_single`

English:
lemma mapDomain_single
  statement: mapDomain f (single a r) = single (f a) r
  proof: by ext; simp

@[to_additive]

中文:
引理 mapDomain_single
  结论: mapDomain f (single a r) = single (f a) r
  证明: by ext; simp

@[to_additive]
-/
lemma mapDomain_single : mapDomain f (single a r) = single (f a) r := by ext; simp

@[to_additive]
/--
lemma `mapDomain_injective` / 引理 `mapDomain_injective`

English:
lemma mapDomain_injective
  given: (hf : Injective f)
  statement: Injective (mapDomain (R := R) f)
  proof: ofCoeff_injective.comp (Finsupp.mapDomain_injective hf).comp coeff_injective

中文:
引理 mapDomain_injective
  条件: (hf : Injective f)
  结论: Injective (mapDomain (R := R) f)
  证明: ofCoeff_injective.comp (Finsupp.mapDomain_injective hf).comp coeff_injective
-/
lemma mapDomain_injective (hf : Injective f) : Injective (mapDomain (R := R) f) :=
ofCoeff_injective.comp (Finsupp.mapDomain_injective hf).comp coeff_injective

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := R) (attr := simp) mapDomain_one]
/--
theorem `mapDomain_one` / 定理 `mapDomain_one`

English:
theorem mapDomain_one
  given: [One M] [One N] {F : Type*} [FunLike F M N] [OneHomClass F M N] (f : F)
  proof: by
  simp [one_def]

中文:
定理 mapDomain_one
  条件: [One M] [One N] {F : 类型} [FunLike F M N] [OneHomClass F M N] (f : F)
  证明: by
  simp [one_def]

Depends on / 依赖: one_def
-/
theorem mapDomain_one [One M] [One N] {F : Type*} [FunLike F M N] [OneHomClass F M N] (f : F) :
    mapDomain f (1 : R[M]) = (1 : R[N]) := by
  simp [one_def]

/-- Given a map `f : R →+ S`, return the corresponding map `R[M] → S[M]` obtained by mapping
each coefficient along `f`. -/
@[to_additive
/-- Given a map `f : R →+ S`, return the corresponding map `R[M] → S[M]` obtained by mapping
each coefficient along `f`. -/]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : R ->+ S) (x : R[M])
  body: .ofCoeff x.coeff.mapRange f f.map_zero

@[to_additive (attr := simp)]

中文:
定义 map
  签名: (f : R ->+ S) (x : R[M])
  定义体: .ofCoeff x.coeff.mapRange f f.map_zero

@[to_additive (attr := simp)]

Depends on / 依赖: f.map_zero, mapRange, map_zero, ofCoeff, x.coeff.mapRange
-/
def map (f : R ->+ S) (x : R[M]) : S[M] := .ofCoeff x.coeff.mapRange f f.map_zero

@[to_additive (attr := simp)]
/--
lemma `coeff_map` / 引理 `coeff_map`

English:
lemma coeff_map
  given: (f : R ->+ S) (x : R[M])
  proof: rfl

中文:
引理 coeff_map
  条件: (f : R ->+ S) (x : R[M])
  证明: rfl
-/
lemma coeff_map (f : R ->+ S) (x : R[M]) :
    (map f x).coeff = x.coeff.mapRange f f.map_zero := rfl

/-- This isn't marked as simp to avoid looping with unfolding `coeff`. -/
@[to_additive /-- This isn't marked as simp to avoid looping with unfolding `coeff`. -/]
/--
lemma `ofCoeff_mapRange` / 引理 `ofCoeff_mapRange`

English:
lemma ofCoeff_mapRange
  given: (f : R ->+ S) (x : M ->₀ R)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 ofCoeff_mapRange
  条件: (f : R ->+ S) (x : M ->₀ R)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma ofCoeff_mapRange (f : R ->+ S) (x : M ->₀ R) :
    ofCoeff (.mapRange f f.map_zero x) = map f (ofCoeff x) := rfl

@[to_additive (attr := simp)]
/--
lemma `map_zero` / 引理 `map_zero`

English:
lemma map_zero
  given: (f : R ->+ S)
  statement: map f (0 : R[M]) = 0
  proof: by ext; simp

@[to_additive]

中文:
引理 map_zero
  条件: (f : R ->+ S)
  结论: map f (0 : R[M]) = 0
  证明: by ext; simp

@[to_additive]
-/
protected lemma map_zero (f : R ->+ S) : map f (0 : R[M]) = 0 := by ext; simp

@[to_additive]
/--
lemma `map_add` / 引理 `map_add`

English:
lemma map_add
  given: (f : R ->+ S) (x y : R[M])
  statement: map f (x + y) = map f x + map f y
  proof: by
  ext; simp

@[to_additive]

中文:
引理 map_add
  条件: (f : R ->+ S) (x y : R[M])
  结论: map f (x + y) = map f x + map f y
  证明: by
  ext; simp

@[to_additive]
-/
protected lemma map_add (f : R ->+ S) (x y : R[M]) : map f (x + y) = map f x + map f y := by
  ext; simp

@[to_additive]
/--
lemma `map_sum` / 引理 `map_sum`

English:
lemma map_sum
  given: (f : R ->+ S) (s : Finset ι) (x : ι -> R[M])
  proof: by ext; simp

@[to_additive (attr := simp)]

中文:
引理 map_sum
  条件: (f : R ->+ S) (s : Finset ι) (x : ι -> R[M])
  证明: by ext; simp

@[to_additive (attr := simp)]
-/
protected lemma map_sum (f : R ->+ S) (s : Finset ι) (x : ι -> R[M]) :
    map f (∑ i in s, x i) = ∑ i in s, map f (x i) := by ext; simp

@[to_additive (attr := simp)]
/--
lemma `map_single` / 引理 `map_single`

English:
lemma map_single
  given: (f : R ->+ S) (r : R) (m : M)
  statement: map f (single m r) = single m (f r)
  proof: by ext; simp

中文:
引理 map_single
  条件: (f : R ->+ S) (r : R) (m : M)
  结论: map f (single m r) = single m (f r)
  证明: by ext; simp
-/
lemma map_single (f : R ->+ S) (r : R) (m : M) : map f (single m r) = single m (f r) := by ext; simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (x : R[M])
  statement: map (.id R) x = x
  proof: by ext; simp

中文:
引理 map_id
  条件: (x : R[M])
  结论: map (.id R) x = x
  证明: by ext; simp
-/
lemma map_id (x : R[M]) : map (.id R) x = x := by ext; simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
lemma `map_map` / 引理 `map_map`

English:
lemma map_map
  given: (f : S ->+ T) (g : R ->+ S) (x : R[M])
  statement: map f (map g x) = map (f.comp g) x
  proof: by
  ext; simp

@[to_additive]

中文:
引理 map_map
  条件: (f : S ->+ T) (g : R ->+ S) (x : R[M])
  结论: map f (map g x) = map (f.comp g) x
  证明: by
  ext; simp

@[to_additive]
-/
lemma map_map (f : S ->+ T) (g : R ->+ S) (x : R[M]) : map f (map g x) = map (f.comp g) x := by
  ext; simp

@[to_additive]
/--
lemma `range_map` / 引理 `range_map`

English:
lemma range_map
  given: (f : R ->+ S)
  statement: Set.range (map (M := M) f) = {x | forall i, x.coeff i in Set.range f}
  proof: calc
    _ = coeffEquiv ⁻¹' (Set.range (mapRange f (map_zero f) ∘ coeffEquiv)) := by
      simp_rw [comp_def, Equiv.eq_preimage_iff_image_eq, ← Set.range_comp', coeffEquiv_apply,
        coeff_map]
    _ = _ := by simp [Finsupp.range_mapRange]

中文:
引理 range_map
  条件: (f : R ->+ S)
  结论: Set.range (map (M := M) f) = {x | 对任意 i, x.coeff i in Set.range f}
  证明: calc
    _ = coeffEquiv ⁻¹' (Set.range (mapRange f (map_zero f) ∘ coeffEquiv)) := by
      simp_rw [comp_def, Equiv.eq_preimage_iff_image_eq, ← Set.range_comp', coeffEquiv_apply,
        coeff_map]
    _ = _ := by simp [Finsupp.range_mapRange]

Depends on / 依赖: Set.range, x.coeff
-/
lemma range_map (f : R ->+ S) : Set.range (map (M := M) f) = {x | forall i, x.coeff i in Set.range f} :=
  calc
    _ = coeffEquiv ⁻¹' (Set.range (mapRange f (map_zero f) ∘ coeffEquiv)) := by
      simp_rw [comp_def, Equiv.eq_preimage_iff_image_eq, ← Set.range_comp', coeffEquiv_apply,
        coeff_map]
    _ = _ := by simp [Finsupp.range_mapRange]

/-- `MonoidAlgebra.map` of an injective function is injective. -/
@[to_additive /-- `AddMonoidAlgebra.map` of an injective function is injective. -/]
/--
lemma `map_injective` / 引理 `map_injective`

English:
lemma map_injective
  given: (f : R ->+ S) (he : Injective f)
  statement: Injective (map (M := M) f)
  proof: by
  have : map (M := M) f = coeffEquiv.symm ∘ Finsupp.mapRange f (map_zero f) ∘ coeffEquiv := by
    ext; simp [ofCoeff_mapRange]
  simpa [this] using mapRange_injective _ (map_zero f) he

中文:
引理 map_injective
  条件: (f : R ->+ S) (he : Injective f)
  结论: Injective (map (M := M) f)
  证明: by
  have : map (M := M) f = coeffEquiv.symm ∘ Finsupp.mapRange f (map_zero f) ∘ coeffEquiv := by
    ext; simp [ofCoeff_mapRange]
  simpa [this] using mapRange_injective _ (map_zero f) he

Depends on / 依赖: Finsupp, Finsupp.mapRange, coeffEquiv, coeffEquiv.symm, mapRange, mapRange_injective, map_zero, ofCoeff_mapRange
-/
lemma map_injective (f : R ->+ S) (he : Injective f) : Injective (map (M := M) f) := by
  have : map (M := M) f = coeffEquiv.symm ∘ Finsupp.mapRange f (map_zero f) ∘ coeffEquiv := by
    ext; simp [ofCoeff_mapRange]
  simpa [this] using mapRange_injective _ (map_zero f) he

/-- `MonoidAlgebra.map` of a surjective function is surjective. -/
@[to_additive /-- `AddMonoidAlgebra.map` of an surjective function is surjective. -/]
/--
lemma `map_surjective` / 引理 `map_surjective`

English:
lemma map_surjective
  given: (f : R ->+ S) (he : Surjective f)
  statement: Surjective (map (M := M) f)
  proof: by
  have : map (M := M) f = coeffEquiv.symm ∘ Finsupp.mapRange f (map_zero f) ∘ coeffEquiv := by
    ext; simp [ofCoeff_mapRange]
  simpa [this] using mapRange_surjective _ (map_zero f) he

中文:
引理 map_surjective
  条件: (f : R ->+ S) (he : Surjective f)
  结论: Surjective (map (M := M) f)
  证明: by
  have : map (M := M) f = coeffEquiv.symm ∘ Finsupp.mapRange f (map_zero f) ∘ coeffEquiv := by
    ext; simp [ofCoeff_mapRange]
  simpa [this] using mapRange_surjective _ (map_zero f) he

Depends on / 依赖: Finsupp, Finsupp.mapRange, coeffEquiv, coeffEquiv.symm, mapRange, mapRange_surjective, map_zero, ofCoeff_mapRange
-/
lemma map_surjective (f : R ->+ S) (he : Surjective f) : Surjective (map (M := M) f) := by
  have : map (M := M) f = coeffEquiv.symm ∘ Finsupp.mapRange f (map_zero f) ∘ coeffEquiv := by
    ext; simp [ofCoeff_mapRange]
  simpa [this] using mapRange_surjective _ (map_zero f) he

/-- Pullback the coefficients of an element of `R[N]` under an injective `f : M → N`.

Coefficients not in the range of `f` are dropped. -/
@[to_additive
/-- Pullback the coefficients of an element of `R[N]` under an injective `f : M → N`.

Coefficients not in the range of `f` are dropped. -/]
/--
Definition of `comapDomain` / `comapDomain` 的定义

English:
definition comapDomain
  signature: (f : M -> N) (hf : Injective f) (x : R[N])
  body: .ofCoeff x.coeff.comapDomain f hf.injOn

@[to_additive (attr := simp)]

中文:
定义 comapDomain
  签名: (f : M -> N) (hf : Injective f) (x : R[N])
  定义体: .ofCoeff x.coeff.comapDomain f hf.injOn

@[to_additive (attr := simp)]

Depends on / 依赖: comapDomain, hf.injOn, ofCoeff, x.coeff.comapDomain
-/
def comapDomain (f : M -> N) (hf : Injective f) (x : R[N]) : R[M] :=
.ofCoeff x.coeff.comapDomain f hf.injOn

@[to_additive (attr := simp)]
/--
lemma `coeff_comapDomain` / 引理 `coeff_comapDomain`

English:
lemma coeff_comapDomain
  given: (f : M -> N) (hf) (x : R[N])
  proof: by simp [comapDomain]

@[to_additive (attr := simp)]

中文:
引理 coeff_comapDomain
  条件: (f : M -> N) (hf) (x : R[N])
  证明: by simp [comapDomain]

@[to_additive (attr := simp)]

Depends on / 依赖: comapDomain
-/
lemma coeff_comapDomain (f : M -> N) (hf) (x : R[N]) :
    (comapDomain f hf x).coeff = x.coeff.comapDomain f hf.injOn := by simp [comapDomain]

@[to_additive (attr := simp)]
/--
lemma `comapDomain_zero` / 引理 `comapDomain_zero`

English:
lemma comapDomain_zero
  given: (f : M -> N) (hf)
  statement: comapDomain f hf (0 : R[N]) = 0
  proof: by ext; simp

@[to_additive (attr := simp)]

中文:
引理 comapDomain_zero
  条件: (f : M -> N) (hf)
  结论: comapDomain f hf (0 : R[N]) = 0
  证明: by ext; simp

@[to_additive (attr := simp)]
-/
lemma comapDomain_zero (f : M -> N) (hf) : comapDomain f hf (0 : R[N]) = 0 := by ext; simp

@[to_additive (attr := simp)]
/--
lemma `comapDomain_add` / 引理 `comapDomain_add`

English:
lemma comapDomain_add
  given: (f : M -> N) (hf) (x y : R[N])
  proof: by
  ext; simp [comapDomain_add_of_injective hf]

@[simp]

中文:
引理 comapDomain_add
  条件: (f : M -> N) (hf) (x y : R[N])
  证明: by
  ext; simp [comapDomain_add_of_injective hf]

@[simp]

Depends on / 依赖: comapDomain_add_of_injective
-/
lemma comapDomain_add (f : M -> N) (hf) (x y : R[N]) :
    comapDomain f hf (x + y) = comapDomain f hf x + comapDomain f hf y := by
  ext; simp [comapDomain_add_of_injective hf]

@[simp]
/--
lemma `comapDomain_single_of_not_mem_range` / 引理 `comapDomain_single_of_not_mem_range`

English:
lemma comapDomain_single_of_not_mem_range
  given: {r : R} {n : N} (hn : n ∉ Set.range f) (hf)
  proof: by ext; simp [*]

中文:
引理 comapDomain_single_of_not_mem_range
  条件: {r : R} {n : N} (hn : n ∉ Set.range f) (hf)
  证明: by ext; simp [*]
-/
lemma comapDomain_single_of_not_mem_range {r : R} {n : N} (hn : n ∉ Set.range f) (hf) :
    comapDomain f hf (single n r) = 0 := by ext; simp [*]

/-- `comapDomain` as an `AddMonoidHom`. -/
@[to_additive (attr := simps) comapDomainAddMonoidHom /-- `comapDomain` as an `AddMonoidHom`. -/]
/--
Definition of `comapDomainAddMonoidHom` / `comapDomainAddMonoidHom` 的定义

English:
definition comapDomainAddMonoidHom
  signature: (f : M -> N) (hf : Injective f)
  body: comapDomain f hf
  map_zero' := by simp
  map_add' := by simp

中文:
定义 comapDomainAddMonoidHom
  签名: (f : M -> N) (hf : Injective f)
  定义体: comapDomain f hf
  map_zero' := by simp
  map_add' := by simp

Depends on / 依赖: comapDomain
-/
def comapDomainAddMonoidHom (f : M -> N) (hf : Injective f) : R[N] ->+ R[M] where
  toFun := comapDomain f hf
  map_zero' := by simp
  map_add' := by simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
lemma `comapDomain_single_map` / 引理 `comapDomain_single_map`

English:
lemma comapDomain_single_map
  given: (f : M -> N) (hf) (m : M) (r : R)
  proof: by ext; simp

@[to_additive]

中文:
引理 comapDomain_single_map
  条件: (f : M -> N) (hf) (m : M) (r : R)
  证明: by ext; simp

@[to_additive]
-/
lemma comapDomain_single_map (f : M -> N) (hf) (m : M) (r : R) :
    comapDomain f hf (single (f m) r) = single m r := by ext; simp

@[to_additive]
/--
lemma `mapDomain_comapDomain` / 引理 `mapDomain_comapDomain`

English:
lemma mapDomain_comapDomain
  given: {f : M -> N} {x : R[N]} (hx : ↑x.coeff.support subseteq Set.range f) (hf)
  proof: by
  ext : 1; exact Finsupp.mapDomain_comapDomain _ hf _ hx

中文:
引理 mapDomain_comapDomain
  条件: {f : M -> N} {x : R[N]} (hx : ↑x.coeff.support subseteq Set.range f) (hf)
  证明: by
  ext : 1; exact Finsupp.mapDomain_comapDomain _ hf _ hx

Depends on / 依赖: Finsupp, Finsupp.mapDomain_comapDomain, mapDomain_comapDomain
-/
lemma mapDomain_comapDomain {f : M -> N} {x : R[N]} (hx : ↑x.coeff.support subseteq Set.range f) (hf) :
    mapDomain f (comapDomain f hf x) = x := by
  ext : 1; exact Finsupp.mapDomain_comapDomain _ hf _ hx

section Mul
variable [Mul M] [Mul N] [Mul O] [FunLike F M N] [MulHomClass F M N]

@[to_additive (dont_translate := R) mapDomain_mul]
/--
lemma `mapDomain_mul` / 引理 `mapDomain_mul`

English:
lemma mapDomain_mul
  given: (f : F) (x y : R[M])
  statement: mapDomain f (x * y) = mapDomain f x * mapDomain f y
  proof: by
  simp [mul_def, mapDomain_sum, add_mul, mul_add, sum_mapDomain_index]

中文:
引理 mapDomain_mul
  条件: (f : F) (x y : R[M])
  结论: mapDomain f (x * y) = mapDomain f x * mapDomain f y
  证明: by
  simp [mul_def, mapDomain_sum, add_mul, mul_add, sum_mapDomain_index]

Depends on / 依赖: add_mul, mapDomain_sum, mul_add, mul_def, sum_mapDomain_index
-/
lemma mapDomain_mul (f : F) (x y : R[M]) : mapDomain f (x * y) = mapDomain f x * mapDomain f y := by
  simp [mul_def, mapDomain_sum, add_mul, mul_add, sum_mapDomain_index]

variable (R) in
/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`MonoidAlgebra.mapDomain f` is a ring homomorphism between their monoid algebras. -/
@[to_additive (attr := simps) /--
If `f : G → H` is a multiplicative homomorphism between two additive monoids, then
`AddMonoidAlgebra.mapDomain f` is a ring homomorphism between their additive monoid algebras. -/]
/--
Definition of `mapDomainNonUnitalRingHom` / `mapDomainNonUnitalRingHom` 的定义

English:
definition mapDomainNonUnitalRingHom
  signature: (f : M ->ₙ* N)
  body: mapDomain f
  map_zero' := mapDomain_zero _
  map_add' := mapDomain_add _
  map_mul' := mapDomain_mul f

中文:
定义 mapDomainNonUnitalRingHom
  签名: (f : M ->ₙ* N)
  定义体: mapDomain f
  map_zero' := mapDomain_zero _
  map_add' := mapDomain_add _
  map_mul' := mapDomain_mul f

Depends on / 依赖: mapDomain
-/
def mapDomainNonUnitalRingHom (f : M ->ₙ* N) : R[M] ->ₙ+* R[N] where
  toFun := mapDomain f
  map_zero' := mapDomain_zero _
  map_add' := mapDomain_add _
  map_mul' := mapDomain_mul f

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := R) (attr := simp)]
/--
lemma `mapDomainNonUnitalRingHom_id` / 引理 `mapDomainNonUnitalRingHom_id`

English:
lemma mapDomainNonUnitalRingHom_id
  statement: mapDomainNonUnitalRingHom R (.id M) = .id R[M]
  proof: by ext; simp

中文:
引理 mapDomainNonUnitalRingHom_id
  结论: mapDomainNonUnitalRingHom R (.id M) = .id R[M]
  证明: by ext; simp
-/
lemma mapDomainNonUnitalRingHom_id : mapDomainNonUnitalRingHom R (.id M) = .id R[M] := by ext; simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := R) (attr := simp)]
/--
lemma `mapDomainNonUnitalRingHom_comp` / 引理 `mapDomainNonUnitalRingHom_comp`

English:
lemma mapDomainNonUnitalRingHom_comp
  given: (f : N ->ₙ* O) (g : M ->ₙ* N)
  proof: by
  ext; simp [Finsupp.mapDomain_comp]

中文:
引理 mapDomainNonUnitalRingHom_comp
  条件: (f : N ->ₙ* O) (g : M ->ₙ* N)
  证明: by
  ext; simp [Finsupp.mapDomain_comp]

Depends on / 依赖: Finsupp, Finsupp.mapDomain_comp, mapDomain_comp
-/
lemma mapDomainNonUnitalRingHom_comp (f : N ->ₙ* O) (g : M ->ₙ* N) :
    mapDomainNonUnitalRingHom R (f.comp g) =
      (mapDomainNonUnitalRingHom R f).comp (mapDomainNonUnitalRingHom R g) := by
  ext; simp [Finsupp.mapDomain_comp]

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- Equivalent monoids have additively isomorphic monoid algebras.

`MonoidAlgebra.mapDomain` as an `AddEquiv`. -/
@[to_additive (dont_translate := R)
/-- Equivalent additive monoids have additively isomorphic additive monoid algebras.

`AddMonoidAlgebra.mapDomain` as an `AddEquiv`. -/]
/--
Definition of `mapDomainAddEquiv` / `mapDomainAddEquiv` 的定义

English:
definition mapDomainAddEquiv
  signature: (e : M ≃ N)
  body: x.mapDomain e
  invFun x := x.mapDomain e.symm
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; simp

中文:
定义 mapDomainAddEquiv
  签名: (e : M ≃ N)
  定义体: x.mapDomain e
  invFun x := x.mapDomain e.symm
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; simp

Depends on / 依赖: mapDomain, x.mapDomain
-/
def mapDomainAddEquiv (e : M ≃ N) : R[M] ≃+ R[N] where
  toFun x := x.mapDomain e
  invFun x := x.mapDomain e.symm
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
lemma `coeff_mapDomainAddEquiv` / 引理 `coeff_mapDomainAddEquiv`

English:
lemma coeff_mapDomainAddEquiv
  given: (e : M ≃ N) (x : R[M])
  proof: by ext; simp [mapDomainAddEquiv]

@[deprecated (since := "2026-06-18")] alias mapDomainAddEquiv_apply := coeff_mapDomainAddEquiv

中文:
引理 coeff_mapDomainAddEquiv
  条件: (e : M ≃ N) (x : R[M])
  证明: by ext; simp [mapDomainAddEquiv]

@[deprecated (since := "2026-06-18")] alias mapDomainAddEquiv_apply := coeff_mapDomainAddEquiv

Depends on / 依赖: mapDomainAddEquiv
-/
lemma coeff_mapDomainAddEquiv (e : M ≃ N) (x : R[M]) :
    (mapDomainAddEquiv R e x).coeff = equivMapDomain e x.coeff := by ext; simp [mapDomainAddEquiv]

@[deprecated (since := "2026-06-18")] alias mapDomainAddEquiv_apply := coeff_mapDomainAddEquiv

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
lemma `mapDomainAddEquiv_single` / 引理 `mapDomainAddEquiv_single`

English:
lemma mapDomainAddEquiv_single
  given: (e : M ≃ N) (r : R) (m : M)
  proof: by simp [mapDomainAddEquiv]

@[to_additive (attr := simp)]

中文:
引理 mapDomainAddEquiv_single
  条件: (e : M ≃ N) (r : R) (m : M)
  证明: by simp [mapDomainAddEquiv]

@[to_additive (attr := simp)]

Depends on / 依赖: mapDomainAddEquiv
-/
lemma mapDomainAddEquiv_single (e : M ≃ N) (r : R) (m : M) :
    mapDomainAddEquiv R e (single m r) = single (e m) r := by simp [mapDomainAddEquiv]

@[to_additive (attr := simp)]
/--
lemma `symm_mapDomainAddEquiv` / 引理 `symm_mapDomainAddEquiv`

English:
lemma symm_mapDomainAddEquiv
  given: (e : M ≃ N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 symm_mapDomainAddEquiv
  条件: (e : M ≃ N)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma symm_mapDomainAddEquiv (e : M ≃ N) :
    (mapDomainAddEquiv R e).symm = mapDomainAddEquiv R e.symm := rfl

@[to_additive (attr := simp)]
/--
lemma `mapDomainAddEquiv_trans` / 引理 `mapDomainAddEquiv_trans`

English:
lemma mapDomainAddEquiv_trans
  given: (e₁ : M ≃ N) (e₂ : N ≃ O)
  proof: by ext; simp

中文:
引理 mapDomainAddEquiv_trans
  条件: (e₁ : M ≃ N) (e₂ : N ≃ O)
  证明: by ext; simp
-/
lemma mapDomainAddEquiv_trans (e₁ : M ≃ N) (e₂ : N ≃ O) :
    mapDomainAddEquiv R (e₁.trans e₂) =
      (mapDomainAddEquiv R e₁).trans (mapDomainAddEquiv R e₂) := by ext; simp

variable (M) in
/-- Additively isomorphic rings have additively isomorphic monoid algebras.

`MonoidAlgebra.map` as an `AddEquiv`. -/
@[to_additive (dont_translate := R S)
/-- Additively isomorphic rings have additively isomorphic additive monoid algebras.

`AddMonoidAlgebra.map` as an `AddEquiv`. -/]
/--
Definition of `mapAddEquiv` / `mapAddEquiv` 的定义

English:
definition mapAddEquiv
  signature: (e : R ≃+ S)
  body: .map e
  invFun := .map e.symm
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' := MonoidAlgebra.map_add _

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv := mapAddEquiv

中文:
定义 mapAddEquiv
  签名: (e : R ≃+ S)
  定义体: .map e
  invFun := .map e.symm
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' := MonoidAlgebra.map_add _

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv := mapAddEquiv
-/
def mapAddEquiv (e : R ≃+ S) : R[M] ≃+ S[M] where
  toFun := .map e
  invFun := .map e.symm
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' := MonoidAlgebra.map_add _

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv := mapAddEquiv

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
lemma `coeff_mapAddEquiv` / 引理 `coeff_mapAddEquiv`

English:
lemma coeff_mapAddEquiv
  given: (e : R ≃+ S) (x : R[M]) (m : M)
  proof: by simp [mapAddEquiv]

@[deprecated (since := "2026-06-18")] alias mapAddEquiv_apply := coeff_mapAddEquiv

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv_apply := coeff_mapAddEquiv

中文:
引理 coeff_mapAddEquiv
  条件: (e : R ≃+ S) (x : R[M]) (m : M)
  证明: by simp [mapAddEquiv]

@[deprecated (since := "2026-06-18")] alias mapAddEquiv_apply := coeff_mapAddEquiv

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv_apply := coeff_mapAddEquiv

Depends on / 依赖: mapAddEquiv
-/
lemma coeff_mapAddEquiv (e : R ≃+ S) (x : R[M]) (m : M) :
    (mapAddEquiv M e x).coeff m = e (x.coeff m) := by simp [mapAddEquiv]

@[deprecated (since := "2026-06-18")] alias mapAddEquiv_apply := coeff_mapAddEquiv

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv_apply := coeff_mapAddEquiv

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
lemma `mapAddEquiv_single` / 引理 `mapAddEquiv_single`

English:
lemma mapAddEquiv_single
  given: (e : R ≃+ S) (r : R) (m : M)
  proof: by simp [mapAddEquiv]

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv_single := mapAddEquiv_single

@[to_additive (attr := simp)]

中文:
引理 mapAddEquiv_single
  条件: (e : R ≃+ S) (r : R) (m : M)
  证明: by simp [mapAddEquiv]

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv_single := mapAddEquiv_single

@[to_additive (attr := simp)]

Depends on / 依赖: mapAddEquiv
-/
lemma mapAddEquiv_single (e : R ≃+ S) (r : R) (m : M) :
    mapAddEquiv M e (single m r) = single m (e r) := by simp [mapAddEquiv]

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv_single := mapAddEquiv_single

@[to_additive (attr := simp)]
/--
lemma `symm_mapAddEquiv` / 引理 `symm_mapAddEquiv`

English:
lemma symm_mapAddEquiv
  given: (e : R ≃+ S)
  proof: rfl

@[deprecated (since := "2026-03-20")] alias symm_mapRangeAddEquiv := symm_mapAddEquiv

@[to_additive (attr := simp)]

中文:
引理 symm_mapAddEquiv
  条件: (e : R ≃+ S)
  证明: rfl

@[deprecated (since := "2026-03-20")] alias symm_mapRangeAddEquiv := symm_mapAddEquiv

@[to_additive (attr := simp)]
-/
lemma symm_mapAddEquiv (e : R ≃+ S) :
    (mapAddEquiv M e).symm = mapAddEquiv M e.symm := rfl

@[deprecated (since := "2026-03-20")] alias symm_mapRangeAddEquiv := symm_mapAddEquiv

@[to_additive (attr := simp)]
/--
lemma `mapAddEquiv_trans` / 引理 `mapAddEquiv_trans`

English:
lemma mapAddEquiv_trans
  given: (e₁ : R ≃+ S) (e₂ : S ≃+ T)
  proof: by
  ext; simp

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv_trans := mapAddEquiv_trans

@[to_additive (attr := simp) (dont_translate := R S) map_mul]

中文:
引理 mapAddEquiv_trans
  条件: (e₁ : R ≃+ S) (e₂ : S ≃+ T)
  证明: by
  ext; simp

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv_trans := mapAddEquiv_trans

@[to_additive (attr := simp) (dont_translate := R S) map_mul]
-/
lemma mapAddEquiv_trans (e₁ : R ≃+ S) (e₂ : S ≃+ T) :
    mapAddEquiv M (e₁.trans e₂) = (mapAddEquiv M e₁).trans (mapAddEquiv M e₂) := by
  ext; simp

@[deprecated (since := "2026-03-20")] alias mapRangeAddEquiv_trans := mapAddEquiv_trans

@[to_additive (attr := simp) (dont_translate := R S) map_mul]
/--
lemma `map_mul` / 引理 `map_mul`

English:
lemma map_mul
  given: (f : R ->+* S) (x y : R[M])
  proof: by
  classical
  ext
  simp [mul_def, sum_mapRange_index, map_finsuppSum, single_apply, apply_ite]

中文:
引理 map_mul
  条件: (f : R ->+* S) (x y : R[M])
  证明: by
  classical
  ext
  simp [mul_def, sum_mapRange_index, map_finsuppSum, single_apply, apply_ite]
-/
protected lemma map_mul (f : R ->+* S) (x y : R[M]) :
    map (f : R ->+ S) (x * y) = map f x * map f y := by
  classical
  ext
  simp [mul_def, sum_mapRange_index, map_finsuppSum, single_apply, apply_ite]

end Mul

variable [Monoid M] [Monoid N] [Monoid O]

variable (R) in
/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`MonoidAlgebra.mapDomain f` is a ring homomorphism between their monoid algebras. -/
@[to_additive (attr := simps) /--
If `f : G → H` is a multiplicative homomorphism between two additive monoids, then
`AddMonoidAlgebra.mapDomain f` is a ring homomorphism between their additive monoid algebras. -/]
/--
Definition of `mapDomainRingHom` / `mapDomainRingHom` 的定义

English:
definition mapDomainRingHom
  signature: (f : M ->* N)
  body: mapDomain f
  map_zero' := mapDomain_zero _
  map_add' := mapDomain_add _
  map_one' := mapDomain_one f
  map_mul' := mapDomain_mul f

中文:
定义 mapDomainRingHom
  签名: (f : M ->* N)
  定义体: mapDomain f
  map_zero' := mapDomain_zero _
  map_add' := mapDomain_add _
  map_one' := mapDomain_one f
  map_mul' := mapDomain_mul f

Depends on / 依赖: mapDomain
-/
def mapDomainRingHom (f : M ->* N) : R[M] ->+* R[N] where
  toFun := mapDomain f
  map_zero' := mapDomain_zero _
  map_add' := mapDomain_add _
  map_one' := mapDomain_one f
  map_mul' := mapDomain_mul f

attribute [local ext high] ringHom_ext

@[to_additive (dont_translate := R) (attr := simp)]
/--
lemma `mapDomainRingHom_id` / 引理 `mapDomainRingHom_id`

English:
lemma mapDomainRingHom_id
  statement: mapDomainRingHom R (.id M) = .id R[M]
  proof: by ext <;> simp

中文:
引理 mapDomainRingHom_id
  结论: mapDomainRingHom R (.id M) = .id R[M]
  证明: by ext <;> simp
-/
lemma mapDomainRingHom_id : mapDomainRingHom R (.id M) = .id R[M] := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := R) (attr := simp)]
/--
lemma `mapDomainRingHom_comp` / 引理 `mapDomainRingHom_comp`

English:
lemma mapDomainRingHom_comp
  given: (f : N ->* O) (g : M ->* N)
  proof: by
  ext <;> simp

@[to_additive (attr := simp) (dont_translate := R S) map_one]

中文:
引理 mapDomainRingHom_comp
  条件: (f : N ->* O) (g : M ->* N)
  证明: by
  ext <;> simp

@[to_additive (attr := simp) (dont_translate := R S) map_one]
-/
lemma mapDomainRingHom_comp (f : N ->* O) (g : M ->* N) :
    mapDomainRingHom R (f.comp g) = (mapDomainRingHom R f).comp (mapDomainRingHom R g) := by
  ext <;> simp

@[to_additive (attr := simp) (dont_translate := R S) map_one]
/--
lemma `map_one` / 引理 `map_one`

English:
lemma map_one
  given: (f : R ->+* S)
  statement: map f (1 : R[M]) = (1 : S[M])
  proof: by ext; simp [one_def]

中文:
引理 map_one
  条件: (f : R ->+* S)
  结论: map f (1 : R[M]) = (1 : S[M])
  证明: by ext; simp [one_def]
-/
protected lemma map_one (f : R ->+* S) : map f (1 : R[M]) = (1 : S[M]) := by ext; simp [one_def]

variable (M) in
/-- The ring homomorphism of monoid algebras induced by a homomorphism of the base rings. -/
@[to_additive (dont_translate := R S)
/-- The ring homomorphism of additive monoid algebras induced by a homomorphism of the base rings.
-/]
/--
Definition of `mapRingHom` / `mapRingHom` 的定义

English:
definition mapRingHom
  signature: (f : R ->+* S)
  body: .map f
  map_zero' := MonoidAlgebra.map_zero _
  map_add' := MonoidAlgebra.map_add _
  map_one' := MonoidAlgebra.map_one _
  map_mul' := MonoidAlgebra.map_mul _

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom := mapRingHom

@[to_additive]

中文:
定义 mapRingHom
  签名: (f : R ->+* S)
  定义体: .map f
  map_zero' := MonoidAlgebra.map_zero _
  map_add' := MonoidAlgebra.map_add _
  map_one' := MonoidAlgebra.map_one _
  map_mul' := MonoidAlgebra.map_mul _

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom := mapRingHom

@[to_additive]
-/
noncomputable def mapRingHom (f : R ->+* S) : R[M] ->+* S[M] where
  toFun := .map f
  map_zero' := MonoidAlgebra.map_zero _
  map_add' := MonoidAlgebra.map_add _
  map_one' := MonoidAlgebra.map_one _
  map_mul' := MonoidAlgebra.map_mul _

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom := mapRingHom

@[to_additive]
/--
lemma `coe_mapRingHom` / 引理 `coe_mapRingHom`

English:
lemma coe_mapRingHom
  given: (f : R ->+* S)
  statement: ⇑(mapRingHom M f) = map f
  proof: rfl

@[deprecated (since := "2026-03-20")] alias coe_mapRangeRingHom := coe_mapRingHom

中文:
引理 coe_mapRingHom
  条件: (f : R ->+* S)
  结论: ⇑(mapRingHom M f) = map f
  证明: rfl

@[deprecated (since := "2026-03-20")] alias coe_mapRangeRingHom := coe_mapRingHom
-/
lemma coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom M f) = map f := rfl

@[deprecated (since := "2026-03-20")] alias coe_mapRangeRingHom := coe_mapRingHom

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
lemma `coeff_mapRingHom` / 引理 `coeff_mapRingHom`

English:
lemma coeff_mapRingHom
  given: (f : R ->+* S) (x : R[M]) (m : M)
  proof: by simp [mapRingHom]

@[deprecated (since := "2026-06-18")] alias mapRingHom_apply := coeff_mapRingHom

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_apply := coeff_mapRingHom

@[to_additive (attr := simp)]

中文:
引理 coeff_mapRingHom
  条件: (f : R ->+* S) (x : R[M]) (m : M)
  证明: by simp [mapRingHom]

@[deprecated (since := "2026-06-18")] alias mapRingHom_apply := coeff_mapRingHom

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_apply := coeff_mapRingHom

@[to_additive (attr := simp)]

Depends on / 依赖: mapRingHom
-/
lemma coeff_mapRingHom (f : R ->+* S) (x : R[M]) (m : M) :
    (mapRingHom M f x).coeff m = f (x.coeff m) := by simp [mapRingHom]

@[deprecated (since := "2026-06-18")] alias mapRingHom_apply := coeff_mapRingHom

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_apply := coeff_mapRingHom

@[to_additive (attr := simp)]
/--
lemma `mapRingHom_single` / 引理 `mapRingHom_single`

English:
lemma mapRingHom_single
  given: (f : R ->+* S) (a : M) (b : R)
  proof: by simp [mapRingHom]

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_single := mapRingHom_single

@[to_additive (dont_translate := R) (attr := simp)]

中文:
引理 mapRingHom_single
  条件: (f : R ->+* S) (a : M) (b : R)
  证明: by simp [mapRingHom]

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_single := mapRingHom_single

@[to_additive (dont_translate := R) (attr := simp)]

Depends on / 依赖: mapRingHom
-/
lemma mapRingHom_single (f : R ->+* S) (a : M) (b : R) :
    mapRingHom M f (single a b) = single a (f b) := by simp [mapRingHom]

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_single := mapRingHom_single

@[to_additive (dont_translate := R) (attr := simp)]
/--
lemma `mapRingHom_id` / 引理 `mapRingHom_id`

English:
lemma mapRingHom_id
  statement: mapRingHom M (.id R) = .id R[M]
  proof: by ext <;> simp

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_id := mapRingHom_id

@[to_additive (dont_translate := R S T) (attr := simp)]

中文:
引理 mapRingHom_id
  结论: mapRingHom M (.id R) = .id R[M]
  证明: by ext <;> simp

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_id := mapRingHom_id

@[to_additive (dont_translate := R S T) (attr := simp)]
-/
lemma mapRingHom_id : mapRingHom M (.id R) = .id R[M] := by ext <;> simp

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_id := mapRingHom_id

@[to_additive (dont_translate := R S T) (attr := simp)]
/--
lemma `mapRingHom_comp` / 引理 `mapRingHom_comp`

English:
lemma mapRingHom_comp
  given: (f : S ->+* T) (g : R ->+* S)
  proof: by
  ext <;> simp

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_comp := mapRingHom_comp

@[to_additive (dont_translate := R S)]

中文:
引理 mapRingHom_comp
  条件: (f : S ->+* T) (g : R ->+* S)
  证明: by
  ext <;> simp

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_comp := mapRingHom_comp

@[to_additive (dont_translate := R S)]
-/
lemma mapRingHom_comp (f : S ->+* T) (g : R ->+* S) :
    mapRingHom M (f.comp g) = (mapRingHom M f).comp (mapRingHom M g) := by
  ext <;> simp

@[deprecated (since := "2026-03-20")] alias mapRangeRingHom_comp := mapRingHom_comp

@[to_additive (dont_translate := R S)]
/--
lemma `mapRingHom_comp_mapDomainRingHom` / 引理 `mapRingHom_comp_mapDomainRingHom`

English:
lemma mapRingHom_comp_mapDomainRingHom
  given: (f : R ->+* S) (g : M ->* N)
  proof: by aesop

@[deprecated (since := "2026-03-20")]
alias mapRangeRingHom_comp_mapDomainRingHom := mapRingHom_comp_mapDomainRingHom

中文:
引理 mapRingHom_comp_mapDomainRingHom
  条件: (f : R ->+* S) (g : M ->* N)
  证明: by aesop

@[deprecated (since := "2026-03-20")]
alias mapRangeRingHom_comp_mapDomainRingHom := mapRingHom_comp_mapDomainRingHom
-/
lemma mapRingHom_comp_mapDomainRingHom (f : R ->+* S) (g : M ->* N) :
    (mapRingHom N f).comp (mapDomainRingHom R g) =
      (mapDomainRingHom S g).comp (mapRingHom M f) := by aesop

@[deprecated (since := "2026-03-20")]
alias mapRangeRingHom_comp_mapDomainRingHom := mapRingHom_comp_mapDomainRingHom

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[to_additive (dont_translate := R)
/-- Isomorphic monoids have isomorphic additive monoid algebras. -/]
/--
Definition of `mapDomainRingEquiv` / `mapDomainRingEquiv` 的定义

English:
definition mapDomainRingEquiv
  signature: (e : M ≃* N)
  body: .ofRingHom (MonoidAlgebra.mapDomainRingHom R e) (MonoidAlgebra.mapDomainRingHom R e.symm)
    (by apply MonoidAlgebra.ringHom_ext <;> simp) (by apply MonoidAlgebra.ringHom_ext <;> simp)

@[to_additive (attr := simp)]

中文:
定义 mapDomainRingEquiv
  签名: (e : M ≃* N)
  定义体: .ofRingHom (MonoidAlgebra.mapDomainRingHom R e) (MonoidAlgebra.mapDomainRingHom R e.symm)
    (by apply MonoidAlgebra.ringHom_ext <;> simp) (by apply MonoidAlgebra.ringHom_ext <;> simp)

@[to_additive (attr := simp)]

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.ringHom_ext, e.symm, mapDomainRingHom, ofRingHom, ringHom_ext
-/
def mapDomainRingEquiv (e : M ≃* N) : R[M] ≃+* R[N] :=
  .ofRingHom (MonoidAlgebra.mapDomainRingHom R e) (MonoidAlgebra.mapDomainRingHom R e.symm)
    (by apply MonoidAlgebra.ringHom_ext <;> simp) (by apply MonoidAlgebra.ringHom_ext <;> simp)

@[to_additive (attr := simp)]
/--
lemma `coeff_mapDomainRingEquiv` / 引理 `coeff_mapDomainRingEquiv`

English:
lemma coeff_mapDomainRingEquiv
  given: (e : M ≃* N) (x : R[M])
  proof: coeff_mapDomainAddEquiv ..

@[deprecated (since := "2026-06-18")] alias mapDomainRingEquiv_apply := coeff_mapDomainRingEquiv

中文:
引理 coeff_mapDomainRingEquiv
  条件: (e : M ≃* N) (x : R[M])
  证明: coeff_mapDomainAddEquiv ..

@[deprecated (since := "2026-06-18")] alias mapDomainRingEquiv_apply := coeff_mapDomainRingEquiv

Depends on / 依赖: coeff_mapDomainAddEquiv
-/
lemma coeff_mapDomainRingEquiv (e : M ≃* N) (x : R[M]) :
    (mapDomainRingEquiv R e x).coeff = equivMapDomain e x.coeff := coeff_mapDomainAddEquiv ..

@[deprecated (since := "2026-06-18")] alias mapDomainRingEquiv_apply := coeff_mapDomainRingEquiv

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
lemma `mapDomainRingEquiv_single` / 引理 `mapDomainRingEquiv_single`

English:
lemma mapDomainRingEquiv_single
  given: (e : M ≃* N) (r : R) (m : M)
  proof: by simp [mapDomainRingEquiv]

@[to_additive]

中文:
引理 mapDomainRingEquiv_single
  条件: (e : M ≃* N) (r : R) (m : M)
  证明: by simp [mapDomainRingEquiv]

@[to_additive]

Depends on / 依赖: mapDomainRingEquiv
-/
lemma mapDomainRingEquiv_single (e : M ≃* N) (r : R) (m : M) :
    mapDomainRingEquiv R e (single m r) = single (e m) r := by simp [mapDomainRingEquiv]

@[to_additive]
/--
lemma `toRingHom_mapDomainRingEquiv` / 引理 `toRingHom_mapDomainRingEquiv`

English:
lemma toRingHom_mapDomainRingEquiv
  given: (e : M ≃* N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 toRingHom_mapDomainRingEquiv
  条件: (e : M ≃* N)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma toRingHom_mapDomainRingEquiv (e : M ≃* N) :
    (mapDomainRingEquiv R e).toRingHom = mapDomainRingHom R e := rfl

@[to_additive (attr := simp)]
/--
lemma `symm_mapDomainRingEquiv` / 引理 `symm_mapDomainRingEquiv`

English:
lemma symm_mapDomainRingEquiv
  given: (e : M ≃* N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 symm_mapDomainRingEquiv
  条件: (e : M ≃* N)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma symm_mapDomainRingEquiv (e : M ≃* N) :
    (mapDomainRingEquiv R e).symm = mapDomainRingEquiv R e.symm := rfl

@[to_additive (attr := simp)]
/--
lemma `mapDomainRingEquiv_trans` / 引理 `mapDomainRingEquiv_trans`

English:
lemma mapDomainRingEquiv_trans
  given: (e₁ : M ≃* N) (e₂ : N ≃* O)
  proof: by ext; simp

中文:
引理 mapDomainRingEquiv_trans
  条件: (e₁ : M ≃* N) (e₂ : N ≃* O)
  证明: by ext; simp
-/
lemma mapDomainRingEquiv_trans (e₁ : M ≃* N) (e₂ : N ≃* O) :
    mapDomainRingEquiv R (e₁.trans e₂) =
      (mapDomainRingEquiv R e₁).trans (mapDomainRingEquiv R e₂) := by ext; simp

variable (M) in
/-- Isomorphic rings have isomorphic monoid algebras. -/
@[to_additive (dont_translate := R S)
/-- Isomorphic rings have isomorphic additive monoid algebras. -/]
/--
Definition of `mapRingEquiv` / `mapRingEquiv` 的定义

English:
definition mapRingEquiv
  signature: (e : R ≃+* S)
  body: .ofRingHom (MonoidAlgebra.mapRingHom M e) (MonoidAlgebra.mapRingHom M e.symm)
    (by apply MonoidAlgebra.ringHom_ext <;> simp) (by apply MonoidAlgebra.ringHom_ext <;> simp)

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv := mapRingEquiv

@[to_additive (attr := simp)]

中文:
定义 mapRingEquiv
  签名: (e : R ≃+* S)
  定义体: .ofRingHom (MonoidAlgebra.mapRingHom M e) (MonoidAlgebra.mapRingHom M e.symm)
    (by apply MonoidAlgebra.ringHom_ext <;> simp) (by apply MonoidAlgebra.ringHom_ext <;> simp)

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv := mapRingEquiv

@[to_additive (attr := simp)]

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.mapRingHom, MonoidAlgebra.ringHom_ext, e.symm, mapRingHom, ofRingHom, ringHom_ext
-/
def mapRingEquiv (e : R ≃+* S) : R[M] ≃+* S[M] :=
  .ofRingHom (MonoidAlgebra.mapRingHom M e) (MonoidAlgebra.mapRingHom M e.symm)
    (by apply MonoidAlgebra.ringHom_ext <;> simp) (by apply MonoidAlgebra.ringHom_ext <;> simp)

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv := mapRingEquiv

@[to_additive (attr := simp)]
/--
lemma `coeff_mapRingEquiv` / 引理 `coeff_mapRingEquiv`

English:
lemma coeff_mapRingEquiv
  given: (e : R ≃+* S) (x : R[M]) (m : M)
  proof: by simp [mapRingEquiv]

@[deprecated (since := "2026-06-18")] alias mapRingEquiv_apply := coeff_mapRingEquiv

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv_apply := coeff_mapRingEquiv

@[to_additive (attr := simp)]

中文:
引理 coeff_mapRingEquiv
  条件: (e : R ≃+* S) (x : R[M]) (m : M)
  证明: by simp [mapRingEquiv]

@[deprecated (since := "2026-06-18")] alias mapRingEquiv_apply := coeff_mapRingEquiv

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv_apply := coeff_mapRingEquiv

@[to_additive (attr := simp)]

Depends on / 依赖: mapRingEquiv
-/
lemma coeff_mapRingEquiv (e : R ≃+* S) (x : R[M]) (m : M) :
    (mapRingEquiv M e x).coeff m = e (x.coeff m) := by simp [mapRingEquiv]

@[deprecated (since := "2026-06-18")] alias mapRingEquiv_apply := coeff_mapRingEquiv

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv_apply := coeff_mapRingEquiv

@[to_additive (attr := simp)]
/--
lemma `mapRingEquiv_single` / 引理 `mapRingEquiv_single`

English:
lemma mapRingEquiv_single
  given: (e : R ≃+* S) (r : R) (m : M)
  proof: by simp [mapRingEquiv]

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv_single := mapRingEquiv_single

@[to_additive]

中文:
引理 mapRingEquiv_single
  条件: (e : R ≃+* S) (r : R) (m : M)
  证明: by simp [mapRingEquiv]

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv_single := mapRingEquiv_single

@[to_additive]

Depends on / 依赖: mapRingEquiv
-/
lemma mapRingEquiv_single (e : R ≃+* S) (r : R) (m : M) :
    mapRingEquiv M e (single m r) = single m (e r) := by simp [mapRingEquiv]

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv_single := mapRingEquiv_single

@[to_additive]
/--
lemma `toRingHom_mapRingEquiv` / 引理 `toRingHom_mapRingEquiv`

English:
lemma toRingHom_mapRingEquiv
  given: (e : R ≃+* S)
  proof: rfl

@[deprecated (since := "2026-03-20")]
alias toRingHom_mapRangeRingEquiv := toRingHom_mapRingEquiv

@[to_additive (attr := simp)]

中文:
引理 toRingHom_mapRingEquiv
  条件: (e : R ≃+* S)
  证明: rfl

@[deprecated (since := "2026-03-20")]
alias toRingHom_mapRangeRingEquiv := toRingHom_mapRingEquiv

@[to_additive (attr := simp)]
-/
lemma toRingHom_mapRingEquiv (e : R ≃+* S) :
    (mapRingEquiv M e).toRingHom = mapRingHom M e := rfl

@[deprecated (since := "2026-03-20")]
alias toRingHom_mapRangeRingEquiv := toRingHom_mapRingEquiv

@[to_additive (attr := simp)]
/--
lemma `symm_mapRingEquiv` / 引理 `symm_mapRingEquiv`

English:
lemma symm_mapRingEquiv
  given: (e : R ≃+* S)
  proof: rfl

@[deprecated (since := "2026-03-20")] alias symm_mapRangeRingEquiv := symm_mapRingEquiv

@[to_additive (attr := simp)]

中文:
引理 symm_mapRingEquiv
  条件: (e : R ≃+* S)
  证明: rfl

@[deprecated (since := "2026-03-20")] alias symm_mapRangeRingEquiv := symm_mapRingEquiv

@[to_additive (attr := simp)]
-/
lemma symm_mapRingEquiv (e : R ≃+* S) :
    (mapRingEquiv M e).symm = mapRingEquiv M e.symm := rfl

@[deprecated (since := "2026-03-20")] alias symm_mapRangeRingEquiv := symm_mapRingEquiv

@[to_additive (attr := simp)]
/--
lemma `mapRingEquiv_trans` / 引理 `mapRingEquiv_trans`

English:
lemma mapRingEquiv_trans
  given: (e₁ : R ≃+* S) (e₂ : S ≃+* T)
  proof: by ext; simp

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv_trans := mapRingEquiv_trans

中文:
引理 mapRingEquiv_trans
  条件: (e₁ : R ≃+* S) (e₂ : S ≃+* T)
  证明: by ext; simp

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv_trans := mapRingEquiv_trans
-/
lemma mapRingEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* T) :
    mapRingEquiv M (e₁.trans e₂) =
      (mapRingEquiv M e₁).trans (mapRingEquiv M e₂) := by ext; simp

@[deprecated (since := "2026-03-20")] alias mapRangeRingEquiv_trans := mapRingEquiv_trans

/-- Nested monoid algebras can be taken in an arbitrary order. -/
@[to_additive (dont_translate := R)
/-- Nested additive monoid algebras can be taken in an arbitrary order. -/]
/--
Definition of `commRingEquiv` / `commRingEquiv` 的定义

English:
definition commRingEquiv
  signature: : R[M][N] ≃+* R[N][M]
  body: curryRingEquiv.symm.trans .trans (mapDomainRingEquiv _ <| .prodComm ..) curryRingEquiv

@[to_additive (attr := simp)]

中文:
定义 commRingEquiv
  签名: : R[M][N] ≃+* R[N][M]
  定义体: curryRingEquiv.symm.trans .trans (mapDomainRingEquiv _ <| .prodComm ..) curryRingEquiv

@[to_additive (attr := simp)]

Depends on / 依赖: curryRingEquiv, curryRingEquiv.symm.trans, mapDomainRingEquiv, prodComm
-/
def commRingEquiv : R[M][N] ≃+* R[N][M] :=
curryRingEquiv.symm.trans .trans (mapDomainRingEquiv _ <| .prodComm ..) curryRingEquiv

@[to_additive (attr := simp)]
/--
lemma `symm_commRingEquiv` / 引理 `symm_commRingEquiv`

English:
lemma symm_commRingEquiv
  statement: (commRingEquiv : R[M][N] ≃+* R[N][M]).symm = commRingEquiv
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 symm_commRingEquiv
  结论: (commRingEquiv : R[M][N] ≃+* R[N][M]).symm = commRingEquiv
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma symm_commRingEquiv : (commRingEquiv : R[M][N] ≃+* R[N][M]).symm = commRingEquiv := rfl

@[to_additive (attr := simp)]
/--
lemma `commRingEquiv_single_single` / 引理 `commRingEquiv_single_single`

English:
lemma commRingEquiv_single_single
  given: (m : M) (n : N) (r : R)
  proof: by simp [commRingEquiv]

@[to_additive (dont_translate := R) (attr := simp)]

中文:
引理 commRingEquiv_single_single
  条件: (m : M) (n : N) (r : R)
  证明: by simp [commRingEquiv]

@[to_additive (dont_translate := R) (attr := simp)]

Depends on / 依赖: commRingEquiv
-/
lemma commRingEquiv_single_single (m : M) (n : N) (r : R) :
    commRingEquiv (single m <| single n r) = single n (single m r) := by simp [commRingEquiv]

@[to_additive (dont_translate := R) (attr := simp)]
/--
lemma `commRingEquiv_single_one` / 引理 `commRingEquiv_single_one`

English:
lemma commRingEquiv_single_one
  given: (m : M)
  proof: commRingEquiv_single_single ..

中文:
引理 commRingEquiv_single_one
  条件: (m : M)
  证明: commRingEquiv_single_single ..

Depends on / 依赖: commRingEquiv_single_single
-/
lemma commRingEquiv_single_one (m : M) :
    commRingEquiv (single m (1 : R[N])) = single 1 (single m 1) := commRingEquiv_single_single ..

-- We want this to have higher priority than `commRingEquiv_single_single`
@[to_additive (dont_translate := R) (attr := simp high)]
/--
lemma `commRingEquiv_single_one_single` / 引理 `commRingEquiv_single_one_single`

English:
lemma commRingEquiv_single_one_single
  given: (m : M)
  proof: commRingEquiv_single_single ..

中文:
引理 commRingEquiv_single_one_single
  条件: (m : M)
  证明: commRingEquiv_single_single ..

Depends on / 依赖: commRingEquiv_single_single
-/
lemma commRingEquiv_single_one_single (m : M) :
    commRingEquiv (single 1 <| single m 1) = (single m (1 : R[N])) := commRingEquiv_single_single ..

end Semiring

section Ring
variable [Ring R] [Ring S]

@[to_additive]
/--
lemma `map_neg` / 引理 `map_neg`

English:
lemma map_neg
  given: (f : R ->+ S) (x : R[M])
  statement: map f (-x) = -map f x
  proof: by ext; simp

@[to_additive]

中文:
引理 map_neg
  条件: (f : R ->+ S) (x : R[M])
  结论: map f (-x) = -map f x
  证明: by ext; simp

@[to_additive]
-/
protected lemma map_neg (f : R ->+ S) (x : R[M]) : map f (-x) = -map f x := by ext; simp

@[to_additive]
/--
lemma `map_sub` / 引理 `map_sub`

English:
lemma map_sub
  given: (f : R ->+ S) (x y : R[M])
  statement: map f (x - y) = map f x - map f y
  proof: by
  ext; simp

中文:
引理 map_sub
  条件: (f : R ->+ S) (x y : R[M])
  结论: map f (x - y) = map f x - map f y
  证明: by
  ext; simp
-/
protected lemma map_sub (f : R ->+ S) (x y : R[M]) : map f (x - y) = map f x - map f y := by
  ext; simp

end Ring
end MonoidAlgebra

/-!
#### Conversions between `AddMonoidAlgebra` and `MonoidAlgebra`
-/

namespace AddMonoidAlgebra
variable [Semiring R] [Add M]

set_option backward.isDefEq.respectTransparency false in
variable (R M) in
/-- The equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative` -/
@[simps]
/--
Definition of `toMultiplicative` / `toMultiplicative` 的定义

English:
definition toMultiplicative
  signature: : AddMonoidAlgebra R M ≃+* MonoidAlgebra R (Multiplicative M) where
  body: .ofCoeff x.coeff.mapDomain .ofAdd
invFun x := .ofCoeff x.coeff.mapDomain Multiplicative.toAdd
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by simp [Finsupp.mapDomain_add]
  map_mul' x y := by
    classical
    ext
    simp [MonoidAlgebra.coeff_mul, coeff_mul, sum_mapD

中文:
定义 toMultiplicative
  签名: : AddMonoidAlgebra R M ≃+* MonoidAlgebra R (Multiplicative M) where
  定义体: .ofCoeff x.coeff.mapDomain .ofAdd
invFun x := .ofCoeff x.coeff.mapDomain Multiplicative.toAdd
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by simp [Finsupp.mapDomain_add]
  map_mul' x y := by
    classical
    ext
    simp [MonoidAlgebra.coeff_mul, coeff_mul, sum_mapD

Depends on / 依赖: mapDomain, ofCoeff, x.coeff.mapDomain
-/
def toMultiplicative : AddMonoidAlgebra R M ≃+* MonoidAlgebra R (Multiplicative M) where
toFun x := .ofCoeff x.coeff.mapDomain .ofAdd
invFun x := .ofCoeff x.coeff.mapDomain Multiplicative.toAdd
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by simp [Finsupp.mapDomain_add]
  map_mul' x y := by
    classical
    ext
    simp [MonoidAlgebra.coeff_mul, coeff_mul, sum_mapDomain_index, add_mul, mul_add, ite_add_zero,
      Multiplicative.ext_iff]

@[simp]
/--
lemma `toMultiplicative_single` / 引理 `toMultiplicative_single`

English:
lemma toMultiplicative_single
  given: (m : M) (r : R)
  proof: by simp [toMultiplicative]

中文:
引理 toMultiplicative_single
  条件: (m : M) (r : R)
  证明: by simp [toMultiplicative]

Depends on / 依赖: toMultiplicative
-/
lemma toMultiplicative_single (m : M) (r : R) :
    toMultiplicative R M (single m r) = .single (.ofAdd m) r := by simp [toMultiplicative]

end AddMonoidAlgebra

namespace MonoidAlgebra
variable [Semiring R] [Mul M]

set_option backward.isDefEq.respectTransparency false in
variable (R M) in
/-- The equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms of `Additive` -/
@[simps]
/--
Definition of `toAdditive` / `toAdditive` 的定义

English:
definition toAdditive
  signature: : MonoidAlgebra R M ≃+* AddMonoidAlgebra R (Additive M) where
  body: .ofCoeff x.coeff.mapDomain .ofMul
invFun x := .ofCoeff x.coeff.mapDomain Additive.toMul
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by simp [Finsupp.mapDomain_add]
  map_mul' x y := by
    classical
    ext
    simp [coeff_mul, AddMonoidAlgebra.coeff_mul, sum_mapDoma

中文:
定义 toAdditive
  签名: : MonoidAlgebra R M ≃+* AddMonoidAlgebra R (Additive M) where
  定义体: .ofCoeff x.coeff.mapDomain .ofMul
invFun x := .ofCoeff x.coeff.mapDomain Additive.toMul
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by simp [Finsupp.mapDomain_add]
  map_mul' x y := by
    classical
    ext
    simp [coeff_mul, AddMonoidAlgebra.coeff_mul, sum_mapDoma

Depends on / 依赖: mapDomain, ofCoeff, x.coeff.mapDomain
-/
def toAdditive : MonoidAlgebra R M ≃+* AddMonoidAlgebra R (Additive M) where
toFun x := .ofCoeff x.coeff.mapDomain .ofMul
invFun x := .ofCoeff x.coeff.mapDomain Additive.toMul
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by simp [Finsupp.mapDomain_add]
  map_mul' x y := by
    classical
    ext
    simp [coeff_mul, AddMonoidAlgebra.coeff_mul, sum_mapDomain_index, add_mul, mul_add,
      ite_add_zero, Additive.ext_iff]

@[simp]
/--
lemma `toAdditive_single` / 引理 `toAdditive_single`

English:
lemma toAdditive_single
  given: (m : M) (r : R)
  statement: toAdditive R M (single m r) = .single (.ofMul m) r
  proof: by
  ext; simp

中文:
引理 toAdditive_single
  条件: (m : M) (r : R)
  结论: toAdditive R M (single m r) = .single (.ofMul m) r
  证明: by
  ext; simp
-/
lemma toAdditive_single (m : M) (r : R) : toAdditive R M (single m r) = .single (.ofMul m) r := by
  ext; simp

end MonoidAlgebra
