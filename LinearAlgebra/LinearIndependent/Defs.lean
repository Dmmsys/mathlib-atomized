/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen
-/
module

public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public meta import Mathlib.Lean.Expr.ExtraRecognizers

/-!

# Linear independence

This file defines linear independence in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define `LinearIndependent R v` as `Function.Injective (Finsupp.linearCombination R v)`. Here
`Finsupp.linearCombination` is the linear map sending a function `f : ι →₀ R` with finite support to
the linear combination of vectors from `v` with these coefficients.

The goal of this file is to define linear independence and to prove that several other
statements are equivalent to this one, including `ker (Finsupp.linearCombination R v) = ⊥` and
some versions with explicitly written linear combinations.

## Main definitions
All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `LinearIndependent R v` states that the elements of the family `v` are linearly independent.

* `LinearIndepOn R v s` states that the elements of the family `v` indexed by the members
  of the set `s : Set ι` are linearly independent.

* `LinearIndependent.repr hv x` returns the linear combination representing `x : span R (range v)`
  on the linearly independent vectors `v`, given `hv : LinearIndependent R v`
  (using classical choice). `LinearIndependent.repr hv` is provided as a linear map.

* `LinearIndependent.Maximal` states that there exists no linear independent family that strictly
  includes the given one.

## Main results

* `Fintype.linearIndependent_iff`: if `ι` is a finite type, then any function `f : ι → R` has
  finite support, so we can reformulate the statement using `∑ i : ι, f i • v i` instead of a sum
  over an auxiliary `s : Finset ι`;

## Implementation notes

We use families instead of sets in `LinearIndependent` because it allows us to say that two
identical vectors are linearly dependent.

If you want to use sets, use `LinearIndepOn id s` given a set `s : Set M`. The lemmas
`LinearIndependent.linearIndepOn_id` and `LinearIndependent.of_linearIndepOn_id_range` connect those
two worlds.

In this file we prove some variants of results on different kinds of (semi)rings. We distinguish
them by using suffixes in their names, e.g. `linearIndependent_iffₛ` for semirings,
`linearIndependent_iffₒₛ` for (canonically) ordered semirings, and `linearIndependent_iff` (without
suffix) for rings.

## TODO

This file contains much more than definitions.

Rework proofs to hold in semirings, by avoiding the path through
`ker (Finsupp.linearCombination R v) = ⊥`.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/

@[expose] public section

assert_not_exists Cardinal

noncomputable section

open Function Module Set Submodule

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}
variable {M : Type*} {M' : Type*} {V : Type u}

section Semiring


variable {v : ι -> M}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R M']
variable (R) (v)
/--
Definition of `LinearIndependent` / `LinearIndependent` 的定义

English:
definition LinearIndependent
  signature: : Prop
  body: Injective (Finsupp.linearCombination R v)

中文:
定义 LinearIndependent
  签名: : 命题
  定义体: Injective (Finsupp.linearCombination R v)

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Injective, linearCombination
-/
def LinearIndependent : Prop :=
  Injective (Finsupp.linearCombination R v)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `LinearIndependent` that suggests pretty printing with type hints
in case the family of vectors is over a `Set`.

Type hints look like `LinearIndependent fun (v : ↑s) => ↑v` or `LinearIndependent (ι := ↑s) f`,
depending on whether the family is a lambda expression or not. -/
@[app_delab LinearIndependent]
meta def delabLinearIndependent : Delab :=
whenPPOption getPPNotation
whenNotPPOption getPPAnalysisSkip
  withOptionAtCurrPos `pp.analysis.skip true do
    let e ← getExpr
guard e.isAppOfArity ``LinearIndependent 7
    let some _ := (e.getArg! 0).coeTypeSet? | failure
    let optionsPerPos ← if (e.getArg! 3).isLambda then
      withNaryArg 3 do return (← read).optionsPerPos.setBool (← getPos) pp.funBinderTypes.name true
    else
      withNaryArg 0 do return (← read).optionsPerPos.setBool (← getPos) `pp.analysis.namedArg true
    withTheReader Context ({· with optionsPerPos}) delab

/--
Definition of `LinearIndepOn` / `LinearIndepOn` 的定义

English:
definition LinearIndepOn
  signature: (s : Set ι)
  body: LinearIndependent R (fun x : s => v x)

中文:
定义 LinearIndepOn
  签名: (s : 集合 ι)
  定义体: LinearIndependent R (fun x : s => v x)

Depends on / 依赖: LinearIndependent
-/
def LinearIndepOn (s : Set ι) : Prop := LinearIndependent R (fun x : s => v x)

variable {R v}

/--
theorem `LinearIndepOn.linearIndependent` / 定理 `LinearIndepOn.linearIndependent`

English:
theorem LinearIndepOn.linearIndependent
  given: {s : Set ι} (h : LinearIndepOn R v s)
  proof: h

中文:
定理 LinearIndepOn.linearIndependent
  条件: {s : 集合 ι} (h : LinearIndepOn R v s)
  证明: h
-/
theorem LinearIndepOn.linearIndependent {s : Set ι} (h : LinearIndepOn R v s) :
    LinearIndependent R (fun x : s => v x) := h

/--
theorem `linearIndependent_iff_injective_finsuppLinearCombination` / 定理 `linearIndependent_iff_injective_finsuppLinearCombination`

English:
theorem linearIndependent_iff_injective_finsuppLinearCombination
  proof: Iff.rfl

alias ⟨LinearIndependent.finsuppLinearCombination_injective, _⟩ :=
  linearIndependent_iff_injective_finsuppLinearCombination

中文:
定理 linearIndependent_iff_injective_finsuppLinearCombination
  证明: Iff.rfl

alias ⟨LinearIndependent.finsuppLinearCombination_injective, _⟩ :=
  linearIndependent_iff_injective_finsuppLinearCombination

Depends on / 依赖: Iff.rfl
-/
theorem linearIndependent_iff_injective_finsuppLinearCombination :
    LinearIndependent R v ↔ Injective (Finsupp.linearCombination R v) := Iff.rfl

alias ⟨LinearIndependent.finsuppLinearCombination_injective, _⟩ :=
  linearIndependent_iff_injective_finsuppLinearCombination

/--
theorem `linearIndependent_iff_injective_fintypeLinearCombination` / 定理 `linearIndependent_iff_injective_fintypeLinearCombination`

English:
theorem linearIndependent_iff_injective_fintypeLinearCombination
  given: [Fintype ι]
  proof: by
  simp [← Finsupp.linearCombination_eq_fintype_linearCombination, LinearIndependent]

alias ⟨LinearIndependent.fintypeLinearCombination_injective, _⟩ :=
  linearIndependent_iff_injective_fintypeLinearCombination

中文:
定理 linearIndependent_iff_injective_fintypeLinearCombination
  条件: [有限类型 ι]
  证明: by
  simp [← Finsupp.linearCombination_eq_fintype_linearCombination, LinearIndependent]

alias ⟨LinearIndependent.fintypeLinearCombination_injective, _⟩ :=
  linearIndependent_iff_injective_fintypeLinearCombination

Depends on / 依赖: Finsupp, Finsupp.linearCombination_eq_fintype_linearCombination, LinearIndependent, linearCombination_eq_fintype_linearCombination
-/
theorem linearIndependent_iff_injective_fintypeLinearCombination [Fintype ι] :
    LinearIndependent R v ↔ Injective (Fintype.linearCombination R v) := by
  simp [← Finsupp.linearCombination_eq_fintype_linearCombination, LinearIndependent]

alias ⟨LinearIndependent.fintypeLinearCombination_injective, _⟩ :=
  linearIndependent_iff_injective_fintypeLinearCombination

/--
theorem `LinearIndependent.injective` / 定理 `LinearIndependent.injective`

English:
theorem LinearIndependent.injective
  given: [Nontrivial R] (hv : LinearIndependent R v)
  statement: Injective v
  proof: by
  simpa [comp_def]
    using Injective.comp hv (Finsupp.single_left_injective one_ne_zero)

中文:
定理 LinearIndependent.injective
  条件: [非平凡 R] (hv : LinearIndependent R v)
  结论: 单射 v
  证明: by
  simpa [comp_def]
    using Injective.comp hv (Finsupp.single_left_injective one_ne_zero)

Depends on / 依赖: Finsupp, Finsupp.single_left_injective, Injective, Injective.comp, comp_def, one_ne_zero, single_left_injective
-/
theorem LinearIndependent.injective [Nontrivial R] (hv : LinearIndependent R v) : Injective v := by
  simpa [comp_def]
    using Injective.comp hv (Finsupp.single_left_injective one_ne_zero)

/--
theorem `LinearIndepOn.injOn` / 定理 `LinearIndepOn.injOn`

English:
theorem LinearIndepOn.injOn
  given: [Nontrivial R] (hv : LinearIndepOn R v s)
  statement: InjOn v s
  proof: injOn_iff_injective.2 LinearIndependent.injective hv

中文:
定理 LinearIndepOn.injOn
  条件: [非平凡 R] (hv : LinearIndepOn R v s)
  结论: 单射限制 v s
  证明: injOn_iff_injective.2 LinearIndependent.injective hv

Depends on / 依赖: LinearIndependent, LinearIndependent.injective, injOn_iff_injective, injective
-/
theorem LinearIndepOn.injOn [Nontrivial R] (hv : LinearIndepOn R v s) : InjOn v s :=
injOn_iff_injective.2 LinearIndependent.injective hv

/--
theorem `LinearIndependent.smul_left_injective` / 定理 `LinearIndependent.smul_left_injective`

English:
theorem LinearIndependent.smul_left_injective
  given: (hv : LinearIndependent R v) (i : ι)
  proof: by convert! hv.comp (Finsupp.single_injective i); simp

中文:
定理 LinearIndependent.smul_left_injective
  条件: (hv : LinearIndependent R v) (i : ι)
  证明: by convert! hv.comp (Finsupp.single_injective i); simp

Depends on / 依赖: Finsupp, Finsupp.single_injective, convert, hv.comp, single_injective
-/
theorem LinearIndependent.smul_left_injective (hv : LinearIndependent R v) (i : ι) :
    Injective fun r : R => r • v i := by convert! hv.comp (Finsupp.single_injective i); simp

/--
theorem `LinearIndependent.ne_zero` / 定理 `LinearIndependent.ne_zero`

English:
theorem LinearIndependent.ne_zero
  given: [Nontrivial R] (i : ι) (hv : LinearIndependent R v)
  proof: by
  intro h
  have := @hv (Finsupp.single i 1 : ι ->₀ R) 0 (by simpa using h)
  simp at this

中文:
定理 LinearIndependent.ne_zero
  条件: [非平凡 R] (i : ι) (hv : LinearIndependent R v)
  证明: by
  intro h
  have := @hv (Finsupp.single i 1 : ι ->₀ R) 0 (by simpa using h)
  simp at this

Depends on / 依赖: Finsupp, Finsupp.single, single
-/
theorem LinearIndependent.ne_zero [Nontrivial R] (i : ι) (hv : LinearIndependent R v) :
    v i != 0 := by
  intro h
  have := @hv (Finsupp.single i 1 : ι ->₀ R) 0 (by simpa using h)
  simp at this

/--
theorem `LinearIndepOn.ne_zero` / 定理 `LinearIndepOn.ne_zero`

English:
theorem LinearIndepOn.ne_zero
  given: [Nontrivial R] {i : ι} (hv : LinearIndepOn R v s) (hi : i in s)
  proof: LinearIndependent.ne_zero ⟨i, hi⟩ hv

中文:
定理 LinearIndepOn.ne_zero
  条件: [非平凡 R] {i : ι} (hv : LinearIndepOn R v s) (hi : i in s)
  证明: LinearIndependent.ne_zero ⟨i, hi⟩ hv

Depends on / 依赖: LinearIndependent, LinearIndependent.ne_zero, ne_zero
-/
theorem LinearIndepOn.ne_zero [Nontrivial R] {i : ι} (hv : LinearIndepOn R v s) (hi : i in s) :
    v i != 0 :=
  LinearIndependent.ne_zero ⟨i, hi⟩ hv

/--
theorem `LinearIndepOn.zero_notMem_image` / 定理 `LinearIndepOn.zero_notMem_image`

English:
theorem LinearIndepOn.zero_notMem_image
  given: [Nontrivial R] (hs : LinearIndepOn R v s)
  statement: 0 ∉ v '' s
  proof: fun ⟨_, hi, h0⟩ => hs.ne_zero hi h0

中文:
定理 LinearIndepOn.zero_notMem_image
  条件: [非平凡 R] (hs : LinearIndepOn R v s)
  结论: 0 ∉ v '' s
  证明: fun ⟨_, hi, h0⟩ => hs.ne_zero hi h0

Depends on / 依赖: hs.ne_zero, ne_zero
-/
theorem LinearIndepOn.zero_notMem_image [Nontrivial R] (hs : LinearIndepOn R v s) : 0 ∉ v '' s :=
  fun ⟨_, hi, h0⟩ => hs.ne_zero hi h0

/--
theorem `linearIndependent_empty_type` / 定理 `linearIndependent_empty_type`

English:
theorem linearIndependent_empty_type
  given: [IsEmpty ι]
  statement: LinearIndependent R v
  proof: injective_of_subsingleton _

@[simp]

中文:
定理 linearIndependent_empty_type
  条件: [是空 ι]
  结论: LinearIndependent R v
  证明: injective_of_subsingleton _

@[simp]

Depends on / 依赖: injective_of_subsingleton
-/
theorem linearIndependent_empty_type [IsEmpty ι] : LinearIndependent R v :=
  injective_of_subsingleton _

@[simp]
/--
theorem `linearIndependent_zero_iff` / 定理 `linearIndependent_zero_iff`

English:
theorem linearIndependent_zero_iff
  given: [Nontrivial R]
  statement: LinearIndependent R (0 : ι -> M) ↔ IsEmpty ι
  proof: ⟨fun h => not_nonempty_iff.1 fun ⟨i⟩ => (h.ne_zero i rfl).elim,
    fun _ => linearIndependent_empty_type⟩

@[simp]

中文:
定理 linearIndependent_zero_iff
  条件: [非平凡 R]
  结论: LinearIndependent R (0 : ι -> M) ↔ 是空 ι
  证明: ⟨fun h => not_nonempty_iff.1 fun ⟨i⟩ => (h.ne_zero i rfl).elim,
    fun _ => linearIndependent_empty_type⟩

@[simp]

Depends on / 依赖: h.ne_zero, linearIndependent_empty_type, ne_zero, not_nonempty_iff
-/
theorem linearIndependent_zero_iff [Nontrivial R] : LinearIndependent R (0 : ι -> M) ↔ IsEmpty ι :=
  ⟨fun h => not_nonempty_iff.1 fun ⟨i⟩ => (h.ne_zero i rfl).elim,
    fun _ => linearIndependent_empty_type⟩

@[simp]
/--
theorem `linearIndepOn_zero_iff` / 定理 `linearIndepOn_zero_iff`

English:
theorem linearIndepOn_zero_iff
  given: [Nontrivial R]
  statement: LinearIndepOn R (0 : ι -> M) s ↔ s = ∅
  proof: linearIndependent_zero_iff.trans isEmpty_coe_sort

@[simp]

中文:
定理 linearIndepOn_zero_iff
  条件: [非平凡 R]
  结论: LinearIndepOn R (0 : ι -> M) s ↔ s = ∅
  证明: linearIndependent_zero_iff.trans isEmpty_coe_sort

@[simp]

Depends on / 依赖: isEmpty_coe_sort, linearIndependent_zero_iff, linearIndependent_zero_iff.trans
-/
theorem linearIndepOn_zero_iff [Nontrivial R] : LinearIndepOn R (0 : ι -> M) s ↔ s = ∅ :=
  linearIndependent_zero_iff.trans isEmpty_coe_sort

@[simp]
/--
theorem `linearIndependent_subsingleton_iff` / 定理 `linearIndependent_subsingleton_iff`

English:
theorem linearIndependent_subsingleton_iff
  given: [Nontrivial R] [Subsingleton M] (f : ι -> M)
  proof: by
  rw [Subsingleton.elim f 0]; rw [linearIndependent_zero_iff]

中文:
定理 linearIndependent_subsingleton_iff
  条件: [非平凡 R] [子单例 M] (f : ι -> M)
  证明: by
  rw [Subsingleton.elim f 0]; rw [linearIndependent_zero_iff]

Depends on / 依赖: Subsingleton, Subsingleton.elim, linearIndependent_zero_iff
-/
theorem linearIndependent_subsingleton_iff [Nontrivial R] [Subsingleton M] (f : ι -> M) :
    LinearIndependent R f ↔ IsEmpty ι := by
  rw [Subsingleton.elim f 0]; rw [linearIndependent_zero_iff]

variable (R M) in
/--
theorem `linearIndependent_empty` / 定理 `linearIndependent_empty`

English:
theorem linearIndependent_empty
  statement: LinearIndependent R (fun x => x : (∅ : Set M) -> M)
  proof: linearIndependent_empty_type

中文:
定理 linearIndependent_empty
  结论: LinearIndependent R (fun x => x : (∅ : 集合 M) -> M)
  证明: linearIndependent_empty_type

Depends on / 依赖: linearIndependent_empty_type
-/
theorem linearIndependent_empty : LinearIndependent R (fun x => x : (∅ : Set M) -> M) :=
  linearIndependent_empty_type

variable (R v) in
@[simp]
/--
theorem `linearIndepOn_empty` / 定理 `linearIndepOn_empty`

English:
theorem linearIndepOn_empty
  statement: LinearIndepOn R v ∅
  proof: linearIndependent_empty_type ..

中文:
定理 linearIndepOn_empty
  结论: LinearIndepOn R v ∅
  证明: linearIndependent_empty_type ..

Depends on / 依赖: linearIndependent_empty_type
-/
theorem linearIndepOn_empty : LinearIndepOn R v ∅ :=
  linearIndependent_empty_type ..

/--
theorem `linearIndependent_set_coe_iff` / 定理 `linearIndependent_set_coe_iff`

English:
theorem linearIndependent_set_coe_iff
  proof: Iff.rfl

中文:
定理 linearIndependent_set_coe_iff
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem linearIndependent_set_coe_iff :
    LinearIndependent R (fun x : s => v x) ↔ LinearIndepOn R v s := Iff.rfl

/--
theorem `linearIndependent_subtype_iff` / 定理 `linearIndependent_subtype_iff`

English:
theorem linearIndependent_subtype_iff
  given: {s : Set M}
  proof: Iff.rfl

中文:
定理 linearIndependent_subtype_iff
  条件: {s : 集合 M}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem linearIndependent_subtype_iff {s : Set M} :
    LinearIndependent R (Subtype.val : s -> M) ↔ LinearIndepOn R id s := Iff.rfl

/--
theorem `linearIndependent_comp_subtype_iff` / 定理 `linearIndependent_comp_subtype_iff`

English:
theorem linearIndependent_comp_subtype_iff
  proof: Iff.rfl

中文:
定理 linearIndependent_comp_subtype_iff
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem linearIndependent_comp_subtype_iff :
    LinearIndependent R (v ∘ Subtype.val : s -> M) ↔ LinearIndepOn R v s := Iff.rfl

/--
theorem `LinearIndependent.comp` / 定理 `LinearIndependent.comp`

English:
theorem LinearIndependent.comp
  given: (h : LinearIndependent R v) (f : ι' -> ι) (hf : Injective f)
  proof: by
  simpa [comp_def] using! Injective.comp h (Finsupp.mapDomain_injective hf)

中文:
定理 LinearIndependent.comp
  条件: (h : LinearIndependent R v) (f : ι' -> ι) (hf : 单射 f)
  证明: by
  simpa [comp_def] using! Injective.comp h (Finsupp.mapDomain_injective hf)

Depends on / 依赖: Finsupp, Finsupp.mapDomain_injective, Injective, Injective.comp, comp_def, mapDomain_injective
-/
theorem LinearIndependent.comp (h : LinearIndependent R v) (f : ι' -> ι) (hf : Injective f) :
    LinearIndependent R (v ∘ f) := by
  simpa [comp_def] using! Injective.comp h (Finsupp.mapDomain_injective hf)

/--
lemma `LinearIndepOn.mono` / 引理 `LinearIndepOn.mono`

English:
lemma LinearIndepOn.mono
  given: {t s : Set ι} (hs : LinearIndepOn R v s) (h : t subseteq s)
  proof: hs.comp _ Set.inclusion_injective h

中文:
引理 LinearIndepOn.mono
  条件: {t s : 集合 ι} (hs : LinearIndepOn R v s) (h : t subseteq s)
  证明: hs.comp _ Set.inclusion_injective h

Depends on / 依赖: Set.inclusion_injective, hs.comp, inclusion_injective
-/
lemma LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn R v s) (h : t subseteq s) :
LinearIndepOn R v t := hs.comp _ Set.inclusion_injective h

-- This version makes `l₁` and `l₂` explicit.
/--
theorem `linearIndependent_iffₛ` / 定理 `linearIndependent_iffₛ`

English:
theorem linearIndependent_iffₛ
  proof: Iff.rfl

中文:
定理 linearIndependent_iffₛ
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem linearIndependent_iffₛ :
    LinearIndependent R v ↔
      forall l₁ l₂, Finsupp.linearCombination R v l₁ = Finsupp.linearCombination R v l₂ -> l₁ = l₂ :=
  Iff.rfl

open Finset in
/--
theorem `linearIndependent_iff'ₛ` / 定理 `linearIndependent_iff'ₛ`

English:
theorem linearIndependent_iff'ₛ
  proof: linearIndependent_iffₛ.trans
    ⟨fun hv s f g eq i his => by
      have h :=
hv (∑ i in s, Finsupp.single i (f i)) (∑ i in s, Finsupp.single i (g i)) by
          simpa only [map_sum, Finsupp.linearCombination_single] using eq
      have (f : ι -> R) : f i = (∑ j in s, Finsupp.single j (f j)) i :=
        calc
          f i = (Finsupp.lapply i : (ι ->₀ R) ->ₗ[R] R) (Finsupp.single i (f i)) := by
            { rw [Finsupp.lapply_apply, Finsupp.single_eq_same] }
          _ = ∑ j in s, (Finsupp.lapply i : (ι ->₀ R) ->ₗ[R] R) (Finsupp.single j (f j)) :=
Eq.symm
              Finset.sum_eq_single i
                (fun j _hjs hji => by rw [Finsupp.lapply_apply, Finsupp.single_eq_of_ne' hji])
                fun hnis => hnis.elim his
          _ = (∑ j in s, Finsupp.single j (f j)) i := (map_sum ..).symm
      rw [this f]; rw [this g]; rw [h],
      fun hv f g hl =>
      Finsupp.ext fun _ => by
        classical
refine _root_.by_contradiction fun hni => hni hv (f.support union g.support) f g ?_ _ ?_
        · rwa [← sum_subset subset_union_left, ← sum_subset subset_union_right] <;>
            rintro i - hi <;> rw [Finsupp.notMem_support_iff.mp hi, zero_smul]
        · contrapose hni
          simp_rw [notMem_union, Finsupp.notMem_support_iff] at hni
          rw [hni.1]; rw [hni.2]⟩

中文:
定理 linearIndependent_iff'ₛ
  证明: linearIndependent_iffₛ.trans
    ⟨fun hv s f g eq i his => by
      have h :=
hv (∑ i in s, Finsupp.single i (f i)) (∑ i in s, Finsupp.single i (g i)) by
          simpa only [map_sum, Finsupp.linearCombination_single] using eq
      have (f : ι -> R) : f i = (∑ j in s, Finsupp.single j (f j)) i :=
        calc
          f i = (Finsupp.lapply i : (ι ->₀ R) ->ₗ[R] R) (Finsupp.single i (f i)) := by
            { rw [Finsupp.lapply_apply, Finsupp.single_eq_same] }
          _ = ∑ j in s, (Finsupp.lapply i : (ι ->₀ R) ->ₗ[R] R) (Finsupp.single j (f j)) :=
Eq.symm
              Finset.sum_eq_single i
                (fun j _hjs hji => by rw [Finsupp.lapply_apply, Finsupp.single_eq_of_ne' hji])
                fun hnis => hnis.elim his
          _ = (∑ j in s, Finsupp.single j (f j)) i := (map_sum ..).symm
      rw [this f]; rw [this g]; rw [h],
      fun hv f g hl =>
      Finsupp.ext fun _ => by
        classical
refine _root_.by_contradiction fun hni => hni hv (f.support union g.support) f g ?_ _ ?_
        · rwa [← sum_subset subset_union_left, ← sum_subset subset_union_right] <;>
            rintro i - hi <;> rw [Finsupp.notMem_support_iff.mp hi, zero_smul]
        · contrapose hni
          simp_rw [notMem_union, Finsupp.notMem_support_iff] at hni
          rw [hni.1]; rw [hni.2]⟩

Depends on / 依赖: Eq.symm, Finsupp, Finsupp.lapply, Finsupp.lapply_apply, Finsupp.linearCombination_single, Finsupp.single, Finsupp.single_eq_same, lapply, lapply_apply, linearCombination_single, map_sum, single, single_eq_same
-/
theorem linearIndependent_iff'ₛ :
    LinearIndependent R v ↔
      forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i • v i -> forall i in s, f i = g i :=
  linearIndependent_iffₛ.trans
    ⟨fun hv s f g eq i his => by
      have h :=
hv (∑ i in s, Finsupp.single i (f i)) (∑ i in s, Finsupp.single i (g i)) by
          simpa only [map_sum, Finsupp.linearCombination_single] using eq
      have (f : ι -> R) : f i = (∑ j in s, Finsupp.single j (f j)) i :=
        calc
          f i = (Finsupp.lapply i : (ι ->₀ R) ->ₗ[R] R) (Finsupp.single i (f i)) := by
            { rw [Finsupp.lapply_apply, Finsupp.single_eq_same] }
          _ = ∑ j in s, (Finsupp.lapply i : (ι ->₀ R) ->ₗ[R] R) (Finsupp.single j (f j)) :=
Eq.symm
              Finset.sum_eq_single i
                (fun j _hjs hji => by rw [Finsupp.lapply_apply, Finsupp.single_eq_of_ne' hji])
                fun hnis => hnis.elim his
          _ = (∑ j in s, Finsupp.single j (f j)) i := (map_sum ..).symm
      rw [this f]; rw [this g]; rw [h],
      fun hv f g hl =>
      Finsupp.ext fun _ => by
        classical
refine _root_.by_contradiction fun hni => hni hv (f.support union g.support) f g ?_ _ ?_
        · rwa [← sum_subset subset_union_left, ← sum_subset subset_union_right] <;>
            rintro i - hi <;> rw [Finsupp.notMem_support_iff.mp hi, zero_smul]
        · contrapose hni
          simp_rw [notMem_union, Finsupp.notMem_support_iff] at hni
          rw [hni.1]; rw [hni.2]⟩

/--
theorem `linearIndependent_iff''ₛ` / 定理 `linearIndependent_iff''ₛ`

English:
theorem linearIndependent_iff''ₛ
  proof: by
  classical
  exact linearIndependent_iff'ₛ.trans
    ⟨fun H s f g eq hv i => if his : i in s then H s f g hv i his else eq i his,
      fun H s f g eq i hi => by
      convert!
        H s (fun j => if j in s then f j else 0) (fun j => if j in s then g j else 0)
          (fun j hj => (if_neg hj).trans (if_neg hj).symm)
          (by simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, eq]) i <;>
      exact (if_pos hi).symm⟩

中文:
定理 linearIndependent_iff''ₛ
  证明: by
  classical
  exact linearIndependent_iff'ₛ.trans
    ⟨fun H s f g eq hv i => if his : i in s then H s f g hv i his else eq i his,
      fun H s f g eq i hi => by
      convert!
        H s (fun j => if j in s then f j else 0) (fun j => if j in s then g j else 0)
          (fun j hj => (if_neg hj).trans (if_neg hj).symm)
          (by simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, eq]) i <;>
      exact (if_pos hi).symm⟩

Depends on / 依赖: Finset, Finset.sum_extend_by_zero, classical, convert, if_neg, if_pos, ite_smul, linearIndependent_iff, simp_rw, sum_extend_by_zero, zero_smul
-/
theorem linearIndependent_iff''ₛ :
    LinearIndependent R v ↔
      forall (s : Finset ι) (f g : ι -> R), (forall i ∉ s, f i = g i) ->
        ∑ i in s, f i • v i = ∑ i in s, g i • v i -> forall i, f i = g i := by
  classical
  exact linearIndependent_iff'ₛ.trans
    ⟨fun H s f g eq hv i => if his : i in s then H s f g hv i his else eq i his,
      fun H s f g eq i hi => by
      convert!
        H s (fun j => if j in s then f j else 0) (fun j => if j in s then g j else 0)
          (fun j hj => (if_neg hj).trans (if_neg hj).symm)
          (by simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, eq]) i <;>
      exact (if_pos hi).symm⟩

/--
theorem `not_linearIndependent_iffₛ` / 定理 `not_linearIndependent_iffₛ`

English:
theorem not_linearIndependent_iffₛ
  proof: by
  rw [linearIndependent_iff'ₛ]
  simp only [exists_prop, not_forall]

中文:
定理 not_linearIndependent_iffₛ
  证明: by
  rw [linearIndependent_iff'ₛ]
  simp only [exists_prop, not_forall]

Depends on / 依赖: exists_prop, linearIndependent_iff, not_forall
-/
theorem not_linearIndependent_iffₛ :
    ¬LinearIndependent R v ↔ exists s : Finset ι,
      exists f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i • v i ∧ exists i in s, f i != g i := by
  rw [linearIndependent_iff'ₛ]
  simp only [exists_prop, not_forall]

/--
theorem `Fintype.linearIndependent_iffₛ` / 定理 `Fintype.linearIndependent_iffₛ`

English:
theorem Fintype.linearIndependent_iffₛ
  given: [Fintype ι]
  proof: by
  simp_rw [linearIndependent_iff_injective_fintypeLinearCombination,
    Injective, Fintype.linearCombination_apply, funext_iff]

中文:
定理 有限类型.linearIndependent_iffₛ
  条件: [有限类型 ι]
  证明: by
  simp_rw [linearIndependent_iff_injective_fintypeLinearCombination,
    Injective, Fintype.linearCombination_apply, funext_iff]

Depends on / 依赖: Fintype, Fintype.linearCombination_apply, Injective, funext_iff, linearCombination_apply, linearIndependent_iff_injective_fintypeLinearCombination, simp_rw
-/
theorem Fintype.linearIndependent_iffₛ [Fintype ι] :
    LinearIndependent R v ↔ forall f g : ι -> R, ∑ i, f i • v i = ∑ i, g i • v i -> forall i, f i = g i := by
  simp_rw [linearIndependent_iff_injective_fintypeLinearCombination,
    Injective, Fintype.linearCombination_apply, funext_iff]

/--
theorem `Fintype.not_linearIndependent_iffₛ` / 定理 `Fintype.not_linearIndependent_iffₛ`

English:
theorem Fintype.not_linearIndependent_iffₛ
  given: [Fintype ι]
  proof: by
  simpa using not_iff_not.2 Fintype.linearIndependent_iffₛ

中文:
定理 有限类型.not_linearIndependent_iffₛ
  条件: [有限类型 ι]
  证明: by
  simpa using not_iff_not.2 Fintype.linearIndependent_iffₛ

Depends on / 依赖: Fintype, Fintype.linearIndependent_iff, not_iff_not
-/
theorem Fintype.not_linearIndependent_iffₛ [Fintype ι] :
    ¬LinearIndependent R v ↔ exists f g : ι -> R, ∑ i, f i • v i = ∑ i, g i • v i ∧ exists i, f i != g i := by
  simpa using not_iff_not.2 Fintype.linearIndependent_iffₛ

/--
lemma `linearIndepOn_finset_iffₛ` / 引理 `linearIndepOn_finset_iffₛ`

English:
lemma linearIndepOn_finset_iffₛ
  given: {s : Finset ι}
  proof: by
  classical
  simp_rw [LinearIndepOn, Fintype.linearIndependent_iffₛ]
  constructor
  · rintro hv f g hfg i hi
    simp_rw [← s.sum_attach] at hfg
    exact hv (f ∘ Subtype.val) (g ∘ Subtype.val) hfg ⟨i, hi⟩
  · rintro hv f g hfg i
    simpa using hv (fun j => if hj : j in s then f ⟨j, hj⟩ else 0)
      (fun j => if hj : j in s then g ⟨j, hj⟩ else 0) (by simpa +contextual [← s.sum_attach]) i

中文:
引理 linearIndepOn_finset_iffₛ
  条件: {s : 有限集 ι}
  证明: by
  classical
  simp_rw [LinearIndepOn, Fintype.linearIndependent_iffₛ]
  constructor
  · rintro hv f g hfg i hi
    simp_rw [← s.sum_attach] at hfg
    exact hv (f ∘ Subtype.val) (g ∘ Subtype.val) hfg ⟨i, hi⟩
  · rintro hv f g hfg i
    simpa using hv (fun j => if hj : j in s then f ⟨j, hj⟩ else 0)
      (fun j => if hj : j in s then g ⟨j, hj⟩ else 0) (by simpa +contextual [← s.sum_attach]) i

Depends on / 依赖: Fintype, Fintype.linearIndependent_iff, LinearIndepOn, Subtype, Subtype.val, classical, contextual, s.sum_attach, simp_rw, sum_attach
-/
lemma linearIndepOn_finset_iffₛ {s : Finset ι} :
    LinearIndepOn R v s ↔ forall f g : ι -> R,
      ∑ i in s, f i • v i = ∑ i in s, g i • v i -> forall i in s, f i = g i := by
  classical
  simp_rw [LinearIndepOn, Fintype.linearIndependent_iffₛ]
  constructor
  · rintro hv f g hfg i hi
    simp_rw [← s.sum_attach] at hfg
    exact hv (f ∘ Subtype.val) (g ∘ Subtype.val) hfg ⟨i, hi⟩
  · rintro hv f g hfg i
    simpa using hv (fun j => if hj : j in s then f ⟨j, hj⟩ else 0)
      (fun j => if hj : j in s then g ⟨j, hj⟩ else 0) (by simpa +contextual [← s.sum_attach]) i

/--
lemma `not_linearIndepOn_finset_iffₛ` / 引理 `not_linearIndepOn_finset_iffₛ`

English:
lemma not_linearIndepOn_finset_iffₛ
  given: {s : Finset ι}
  proof: by
  simpa using linearIndepOn_finset_iffₛ.not

中文:
引理 not_linearIndepOn_finset_iffₛ
  条件: {s : 有限集 ι}
  证明: by
  simpa using linearIndepOn_finset_iffₛ.not
-/
lemma not_linearIndepOn_finset_iffₛ {s : Finset ι} :
    ¬LinearIndepOn R v s ↔ exists f g : ι -> R,
      ∑ i in s, f i • v i = ∑ i in s, g i • v i ∧ exists i in s, f i != g i := by
  simpa using linearIndepOn_finset_iffₛ.not

/--
theorem `linearIndependent_iff_finset_linearIndependent` / 定理 `linearIndependent_iff_finset_linearIndependent`

English:
theorem linearIndependent_iff_finset_linearIndependent
  proof: ⟨fun H _ => H.comp _ Subtype.val_injective, fun H => linearIndependent_iff'ₛ.2 fun s f g eq i hi =>
    Fintype.linearIndependent_iffₛ.1 (H s) (f ∘ Subtype.val) (g ∘ Subtype.val)
      (by simpa only [← s.sum_coe_sort] using! eq) ⟨i, hi⟩⟩

中文:
定理 linearIndependent_iff_finset_linearIndependent
  证明: ⟨fun H _ => H.comp _ Subtype.val_injective, fun H => linearIndependent_iff'ₛ.2 fun s f g eq i hi =>
    Fintype.linearIndependent_iffₛ.1 (H s) (f ∘ Subtype.val) (g ∘ Subtype.val)
      (by simpa only [← s.sum_coe_sort] using! eq) ⟨i, hi⟩⟩

Depends on / 依赖: Fintype, Fintype.linearIndependent_iff, H.comp, Subtype, Subtype.val, Subtype.val_injective, linearIndependent_iff, s.sum_coe_sort, sum_coe_sort, val_injective
-/
theorem linearIndependent_iff_finset_linearIndependent :
    LinearIndependent R v ↔ forall (s : Finset ι), LinearIndependent R (v ∘ (Subtype.val : s -> ι)) :=
  ⟨fun H _ => H.comp _ Subtype.val_injective, fun H => linearIndependent_iff'ₛ.2 fun s f g eq i hi =>
    Fintype.linearIndependent_iffₛ.1 (H s) (f ∘ Subtype.val) (g ∘ Subtype.val)
      (by simpa only [← s.sum_coe_sort] using! eq) ⟨i, hi⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `linearIndepOn_iff_linearIndepOn_finset` / 引理 `linearIndepOn_iff_linearIndepOn_finset`

English:
lemma linearIndepOn_iff_linearIndepOn_finset
  proof: hv.mono hts
  mpr hv := by
    rw [LinearIndepOn]; rw [linearIndependent_iff_finset_linearIndependent]
    exact fun t => (hv (t.map <| .subtype _) (by simp)).comp (ι' := t)
      (fun x => ⟨x, Finset.mem_map_of_mem (.subtype _) x.2⟩) fun x => by aesop

中文:
引理 linearIndepOn_iff_linearIndepOn_finset
  证明: hv.mono hts
  mpr hv := by
    rw [LinearIndepOn]; rw [linearIndependent_iff_finset_linearIndependent]
    exact fun t => (hv (t.map <| .subtype _) (by simp)).comp (ι' := t)
      (fun x => ⟨x, Finset.mem_map_of_mem (.subtype _) x.2⟩) fun x => by aesop

Depends on / 依赖: hv.mono
-/
lemma linearIndepOn_iff_linearIndepOn_finset :
    LinearIndepOn R v s ↔ forall t : Finset ι, ↑t subseteq s -> LinearIndepOn R v t where
  mp hv t hts := hv.mono hts
  mpr hv := by
    rw [LinearIndepOn]; rw [linearIndependent_iff_finset_linearIndependent]
    exact fun t => (hv (t.map <| .subtype _) (by simp)).comp (ι' := t)
      (fun x => ⟨x, Finset.mem_map_of_mem (.subtype _) x.2⟩) fun x => by aesop

/--
theorem `LinearIndependent.of_comp` / 定理 `LinearIndependent.of_comp`

English:
theorem LinearIndependent.of_comp
  given: (f : M ->ₗ[R] M') (hfv : LinearIndependent R (f ∘ v))
  proof: by
  rw [LinearIndependent]; rw [Finsupp.linearCombination_linear_comp]; rw [LinearMap.coe_comp] at hfv
  exact hfv.of_comp

中文:
定理 LinearIndependent.of_comp
  条件: (f : M ->ₗ[R] M') (hfv : LinearIndependent R (f ∘ v))
  证明: by
  rw [LinearIndependent]; rw [Finsupp.linearCombination_linear_comp]; rw [LinearMap.coe_comp] at hfv
  exact hfv.of_comp

Depends on / 依赖: Finsupp, Finsupp.linearCombination_linear_comp, LinearIndependent, LinearMap, LinearMap.coe_comp, coe_comp, hfv.of_comp, linearCombination_linear_comp, of_comp
-/
theorem LinearIndependent.of_comp (f : M ->ₗ[R] M') (hfv : LinearIndependent R (f ∘ v)) :
    LinearIndependent R v := by
  rw [LinearIndependent]; rw [Finsupp.linearCombination_linear_comp]; rw [LinearMap.coe_comp] at hfv
  exact hfv.of_comp

/--
theorem `LinearIndepOn.of_comp` / 定理 `LinearIndepOn.of_comp`

English:
theorem LinearIndepOn.of_comp
  given: (f : M ->ₗ[R] M') (hfv : LinearIndepOn R (f ∘ v) s)
  proof: LinearIndependent.of_comp f hfv

中文:
定理 LinearIndepOn.of_comp
  条件: (f : M ->ₗ[R] M') (hfv : LinearIndepOn R (f ∘ v) s)
  证明: LinearIndependent.of_comp f hfv

Depends on / 依赖: LinearIndependent, LinearIndependent.of_comp, of_comp
-/
theorem LinearIndepOn.of_comp (f : M ->ₗ[R] M') (hfv : LinearIndepOn R (f ∘ v) s) :
    LinearIndepOn R v s :=
  LinearIndependent.of_comp f hfv

/--
lemma `LinearIndependent.of_linearIndependent_subset` / 引理 `LinearIndependent.of_linearIndependent_subset`

English:
lemma LinearIndependent.of_linearIndependent_subset
  statement: (s : Set ι') {v : ι -> ι' -> R}
  proof: hv.of_comp ⟨⟨s.domRestrict, fun _ _ => rfl⟩, fun _ _ => rfl⟩

中文:
引理 LinearIndependent.of_linearIndependent_subset
  结论: (s : 集合 ι') {v : ι -> ι' -> R}
  证明: hv.of_comp ⟨⟨s.domRestrict, fun _ _ => rfl⟩, fun _ _ => rfl⟩

Depends on / 依赖: domRestrict, hv.of_comp, of_comp, s.domRestrict
-/
lemma LinearIndependent.of_linearIndependent_subset (s : Set ι') {v : ι -> ι' -> R}
    (hv : LinearIndependent R fun (i : ι) (j : s) => v i j) :
    LinearIndependent R v :=
  hv.of_comp ⟨⟨s.domRestrict, fun _ _ => rfl⟩, fun _ _ => rfl⟩

/--
theorem `LinearMap.linearIndependent_iff_of_injOn` / 定理 `LinearMap.linearIndependent_iff_of_injOn`

English:
theorem LinearMap.linearIndependent_iff_of_injOn
  statement: (f : M ->ₗ[R] M')
  proof: by
  simp_rw [LinearIndependent, Finsupp.linearCombination_linear_comp, coe_comp]
  rw [hf_inj.injective_iff]
  rw [← Finsupp.range_linearCombination]; rw [LinearMap.coe_range]

中文:
定理 线性映射.linearIndependent_iff_of_injOn
  结论: (f : M ->ₗ[R] M')
  证明: by
  simp_rw [LinearIndependent, Finsupp.linearCombination_linear_comp, coe_comp]
  rw [hf_inj.injective_iff]
  rw [← Finsupp.range_linearCombination]; rw [LinearMap.coe_range]
-/
protected theorem LinearMap.linearIndependent_iff_of_injOn (f : M ->ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (Set.range v))) :
    LinearIndependent R (f ∘ v) ↔ LinearIndependent R v := by
  simp_rw [LinearIndependent, Finsupp.linearCombination_linear_comp, coe_comp]
  rw [hf_inj.injective_iff]
  rw [← Finsupp.range_linearCombination]; rw [LinearMap.coe_range]

/--
theorem `LinearMap.linearIndepOn_iff_of_injOn` / 定理 `LinearMap.linearIndepOn_iff_of_injOn`

English:
theorem LinearMap.linearIndepOn_iff_of_injOn
  statement: (f : M ->ₗ[R] M')
  proof: f.linearIndependent_iff_of_injOn (by rwa [← image_eq_range]) (v := fun i : s => v i)

中文:
定理 线性映射.linearIndepOn_iff_of_injOn
  结论: (f : M ->ₗ[R] M')
  证明: f.linearIndependent_iff_of_injOn (by rwa [← image_eq_range]) (v := fun i : s => v i)
-/
protected theorem LinearMap.linearIndepOn_iff_of_injOn (f : M ->ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (v '' s))) :
    LinearIndepOn R (f ∘ v) s ↔ LinearIndepOn R v s :=
  f.linearIndependent_iff_of_injOn (by rwa [← image_eq_range]) (v := fun i : s => v i)

-- TODO : Rename this `LinearIndependent.of_subsingleton`.
@[nontriviality]
/--
theorem `linearIndependent_of_subsingleton` / 定理 `linearIndependent_of_subsingleton`

English:
theorem linearIndependent_of_subsingleton
  given: [Subsingleton R]
  statement: LinearIndependent R v
  proof: linearIndependent_iffₛ.2 fun _l _l' _hl => Subsingleton.elim _ _

@[nontriviality]

中文:
定理 linearIndependent_of_subsingleton
  条件: [子单例 R]
  结论: LinearIndependent R v
  证明: linearIndependent_iffₛ.2 fun _l _l' _hl => Subsingleton.elim _ _

@[nontriviality]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem linearIndependent_of_subsingleton [Subsingleton R] : LinearIndependent R v :=
  linearIndependent_iffₛ.2 fun _l _l' _hl => Subsingleton.elim _ _

@[nontriviality]
/--
theorem `LinearIndepOn.of_subsingleton` / 定理 `LinearIndepOn.of_subsingleton`

English:
theorem LinearIndepOn.of_subsingleton
  given: [Subsingleton R]
  statement: LinearIndepOn R v s
  proof: linearIndependent_of_subsingleton

中文:
定理 LinearIndepOn.of_subsingleton
  条件: [子单例 R]
  结论: LinearIndepOn R v s
  证明: linearIndependent_of_subsingleton

Depends on / 依赖: linearIndependent_of_subsingleton
-/
theorem LinearIndepOn.of_subsingleton [Subsingleton R] : LinearIndepOn R v s :=
  linearIndependent_of_subsingleton

/--
theorem `linearIndependent_equiv` / 定理 `linearIndependent_equiv`

English:
theorem linearIndependent_equiv
  given: (e : ι ≃ ι') {f : ι' -> M}
  proof: ⟨fun h => comp_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective,
    fun h => h.comp _ e.injective⟩

中文:
定理 linearIndependent_equiv
  条件: (e : ι ≃ ι') {f : ι' -> M}
  证明: ⟨fun h => comp_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective,
    fun h => h.comp _ e.injective⟩

Depends on / 依赖: comp_id, e.injective, e.self_comp_symm, e.symm.injective, h.comp, injective, self_comp_symm
-/
theorem linearIndependent_equiv (e : ι ≃ ι') {f : ι' -> M} :
    LinearIndependent R (f ∘ e) ↔ LinearIndependent R f :=
  ⟨fun h => comp_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective,
    fun h => h.comp _ e.injective⟩

/--
theorem `linearIndependent_equiv'` / 定理 `linearIndependent_equiv'`

English:
theorem linearIndependent_equiv'
  given: (e : ι ≃ ι') {f : ι' -> M} {g : ι -> M} (h : f ∘ e = g)
  proof: h ▸ linearIndependent_equiv e

中文:
定理 linearIndependent_equiv'
  条件: (e : ι ≃ ι') {f : ι' -> M} {g : ι -> M} (h : f ∘ e = g)
  证明: h ▸ linearIndependent_equiv e

Depends on / 依赖: linearIndependent_equiv
-/
theorem linearIndependent_equiv' (e : ι ≃ ι') {f : ι' -> M} {g : ι -> M} (h : f ∘ e = g) :
    LinearIndependent R g ↔ LinearIndependent R f :=
  h ▸ linearIndependent_equiv e

/--
theorem `linearIndepOn_equiv` / 定理 `linearIndepOn_equiv`

English:
theorem linearIndepOn_equiv
  given: (e : ι ≃ ι') {f : ι' -> M} {s : Set ι}
  proof: linearIndependent_equiv' (e.image s) by simp [funext_iff]

@[simp]

中文:
定理 linearIndepOn_equiv
  条件: (e : ι ≃ ι') {f : ι' -> M} {s : 集合 ι}
  证明: linearIndependent_equiv' (e.image s) by simp [funext_iff]

@[simp]

Depends on / 依赖: e.image, funext_iff, linearIndependent_equiv
-/
theorem linearIndepOn_equiv (e : ι ≃ ι') {f : ι' -> M} {s : Set ι} :
    LinearIndepOn R (f ∘ e) s ↔ LinearIndepOn R f (e '' s) :=
linearIndependent_equiv' (e.image s) by simp [funext_iff]

@[simp]
/--
theorem `linearIndepOn_univ_iff` / 定理 `linearIndepOn_univ_iff`

English:
theorem linearIndepOn_univ_iff
  statement: LinearIndepOn R v univ ↔ LinearIndependent R v
  proof: linearIndependent_equiv' (Equiv.Set.univ ι) rfl

@[deprecated (since := "2026-02-24")] alias linearIndepOn_univ := linearIndepOn_univ_iff

alias ⟨_, LinearIndependent.linearIndepOn_univ⟩ := linearIndepOn_univ_iff

中文:
定理 linearIndepOn_univ_iff
  结论: LinearIndepOn R v univ ↔ LinearIndependent R v
  证明: linearIndependent_equiv' (Equiv.Set.univ ι) rfl

@[deprecated (since := "2026-02-24")] alias linearIndepOn_univ := linearIndepOn_univ_iff

alias ⟨_, LinearIndependent.linearIndepOn_univ⟩ := linearIndepOn_univ_iff

Depends on / 依赖: Equiv.Set.univ, linearIndependent_equiv
-/
theorem linearIndepOn_univ_iff : LinearIndepOn R v univ ↔ LinearIndependent R v :=
  linearIndependent_equiv' (Equiv.Set.univ ι) rfl

@[deprecated (since := "2026-02-24")] alias linearIndepOn_univ := linearIndepOn_univ_iff

alias ⟨_, LinearIndependent.linearIndepOn_univ⟩ := linearIndepOn_univ_iff

/--
lemma `LinearIndependent.linearIndepOn` / 引理 `LinearIndependent.linearIndepOn`

English:
lemma LinearIndependent.linearIndepOn
  given: (h : LinearIndependent R v) (s : Set ι)
  proof: h.linearIndepOn_univ.mono s.subset_univ

中文:
引理 LinearIndependent.linearIndepOn
  条件: (h : LinearIndependent R v) (s : 集合 ι)
  证明: h.linearIndepOn_univ.mono s.subset_univ

Depends on / 依赖: h.linearIndepOn_univ.mono, linearIndepOn_univ, s.subset_univ, subset_univ
-/
lemma LinearIndependent.linearIndepOn (h : LinearIndependent R v) (s : Set ι) :
    LinearIndepOn R v s :=
  h.linearIndepOn_univ.mono s.subset_univ

/--
theorem `linearIndepOn_iff_image` / 定理 `linearIndepOn_iff_image`

English:
theorem linearIndepOn_iff_image
  given: {ι} {s : Set ι} {f : ι -> M} (hf : Set.InjOn f s)
  proof: linearIndependent_equiv' (Equiv.Set.imageOfInjOn _ _ hf) rfl

中文:
定理 linearIndepOn_iff_image
  条件: {ι} {s : 集合 ι} {f : ι -> M} (hf : 集合.单射限制 f s)
  证明: linearIndependent_equiv' (Equiv.Set.imageOfInjOn _ _ hf) rfl

Depends on / 依赖: Equiv.Set.imageOfInjOn, imageOfInjOn, linearIndependent_equiv
-/
theorem linearIndepOn_iff_image {ι} {s : Set ι} {f : ι -> M} (hf : Set.InjOn f s) :
    LinearIndepOn R f s ↔ LinearIndepOn R id (f '' s) :=
  linearIndependent_equiv' (Equiv.Set.imageOfInjOn _ _ hf) rfl

/--
theorem `linearIndepOn_range_iff` / 定理 `linearIndepOn_range_iff`

English:
theorem linearIndepOn_range_iff
  given: {ι} {f : ι -> ι'} (hf : Injective f) (g : ι' -> M)
  proof: Iff.symm linearIndependent_equiv' (Equiv.ofInjective f hf) rfl

alias ⟨LinearIndependent.of_linearIndepOn_range, _⟩ := linearIndepOn_range_iff

中文:
定理 linearIndepOn_range_iff
  条件: {ι} {f : ι -> ι'} (hf : 单射 f) (g : ι' -> M)
  证明: Iff.symm linearIndependent_equiv' (Equiv.ofInjective f hf) rfl

alias ⟨LinearIndependent.of_linearIndepOn_range, _⟩ := linearIndepOn_range_iff

Depends on / 依赖: Equiv.ofInjective, Iff.symm, linearIndependent_equiv, ofInjective
-/
theorem linearIndepOn_range_iff {ι} {f : ι -> ι'} (hf : Injective f) (g : ι' -> M) :
    LinearIndepOn R g (range f) ↔ LinearIndependent R (g ∘ f) :=
Iff.symm linearIndependent_equiv' (Equiv.ofInjective f hf) rfl

alias ⟨LinearIndependent.of_linearIndepOn_range, _⟩ := linearIndepOn_range_iff

/--
theorem `linearIndepOn_id_range_iff` / 定理 `linearIndepOn_id_range_iff`

English:
theorem linearIndepOn_id_range_iff
  given: {ι} {f : ι -> M} (hf : Injective f)
  proof: linearIndepOn_range_iff hf id

alias ⟨LinearIndependent.of_linearIndepOn_id_range, _⟩ := linearIndepOn_id_range_iff

中文:
定理 linearIndepOn_id_range_iff
  条件: {ι} {f : ι -> M} (hf : 单射 f)
  证明: linearIndepOn_range_iff hf id

alias ⟨LinearIndependent.of_linearIndepOn_id_range, _⟩ := linearIndepOn_id_range_iff

Depends on / 依赖: linearIndepOn_range_iff
-/
theorem linearIndepOn_id_range_iff {ι} {f : ι -> M} (hf : Injective f) :
    LinearIndepOn R id (range f) ↔ LinearIndependent R f :=
  linearIndepOn_range_iff hf id

alias ⟨LinearIndependent.of_linearIndepOn_id_range, _⟩ := linearIndepOn_id_range_iff

/--
theorem `LinearIndependent.linearIndepOn_id` / 定理 `LinearIndependent.linearIndepOn_id`

English:
theorem LinearIndependent.linearIndepOn_id
  given: (i : LinearIndependent R v)
  proof: by
  simpa using! i.comp _ (rangeSplitting_injective v)

中文:
定理 LinearIndependent.linearIndepOn_id
  条件: (i : LinearIndependent R v)
  证明: by
  simpa using! i.comp _ (rangeSplitting_injective v)

Depends on / 依赖: i.comp, rangeSplitting_injective
-/
theorem LinearIndependent.linearIndepOn_id (i : LinearIndependent R v) :
    LinearIndepOn R id (range v) := by
  simpa using! i.comp _ (rangeSplitting_injective v)

/--
theorem `LinearIndependent.linearIndepOn_id'` / 定理 `LinearIndependent.linearIndepOn_id'`

English:
theorem LinearIndependent.linearIndepOn_id'
  statement: (hv : LinearIndependent R v) {t : Set M}
  proof: ht ▸ hv.linearIndepOn_id

中文:
定理 LinearIndependent.linearIndepOn_id'
  结论: (hv : LinearIndependent R v) {t : 集合 M}
  证明: ht ▸ hv.linearIndepOn_id

Depends on / 依赖: hv.linearIndepOn_id, linearIndepOn_id
-/
theorem LinearIndependent.linearIndepOn_id' (hv : LinearIndependent R v) {t : Set M}
    (ht : Set.range v = t) : LinearIndepOn R id t :=
  ht ▸ hv.linearIndepOn_id

section Indexed

/--
theorem `linearIndepOn_iffₛ` / 定理 `linearIndepOn_iffₛ`

English:
theorem linearIndepOn_iffₛ
  statement: LinearIndepOn R v s ↔
  proof: by
  simp only [LinearIndepOn, linearIndependent_iffₛ, Finsupp.mem_supported,
    Finsupp.linearCombination_apply, Set.subset_def, Finset.mem_coe]
refine ⟨fun h l₁ h₁ l₂ h₂ eq => (Finsupp.subtypeDomain_eq_iff h₁ h₂).1 h _ _
    (Finsupp.sum_subtypeDomain_index h₁).trans eq ▸ (Finsupp.sum_subtypeDomain_index h₂).symm,
    fun h l₁ l₂ eq => ?_⟩
refine Finsupp.embDomain_injective (Embedding.subtype (· in s)) h _ ?_ _ ?_ ?_
  iterate 2 simpa using fun _ h _ => h
  simp_rw [Finsupp.embDomain_eq_mapDomain]
  rwa [Finsupp.sum_mapDomain_index, Finsupp.sum_mapDomain_index] <;>
    intros <;> simp only [zero_smul, add_smul]

中文:
定理 linearIndepOn_iffₛ
  结论: LinearIndepOn R v s ↔
  证明: by
  simp only [LinearIndepOn, linearIndependent_iffₛ, Finsupp.mem_supported,
    Finsupp.linearCombination_apply, Set.subset_def, Finset.mem_coe]
refine ⟨fun h l₁ h₁ l₂ h₂ eq => (Finsupp.subtypeDomain_eq_iff h₁ h₂).1 h _ _
    (Finsupp.sum_subtypeDomain_index h₁).trans eq ▸ (Finsupp.sum_subtypeDomain_index h₂).symm,
    fun h l₁ l₂ eq => ?_⟩
refine Finsupp.embDomain_injective (Embedding.subtype (· in s)) h _ ?_ _ ?_ ?_
  iterate 2 simpa using fun _ h _ => h
  simp_rw [Finsupp.embDomain_eq_mapDomain]
  rwa [Finsupp.sum_mapDomain_index, Finsupp.sum_mapDomain_index] <;>
    intros <;> simp only [zero_smul, add_smul]

Depends on / 依赖: Embedding, Embedding.subtype, Finset, Finset.mem_coe, Finsupp, Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_injective, Finsupp.linearCombination_apply, Finsupp.mem_supported, Finsupp.subtypeDomain_eq_iff, Finsupp.sum_subtypeDomain_index, LinearIndepOn, Set.subset_def, embDomain_eq_mapDomain, embDomain_injective, iterate, linearCombination_apply, mem_coe, mem_supported, simp_rw
-/
theorem linearIndepOn_iffₛ : LinearIndepOn R v s ↔
      forall f in Finsupp.supported R R s, forall g in Finsupp.supported R R s,
        Finsupp.linearCombination R v f = Finsupp.linearCombination R v g -> f = g := by
  simp only [LinearIndepOn, linearIndependent_iffₛ, Finsupp.mem_supported,
    Finsupp.linearCombination_apply, Set.subset_def, Finset.mem_coe]
refine ⟨fun h l₁ h₁ l₂ h₂ eq => (Finsupp.subtypeDomain_eq_iff h₁ h₂).1 h _ _
    (Finsupp.sum_subtypeDomain_index h₁).trans eq ▸ (Finsupp.sum_subtypeDomain_index h₂).symm,
    fun h l₁ l₂ eq => ?_⟩
refine Finsupp.embDomain_injective (Embedding.subtype (· in s)) h _ ?_ _ ?_ ?_
  iterate 2 simpa using fun _ h _ => h
  simp_rw [Finsupp.embDomain_eq_mapDomain]
  rwa [Finsupp.sum_mapDomain_index, Finsupp.sum_mapDomain_index] <;>
    intros <;> simp only [zero_smul, add_smul]

/--
theorem `linearDepOn_iff'ₛ` / 定理 `linearDepOn_iff'ₛ`

English:
theorem linearDepOn_iff'ₛ
  statement: ¬LinearIndepOn R v s ↔
  proof: by
  simp [linearIndepOn_iffₛ]

中文:
定理 linearDepOn_iff'ₛ
  结论: ¬LinearIndepOn R v s ↔
  证明: by
  simp [linearIndepOn_iffₛ]
-/
theorem linearDepOn_iff'ₛ : ¬LinearIndepOn R v s ↔
      exists f g : ι ->₀ R, f in Finsupp.supported R R s ∧ g in Finsupp.supported R R s ∧
        Finsupp.linearCombination R v f = Finsupp.linearCombination R v g ∧ f != g := by
  simp [linearIndepOn_iffₛ]

/--
theorem `linearDepOn_iffₛ` / 定理 `linearDepOn_iffₛ`

English:
theorem linearDepOn_iffₛ
  statement: ¬LinearIndepOn R v s ↔
  proof: linearDepOn_iff'ₛ

中文:
定理 linearDepOn_iffₛ
  结论: ¬LinearIndepOn R v s ↔
  证明: linearDepOn_iff'ₛ

Depends on / 依赖: linearDepOn_iff
-/
theorem linearDepOn_iffₛ : ¬LinearIndepOn R v s ↔
      exists f g : ι ->₀ R, f in Finsupp.supported R R s ∧ g in Finsupp.supported R R s ∧
        ∑ i in f.support, f i • v i = ∑ i in g.support, g i • v i ∧ f != g :=
  linearDepOn_iff'ₛ

/--
theorem `linearIndependent_restrict_iff` / 定理 `linearIndependent_restrict_iff`

English:
theorem linearIndependent_restrict_iff
  proof: Iff.rfl

中文:
定理 linearIndependent_restrict_iff
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem linearIndependent_restrict_iff :
    LinearIndependent R (s.domRestrict v) ↔ LinearIndepOn R v s := Iff.rfl

/--
theorem `LinearIndepOn.linearIndependent_restrict` / 定理 `LinearIndepOn.linearIndependent_restrict`

English:
theorem LinearIndepOn.linearIndependent_restrict
  given: (hs : LinearIndepOn R v s)
  proof: hs

中文:
定理 LinearIndepOn.linearIndependent_restrict
  条件: (hs : LinearIndepOn R v s)
  证明: hs
-/
theorem LinearIndepOn.linearIndependent_restrict (hs : LinearIndepOn R v s) :
    LinearIndependent R (s.domRestrict v) :=
  hs

/--
theorem `linearIndepOn_iff_linearCombinationOnₛ` / 定理 `linearIndepOn_iff_linearCombinationOnₛ`

English:
theorem linearIndepOn_iff_linearCombinationOnₛ
  proof: by
  rw [← linearIndependent_restrict_iff]
  simp [LinearIndependent, Finsupp.linearCombination_restrict]

中文:
定理 linearIndepOn_iff_linearCombinationOnₛ
  证明: by
  rw [← linearIndependent_restrict_iff]
  simp [LinearIndependent, Finsupp.linearCombination_restrict]

Depends on / 依赖: Finsupp, Finsupp.linearCombination_restrict, LinearIndependent, linearCombination_restrict, linearIndependent_restrict_iff
-/
theorem linearIndepOn_iff_linearCombinationOnₛ :
    LinearIndepOn R v s ↔ Injective (Finsupp.linearCombinationOn ι M R v s) := by
  rw [← linearIndependent_restrict_iff]
  simp [LinearIndependent, Finsupp.linearCombination_restrict]

end Indexed

section repr

/-- Canonical isomorphism between linear combinations and the span of linearly independent vectors.
-/
@[simps (rhsMd := default) apply_coe symm_apply]
/--
Definition of `LinearIndependent.linearCombinationEquiv` / `LinearIndependent.linearCombinationEquiv` 的定义

English:
definition LinearIndependent.linearCombinationEquiv
  signature: (hv : LinearIndependent R v)
  body: by
  refine LinearEquiv.ofBijective (LinearMap.codRestrict (span R (range v))
    (Finsupp.linearCombination R v) ?_) ⟨hv.codRestrict _, ?_⟩
  · simp_rw [← Finsupp.range_linearCombination]; exact fun c => ⟨c, rfl⟩
  rw [← LinearMap.range_eq_top]; rw [LinearMap.range_eq_map]; rw [LinearMap.map_codRestrict]; rw [← LinearMap.range_le_iff_comap]; rw [range_subtype]; rw [Submodule.map_top]; rw [Finsupp.range_linearCombination]

中文:
定义 LinearIndependent.linearCombinationEquiv
  签名: (hv : LinearIndependent R v)
  定义体: by
  refine LinearEquiv.ofBijective (LinearMap.codRestrict (span R (range v))
    (Finsupp.linearCombination R v) ?_) ⟨hv.codRestrict _, ?_⟩
  · simp_rw [← Finsupp.range_linearCombination]; exact fun c => ⟨c, rfl⟩
  rw [← LinearMap.range_eq_top]; rw [LinearMap.range_eq_map]; rw [LinearMap.map_codRestrict]; rw [← LinearMap.range_le_iff_comap]; rw [range_subtype]; rw [Submodule.map_top]; rw [Finsupp.range_linearCombination]

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Finsupp.range_linearCombination, LinearEquiv, LinearEquiv.ofBijective, LinearMap, LinearMap.codRestrict, LinearMap.map_codRestrict, LinearMap.range_eq_map, LinearMap.range_eq_top, LinearMap.range_le_iff_comap, Submodule, Submodule.map_top, codRestrict, hv.codRestrict, linearCombination, map_codRestrict, map_top, ofBijective, range_eq_map
-/
def LinearIndependent.linearCombinationEquiv (hv : LinearIndependent R v) :
    (ι ->₀ R) ≃ₗ[R] span R (range v) := by
  refine LinearEquiv.ofBijective (LinearMap.codRestrict (span R (range v))
    (Finsupp.linearCombination R v) ?_) ⟨hv.codRestrict _, ?_⟩
  · simp_rw [← Finsupp.range_linearCombination]; exact fun c => ⟨c, rfl⟩
  rw [← LinearMap.range_eq_top]; rw [LinearMap.range_eq_map]; rw [LinearMap.map_codRestrict]; rw [← LinearMap.range_le_iff_comap]; rw [range_subtype]; rw [Submodule.map_top]; rw [Finsupp.range_linearCombination]

/--
Definition of `LinearIndependent.repr` / `LinearIndependent.repr` 的定义

English:
definition LinearIndependent.repr
  signature: (hv : LinearIndependent R v)
  body: hv.linearCombinationEquiv.symm

中文:
定义 LinearIndependent.repr
  签名: (hv : LinearIndependent R v)
  定义体: hv.linearCombinationEquiv.symm

Depends on / 依赖: hv.linearCombinationEquiv.symm, linearCombinationEquiv
-/
def LinearIndependent.repr (hv : LinearIndependent R v) : span R (range v) ->ₗ[R] ι ->₀ R :=
  hv.linearCombinationEquiv.symm

variable (hv : LinearIndependent R v) {i : ι}

@[simp]
/--
theorem `LinearIndependent.linearCombination_repr` / 定理 `LinearIndependent.linearCombination_repr`

English:
theorem LinearIndependent.linearCombination_repr
  given: (x)
  proof: Subtype.ext_iff.1 (LinearEquiv.apply_symm_apply hv.linearCombinationEquiv x)

中文:
定理 LinearIndependent.linearCombination_repr
  条件: (x)
  证明: Subtype.ext_iff.1 (LinearEquiv.apply_symm_apply hv.linearCombinationEquiv x)

Depends on / 依赖: LinearEquiv, LinearEquiv.apply_symm_apply, Subtype, Subtype.ext_iff, apply_symm_apply, ext_iff, hv.linearCombinationEquiv, linearCombinationEquiv
-/
theorem LinearIndependent.linearCombination_repr (x) :
    Finsupp.linearCombination R v (hv.repr x) = x :=
  Subtype.ext_iff.1 (LinearEquiv.apply_symm_apply hv.linearCombinationEquiv x)

/--
theorem `LinearIndependent.linearCombination_comp_repr` / 定理 `LinearIndependent.linearCombination_comp_repr`

English:
theorem LinearIndependent.linearCombination_comp_repr
  proof: LinearMap.ext hv.linearCombination_repr

中文:
定理 LinearIndependent.linearCombination_comp_repr
  证明: LinearMap.ext hv.linearCombination_repr

Depends on / 依赖: LinearMap, LinearMap.ext, hv.linearCombination_repr, linearCombination_repr
-/
theorem LinearIndependent.linearCombination_comp_repr :
    (Finsupp.linearCombination R v).comp hv.repr = Submodule.subtype _ :=
LinearMap.ext hv.linearCombination_repr

/--
theorem `LinearIndependent.repr_ker` / 定理 `LinearIndependent.repr_ker`

English:
theorem LinearIndependent.repr_ker
  statement: LinearMap.ker hv.repr = ⊥
  proof: by
  rw [LinearIndependent.repr]; rw [LinearEquiv.ker]

中文:
定理 LinearIndependent.repr_ker
  结论: 线性映射.ker hv.repr = ⊥
  证明: by
  rw [LinearIndependent.repr]; rw [LinearEquiv.ker]

Depends on / 依赖: LinearEquiv, LinearEquiv.ker, LinearIndependent, LinearIndependent.repr
-/
theorem LinearIndependent.repr_ker : LinearMap.ker hv.repr = ⊥ := by
  rw [LinearIndependent.repr]; rw [LinearEquiv.ker]

/--
theorem `LinearIndependent.repr_range` / 定理 `LinearIndependent.repr_range`

English:
theorem LinearIndependent.repr_range
  statement: LinearMap.range hv.repr = ⊤
  proof: by
  rw [LinearIndependent.repr]; rw [LinearEquiv.range]

中文:
定理 LinearIndependent.repr_range
  结论: 线性映射.range hv.repr = ⊤
  证明: by
  rw [LinearIndependent.repr]; rw [LinearEquiv.range]

Depends on / 依赖: LinearEquiv, LinearEquiv.range, LinearIndependent, LinearIndependent.repr
-/
theorem LinearIndependent.repr_range : LinearMap.range hv.repr = ⊤ := by
  rw [LinearIndependent.repr]; rw [LinearEquiv.range]

/--
theorem `LinearIndependent.repr_eq` / 定理 `LinearIndependent.repr_eq`

English:
theorem LinearIndependent.repr_eq
  statement: {l : ι ->₀ R} {x : span R (range v)}
  proof: by
  have :
    ↑((LinearIndependent.linearCombinationEquiv hv : (ι ->₀ R) ->ₗ[R] span R (range v)) l) =
      Finsupp.linearCombination R v l :=
    rfl
  have : (LinearIndependent.linearCombinationEquiv hv : (ι ->₀ R) ->ₗ[R] span R (range v)) l = x := by
    rw [eq] at this
    exact Subtype.ext_iff.2 this
  rw [← LinearEquiv.symm_apply_apply hv.linearCombinationEquiv l]
  rw [← this]
  rfl

中文:
定理 LinearIndependent.repr_eq
  结论: {l : ι ->₀ R} {x : span R (range v)}
  证明: by
  have :
    ↑((LinearIndependent.linearCombinationEquiv hv : (ι ->₀ R) ->ₗ[R] span R (range v)) l) =
      Finsupp.linearCombination R v l :=
    rfl
  have : (LinearIndependent.linearCombinationEquiv hv : (ι ->₀ R) ->ₗ[R] span R (range v)) l = x := by
    rw [eq] at this
    exact Subtype.ext_iff.2 this
  rw [← LinearEquiv.symm_apply_apply hv.linearCombinationEquiv l]
  rw [← this]
  rfl

Depends on / 依赖: Finsupp, Finsupp.linearCombination, LinearEquiv, LinearEquiv.symm_apply_apply, LinearIndependent, LinearIndependent.linearCombinationEquiv, Subtype, Subtype.ext_iff, ext_iff, hv.linearCombinationEquiv, linearCombination, linearCombinationEquiv, symm_apply_apply
-/
theorem LinearIndependent.repr_eq {l : ι ->₀ R} {x : span R (range v)}
    (eq : Finsupp.linearCombination R v l = ↑x) : hv.repr x = l := by
  have :
    ↑((LinearIndependent.linearCombinationEquiv hv : (ι ->₀ R) ->ₗ[R] span R (range v)) l) =
      Finsupp.linearCombination R v l :=
    rfl
  have : (LinearIndependent.linearCombinationEquiv hv : (ι ->₀ R) ->ₗ[R] span R (range v)) l = x := by
    rw [eq] at this
    exact Subtype.ext_iff.2 this
  rw [← LinearEquiv.symm_apply_apply hv.linearCombinationEquiv l]
  rw [← this]
  rfl

/--
theorem `LinearIndependent.repr_eq_single` / 定理 `LinearIndependent.repr_eq_single`

English:
theorem LinearIndependent.repr_eq_single
  given: (i) (x : span R (range v)) (hx : ↑x = v i)
  proof: by
  apply hv.repr_eq
  simp [Finsupp.linearCombination_single, hx]

中文:
定理 LinearIndependent.repr_eq_single
  条件: (i) (x : span R (range v)) (hx : ↑x = v i)
  证明: by
  apply hv.repr_eq
  simp [Finsupp.linearCombination_single, hx]

Depends on / 依赖: Finsupp, Finsupp.linearCombination_single, hv.repr_eq, linearCombination_single, repr_eq
-/
theorem LinearIndependent.repr_eq_single (i) (x : span R (range v)) (hx : ↑x = v i) :
    hv.repr x = Finsupp.single i 1 := by
  apply hv.repr_eq
  simp [Finsupp.linearCombination_single, hx]

/--
theorem `LinearIndependent.span_repr_eq` / 定理 `LinearIndependent.span_repr_eq`

English:
theorem LinearIndependent.span_repr_eq
  given: [Nontrivial R] (x)
  proof: by
  have p :
    (Span.repr R (Set.range v) x).equivMapDomain (Equiv.ofInjective _ hv.injective).symm =
      hv.repr x := by
    apply (LinearIndependent.linearCombinationEquiv hv).injective
    ext
    simp only [LinearIndependent.linearCombinationEquiv_apply_coe, Equiv.self_comp_ofInjective_symm,
      LinearIndependent.linearCombination_repr, Finsupp.linearCombination_equivMapDomain,
      Span.finsupp_linearCombination_repr]
  ext ⟨_, ⟨i, rfl⟩⟩
  simp [← p]

中文:
定理 LinearIndependent.span_repr_eq
  条件: [非平凡 R] (x)
  证明: by
  have p :
    (Span.repr R (Set.range v) x).equivMapDomain (Equiv.ofInjective _ hv.injective).symm =
      hv.repr x := by
    apply (LinearIndependent.linearCombinationEquiv hv).injective
    ext
    simp only [LinearIndependent.linearCombinationEquiv_apply_coe, Equiv.self_comp_ofInjective_symm,
      LinearIndependent.linearCombination_repr, Finsupp.linearCombination_equivMapDomain,
      Span.finsupp_linearCombination_repr]
  ext ⟨_, ⟨i, rfl⟩⟩
  simp [← p]

Depends on / 依赖: Equiv.ofInjective, Equiv.self_comp_ofInjective_symm, Finsupp, Finsupp.linearCombination_equivMapDomain, LinearIndependent, LinearIndependent.linearCombinationEquiv, LinearIndependent.linearCombinationEquiv_apply_coe, LinearIndependent.linearCombination_repr, Set.range, Span.finsupp_linearCombination_repr, Span.repr, equivMapDomain, finsupp_linearCombination_repr, hv.injective, hv.repr, injective, linearCombinationEquiv, linearCombinationEquiv_apply_coe, linearCombination_equivMapDomain, linearCombination_repr
-/
theorem LinearIndependent.span_repr_eq [Nontrivial R] (x) :
    Span.repr R (Set.range v) x =
      (hv.repr x).equivMapDomain (Equiv.ofInjective _ hv.injective) := by
  have p :
    (Span.repr R (Set.range v) x).equivMapDomain (Equiv.ofInjective _ hv.injective).symm =
      hv.repr x := by
    apply (LinearIndependent.linearCombinationEquiv hv).injective
    ext
    simp only [LinearIndependent.linearCombinationEquiv_apply_coe, Equiv.self_comp_ofInjective_symm,
      LinearIndependent.linearCombination_repr, Finsupp.linearCombination_equivMapDomain,
      Span.finsupp_linearCombination_repr]
  ext ⟨_, ⟨i, rfl⟩⟩
  simp [← p]

/--
theorem `LinearIndependent.eq_zero_of_smul_mem_span` / 定理 `LinearIndependent.eq_zero_of_smul_mem_span`

English:
theorem LinearIndependent.eq_zero_of_smul_mem_span
  statement: (hv : LinearIndependent R v) (i : ι) (a : R)
  proof: by
  rw [Finsupp.span_image_eq_map_linearCombination]; rw [mem_map] at ha
  rcases ha with ⟨l, hl, e⟩
  rw [linearIndependent_iffₛ.1 hv l (Finsupp.single i a) (by simp [e])] at hl
  by_contra hn
  exact (notMem_of_mem_sdiff (hl <| by simp [hn])) (mem_singleton _)

nonrec lemma LinearIndepOn.eq_zero_of_smul_mem_span (hv : LinearIndepOn R v s) (hi : i in s) (a : R)
    (ha : a • v i in span R (v '' (s \ {i}))) : a = 0 :=
hv.eq_zero_of_smul_mem_span ⟨i, hi⟩ _ by
    simpa [← comp_def, image_comp, image_sdiff Subtype.val_injective]

中文:
定理 LinearIndependent.eq_zero_of_smul_mem_span
  结论: (hv : LinearIndependent R v) (i : ι) (a : R)
  证明: by
  rw [Finsupp.span_image_eq_map_linearCombination]; rw [mem_map] at ha
  rcases ha with ⟨l, hl, e⟩
  rw [linearIndependent_iffₛ.1 hv l (Finsupp.single i a) (by simp [e])] at hl
  by_contra hn
  exact (notMem_of_mem_sdiff (hl <| by simp [hn])) (mem_singleton _)

nonrec lemma LinearIndepOn.eq_zero_of_smul_mem_span (hv : LinearIndepOn R v s) (hi : i in s) (a : R)
    (ha : a • v i in span R (v '' (s \ {i}))) : a = 0 :=
hv.eq_zero_of_smul_mem_span ⟨i, hi⟩ _ by
    simpa [← comp_def, image_comp, image_sdiff Subtype.val_injective]

Depends on / 依赖: Finsupp, Finsupp.single, Finsupp.span_image_eq_map_linearCombination, mem_map, mem_singleton, notMem_of_mem_sdiff, single, span_image_eq_map_linearCombination
-/
theorem LinearIndependent.eq_zero_of_smul_mem_span (hv : LinearIndependent R v) (i : ι) (a : R)
    (ha : a • v i in span R (v '' (univ \ {i}))) : a = 0 := by
  rw [Finsupp.span_image_eq_map_linearCombination]; rw [mem_map] at ha
  rcases ha with ⟨l, hl, e⟩
  rw [linearIndependent_iffₛ.1 hv l (Finsupp.single i a) (by simp [e])] at hl
  by_contra hn
  exact (notMem_of_mem_sdiff (hl <| by simp [hn])) (mem_singleton _)

nonrec lemma LinearIndepOn.eq_zero_of_smul_mem_span (hv : LinearIndepOn R v s) (hi : i in s) (a : R)
    (ha : a • v i in span R (v '' (s \ {i}))) : a = 0 :=
hv.eq_zero_of_smul_mem_span ⟨i, hi⟩ _ by
    simpa [← comp_def, image_comp, image_sdiff Subtype.val_injective]

variable [Nontrivial R]

/--
lemma `LinearIndependent.notMem_span` / 引理 `LinearIndependent.notMem_span`

English:
lemma LinearIndependent.notMem_span
  given: (hv : LinearIndependent R v) (i : ι)
  proof: fun hi =>
one_ne_zero hv.eq_zero_of_smul_mem_span i 1 by simpa [Set.compl_eq_univ_sdiff] using hi

中文:
引理 LinearIndependent.notMem_span
  条件: (hv : LinearIndependent R v) (i : ι)
  证明: fun hi =>
one_ne_zero hv.eq_zero_of_smul_mem_span i 1 by simpa [Set.compl_eq_univ_sdiff] using hi
-/
lemma LinearIndependent.notMem_span (hv : LinearIndependent R v) (i : ι) :
    v i ∉ span R (v '' {i}ᶜ) := fun hi =>
one_ne_zero hv.eq_zero_of_smul_mem_span i 1 by simpa [Set.compl_eq_univ_sdiff] using hi

/--
lemma `LinearIndepOn.notMem_span` / 引理 `LinearIndepOn.notMem_span`

English:
lemma LinearIndepOn.notMem_span
  given: (hv : LinearIndepOn R v s) (hi : i in s)
  proof: fun hi' =>
one_ne_zero hv.eq_zero_of_smul_mem_span hi 1 by simpa [Set.compl_eq_univ_sdiff] using hi'

中文:
引理 LinearIndepOn.notMem_span
  条件: (hv : LinearIndepOn R v s) (hi : i in s)
  证明: fun hi' =>
one_ne_zero hv.eq_zero_of_smul_mem_span hi 1 by simpa [Set.compl_eq_univ_sdiff] using hi'
-/
lemma LinearIndepOn.notMem_span (hv : LinearIndepOn R v s) (hi : i in s) :
    v i ∉ span R (v '' (s \ {i})) := fun hi' =>
one_ne_zero hv.eq_zero_of_smul_mem_span hi 1 by simpa [Set.compl_eq_univ_sdiff] using hi'

/--
lemma `LinearIndepOn.notMem_span_of_insert` / 引理 `LinearIndepOn.notMem_span_of_insert`

English:
lemma LinearIndepOn.notMem_span_of_insert
  given: (hv : LinearIndepOn R v (insert i s)) (hi : i ∉ s)
  proof: by simpa [hi] using hv.notMem_span mem_insert ..

中文:
引理 LinearIndepOn.notMem_span_of_insert
  条件: (hv : LinearIndepOn R v (insert i s)) (hi : i ∉ s)
  证明: by simpa [hi] using hv.notMem_span mem_insert ..

Depends on / 依赖: hv.notMem_span, mem_insert, notMem_span
-/
lemma LinearIndepOn.notMem_span_of_insert (hv : LinearIndepOn R v (insert i s)) (hi : i ∉ s) :
v i ∉ span R (v '' s) := by simpa [hi] using hv.notMem_span mem_insert ..

end repr

section Maximal

universe v w

/--
A linearly independent family is maximal if there is no strictly larger linearly independent family.
-/
@[nolint unusedArguments]
/--
Definition of `LinearIndependent.Maximal` / `LinearIndependent.Maximal` 的定义

English:
definition LinearIndependent.Maximal
  signature: {ι : Type w} {R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M]
  body: forall (s : Set M) (_i' : LinearIndependent R ((↑) : s -> M)) (_h : range v <= s), range v = s

中文:
定义 LinearIndependent.极大
  签名: {ι : 类型 w} {R : 类型u} [半环 R] {M : 类型v} [加法交换幺半群 M]
  定义体: forall (s : Set M) (_i' : LinearIndependent R ((↑) : s -> M)) (_h : range v <= s), range v = s

Depends on / 依赖: LinearIndependent
-/
def LinearIndependent.Maximal {ι : Type w} {R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M]
    [Module R M] {v : ι -> M} (_i : LinearIndependent R v) : Prop :=
  forall (s : Set M) (_i' : LinearIndependent R ((↑) : s -> M)) (_h : range v <= s), range v = s

/--
theorem `LinearIndependent.maximal_iff` / 定理 `LinearIndependent.maximal_iff`

English:
theorem LinearIndependent.maximal_iff
  statement: {ι : Type w} {R : Type u} [Semiring R] [Nontrivial R]
  proof: by
  constructor
  · rintro p κ w i' j rfl
    specialize p (range w) i'.linearIndepOn_id (range_comp_subset_range _ _)
    rw [range_comp]; rw [← image_univ (f := w)] at p
    exact range_eq_univ.mp (image_injective.mpr i'.injective p)
  · intro p w i' h
    specialize
      p w ((↑) : w -> M) i' (fun i => ⟨v i, range_subset_iff.mp h i⟩)
        (by
          ext
          simp)
    have q := congr_arg (fun s => ((↑) : w -> M) '' s) p.range_eq
    rw [← image_univ]; rw [image_image] at q
    simpa using q

中文:
定理 LinearIndependent.maximal_iff
  结论: {ι : 类型 w} {R : 类型u} [半环 R] [非平凡 R]
  证明: by
  constructor
  · rintro p κ w i' j rfl
    specialize p (range w) i'.linearIndepOn_id (range_comp_subset_range _ _)
    rw [range_comp]; rw [← image_univ (f := w)] at p
    exact range_eq_univ.mp (image_injective.mpr i'.injective p)
  · intro p w i' h
    specialize
      p w ((↑) : w -> M) i' (fun i => ⟨v i, range_subset_iff.mp h i⟩)
        (by
          ext
          simp)
    have q := congr_arg (fun s => ((↑) : w -> M) '' s) p.range_eq
    rw [← image_univ]; rw [image_image] at q
    simpa using q

Depends on / 依赖: congr_arg, image_image, image_injective, image_injective.mpr, image_univ, injective, linearIndepOn_id, p.range_eq, range_comp, range_comp_subset_range, range_eq, range_eq_univ, range_eq_univ.mp, range_subset_iff, range_subset_iff.mp, specialize
-/
theorem LinearIndependent.maximal_iff {ι : Type w} {R : Type u} [Semiring R] [Nontrivial R]
    {M : Type v} [AddCommMonoid M] [Module R M] {v : ι -> M} (i : LinearIndependent R v) :
    i.Maximal ↔
      forall (κ : Type v) (w : κ -> M) (_i' : LinearIndependent R w) (j : ι -> κ) (_h : w ∘ j = v),
        Surjective j := by
  constructor
  · rintro p κ w i' j rfl
    specialize p (range w) i'.linearIndepOn_id (range_comp_subset_range _ _)
    rw [range_comp]; rw [← image_univ (f := w)] at p
    exact range_eq_univ.mp (image_injective.mpr i'.injective p)
  · intro p w i' h
    specialize
      p w ((↑) : w -> M) i' (fun i => ⟨v i, range_subset_iff.mp h i⟩)
        (by
          ext
          simp)
    have q := congr_arg (fun s => ((↑) : w -> M) '' s) p.range_eq
    rw [← image_univ]; rw [image_image] at q
    simpa using q

end Maximal

/-!
### Properties which require `LinearOrder R` and `CanonicallyOrderedAdd R`

If the semiring `R` is linearly and canonically ordered (e.g. `R = ℕ`), `LinearIndependent` can be
proved from linear combination over two disjoint sets.
-/

section LinearlyCanonicallyOrdered

variable [LinearOrder R] [CanonicallyOrderedAdd R] [AddRightReflectLE R] [IsCancelAdd M]

/--
theorem `linearIndependent_iffₒₛ` / 定理 `linearIndependent_iffₒₛ`

English:
theorem linearIndependent_iffₒₛ
  proof: by
  classical
  let : Sub R := CanonicallyOrderedAdd.toSub
  have : OrderedSub R := CanonicallyOrderedAdd.toOrderedSub
  rw [linearIndependent_iff'ₛ]
  refine ⟨fun h s t f hst heq => ?_, fun h s f g heq => ?_⟩
  · specialize h (s union t) (fun i => if i in s then f i else 0) (fun i => if i in t then f i else 0) ?_
    · simpa
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · simpa [hi, hst.notMem_of_mem_left_finset hi] using h i (Finset.mem_union_left _ hi)
    · simpa [hi, hst.notMem_of_mem_right_finset hi] using (h i (Finset.mem_union_right _ hi)).symm
  · specialize h { i in s | g i <= f i } { i in s | f i < g i }
      (fun i => if g i <= f i then f i - g i else g i - f i) ?_ ?_
    · simp_rw [Finset.disjoint_left, Finset.mem_filter]
      exact fun i ⟨_, hi⟩ ⟨_, hi'⟩ => hi.not_gt hi'
    · rw [← add_right_cancel_iff
        (a := ∑ i in s with g i <= f i, g i • v i + ∑ i in s with f i < g i, f i • v i)]
      conv_lhs => rw [← add_assoc, ← Finset.sum_add_distrib]
      conv_rhs => rw [add_left_comm, ← Finset.sum_add_distrib]
      convert! heq
        <;> simp_rw [← Finset.sum_filter_add_sum_filter_not s (fun i => g i <= f i), not_le]
        <;> congr! 2 with i hi
        <;> simp only [Finset.mem_filter] at hi
      · simp [hi.2, ← add_smul, tsub_add_cancel_of_le hi.2]
      · simp [hi.2.not_ge, ← add_smul, tsub_add_cancel_of_le hi.2.le]
    simp only [Finset.mem_filter] at h
    intro i hi
    by_cases hi' : g i <= f i
    · apply hi'.antisymm'
      simpa [hi', tsub_eq_zero_iff_le] using h.1 i ⟨hi, hi'⟩
    · apply (not_le.1 hi').le.antisymm
      simpa [hi', tsub_eq_zero_iff_le] using h.2 i ⟨hi, not_le.1 hi'⟩

中文:
定理 linearIndependent_iffₒₛ
  证明: by
  classical
  let : Sub R := CanonicallyOrderedAdd.toSub
  have : OrderedSub R := CanonicallyOrderedAdd.toOrderedSub
  rw [linearIndependent_iff'ₛ]
  refine ⟨fun h s t f hst heq => ?_, fun h s f g heq => ?_⟩
  · specialize h (s union t) (fun i => if i in s then f i else 0) (fun i => if i in t then f i else 0) ?_
    · simpa
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · simpa [hi, hst.notMem_of_mem_left_finset hi] using h i (Finset.mem_union_left _ hi)
    · simpa [hi, hst.notMem_of_mem_right_finset hi] using (h i (Finset.mem_union_right _ hi)).symm
  · specialize h { i in s | g i <= f i } { i in s | f i < g i }
      (fun i => if g i <= f i then f i - g i else g i - f i) ?_ ?_
    · simp_rw [Finset.disjoint_left, Finset.mem_filter]
      exact fun i ⟨_, hi⟩ ⟨_, hi'⟩ => hi.not_gt hi'
    · rw [← add_right_cancel_iff
        (a := ∑ i in s with g i <= f i, g i • v i + ∑ i in s with f i < g i, f i • v i)]
      conv_lhs => rw [← add_assoc, ← Finset.sum_add_distrib]
      conv_rhs => rw [add_left_comm, ← Finset.sum_add_distrib]
      convert! heq
        <;> simp_rw [← Finset.sum_filter_add_sum_filter_not s (fun i => g i <= f i), not_le]
        <;> congr! 2 with i hi
        <;> simp only [Finset.mem_filter] at hi
      · simp [hi.2, ← add_smul, tsub_add_cancel_of_le hi.2]
      · simp [hi.2.not_ge, ← add_smul, tsub_add_cancel_of_le hi.2.le]
    simp only [Finset.mem_filter] at h
    intro i hi
    by_cases hi' : g i <= f i
    · apply hi'.antisymm'
      simpa [hi', tsub_eq_zero_iff_le] using h.1 i ⟨hi, hi'⟩
    · apply (not_le.1 hi').le.antisymm
      simpa [hi', tsub_eq_zero_iff_le] using h.2 i ⟨hi, not_le.1 hi'⟩

Depends on / 依赖: CanonicallyOrderedAdd, CanonicallyOrderedAdd.toOrderedSub, CanonicallyOrderedAdd.toSub, Finset, Finset.mem_union_left, OrderedSub, classical, hst.notMem_of_mem_left_finset, hst.notMem_of_mem_right_finset, linearIndependent_iff, mem_union_left, notMem_of_mem_left_finset, notMem_of_mem_right_finset, specialize, toOrderedSub
-/
theorem linearIndependent_iffₒₛ :
    LinearIndependent R v ↔
      forall (s t : Finset ι) (f : ι -> R), Disjoint s t ->
        ∑ i in s, f i • v i = ∑ i in t, f i • v i -> (forall i in s, f i = 0) ∧ forall i in t, f i = 0 := by
  classical
  let : Sub R := CanonicallyOrderedAdd.toSub
  have : OrderedSub R := CanonicallyOrderedAdd.toOrderedSub
  rw [linearIndependent_iff'ₛ]
  refine ⟨fun h s t f hst heq => ?_, fun h s f g heq => ?_⟩
  · specialize h (s union t) (fun i => if i in s then f i else 0) (fun i => if i in t then f i else 0) ?_
    · simpa
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · simpa [hi, hst.notMem_of_mem_left_finset hi] using h i (Finset.mem_union_left _ hi)
    · simpa [hi, hst.notMem_of_mem_right_finset hi] using (h i (Finset.mem_union_right _ hi)).symm
  · specialize h { i in s | g i <= f i } { i in s | f i < g i }
      (fun i => if g i <= f i then f i - g i else g i - f i) ?_ ?_
    · simp_rw [Finset.disjoint_left, Finset.mem_filter]
      exact fun i ⟨_, hi⟩ ⟨_, hi'⟩ => hi.not_gt hi'
    · rw [← add_right_cancel_iff
        (a := ∑ i in s with g i <= f i, g i • v i + ∑ i in s with f i < g i, f i • v i)]
      conv_lhs => rw [← add_assoc, ← Finset.sum_add_distrib]
      conv_rhs => rw [add_left_comm, ← Finset.sum_add_distrib]
      convert! heq
        <;> simp_rw [← Finset.sum_filter_add_sum_filter_not s (fun i => g i <= f i), not_le]
        <;> congr! 2 with i hi
        <;> simp only [Finset.mem_filter] at hi
      · simp [hi.2, ← add_smul, tsub_add_cancel_of_le hi.2]
      · simp [hi.2.not_ge, ← add_smul, tsub_add_cancel_of_le hi.2.le]
    simp only [Finset.mem_filter] at h
    intro i hi
    by_cases hi' : g i <= f i
    · apply hi'.antisymm'
      simpa [hi', tsub_eq_zero_iff_le] using h.1 i ⟨hi, hi'⟩
    · apply (not_le.1 hi').le.antisymm
      simpa [hi', tsub_eq_zero_iff_le] using h.2 i ⟨hi, not_le.1 hi'⟩

/--
theorem `not_linearIndependent_iffₒₛ` / 定理 `not_linearIndependent_iffₒₛ`

English:
theorem not_linearIndependent_iffₒₛ
  proof: by
  simp only [linearIndependent_iffₒₛ, pos_iff_ne_zero]
  push +distrib Not
  refine ⟨fun ⟨s, t, f, hst, heq, h⟩ => ?_,
    fun ⟨s, t, f, hst, heq, hi⟩ => ⟨s, t, f, hst, heq, .inl hi⟩⟩
  rcases h with ⟨i, hi, hfi⟩ | ⟨i, hi, hgi⟩
  · exact ⟨s, t, f, hst, heq, i, hi, hfi⟩
  · exact ⟨t, s, f, hst.symm, heq.symm, i, hi, hgi⟩

nonrec theorem Fintype.linearIndependent_iffₒₛ [DecidableEq ι] [Fintype ι] :
    LinearIndependent R v ↔ forall t, forall (f : ι -> R),
      ∑ i in t, f i • v i = ∑ i ∉ t, f i • v i -> forall i, f i = 0 := by
  rw [linearIndependent_iffₒₛ]
  refine ⟨fun h t f heq i => ?_, fun h t₁ t₂ f ht₁t₂ heq => ?_⟩
  · specialize h t tᶜ f disjoint_compl_right heq
    by_cases hi : i in t
    · exact h.1 i hi
    · exact h.2 i (Finset.mem_compl.2 hi)
  · specialize h t₁ (fun i => if i in t₁ ∨ i in t₂ then f i else 0) ?_
    · rw [← Finset.sum_subset ht₁t₂.le_compl_left]
      · convert! heq using 2 with i hi i hi <;> simp [hi]
      · intro i hi hi'
        simp [Finset.mem_compl.1 hi, hi']
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩ <;> simpa [hi] using h i

中文:
定理 not_linearIndependent_iffₒₛ
  证明: by
  simp only [linearIndependent_iffₒₛ, pos_iff_ne_zero]
  push +distrib Not
  refine ⟨fun ⟨s, t, f, hst, heq, h⟩ => ?_,
    fun ⟨s, t, f, hst, heq, hi⟩ => ⟨s, t, f, hst, heq, .inl hi⟩⟩
  rcases h with ⟨i, hi, hfi⟩ | ⟨i, hi, hgi⟩
  · exact ⟨s, t, f, hst, heq, i, hi, hfi⟩
  · exact ⟨t, s, f, hst.symm, heq.symm, i, hi, hgi⟩

nonrec theorem Fintype.linearIndependent_iffₒₛ [DecidableEq ι] [Fintype ι] :
    LinearIndependent R v ↔ forall t, forall (f : ι -> R),
      ∑ i in t, f i • v i = ∑ i ∉ t, f i • v i -> forall i, f i = 0 := by
  rw [linearIndependent_iffₒₛ]
  refine ⟨fun h t f heq i => ?_, fun h t₁ t₂ f ht₁t₂ heq => ?_⟩
  · specialize h t tᶜ f disjoint_compl_right heq
    by_cases hi : i in t
    · exact h.1 i hi
    · exact h.2 i (Finset.mem_compl.2 hi)
  · specialize h t₁ (fun i => if i in t₁ ∨ i in t₂ then f i else 0) ?_
    · rw [← Finset.sum_subset ht₁t₂.le_compl_left]
      · convert! heq using 2 with i hi i hi <;> simp [hi]
      · intro i hi hi'
        simp [Finset.mem_compl.1 hi, hi']
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩ <;> simpa [hi] using h i

Depends on / 依赖: distrib, heq.symm, hst.symm, pos_iff_ne_zero
-/
theorem not_linearIndependent_iffₒₛ :
    ¬ LinearIndependent R v ↔
      exists (s t : Finset ι) (f : ι -> R),
        Disjoint s t ∧ ∑ i in s, f i • v i = ∑ i in t, f i • v i ∧ exists i in s, 0 < f i := by
  simp only [linearIndependent_iffₒₛ, pos_iff_ne_zero]
  push +distrib Not
  refine ⟨fun ⟨s, t, f, hst, heq, h⟩ => ?_,
    fun ⟨s, t, f, hst, heq, hi⟩ => ⟨s, t, f, hst, heq, .inl hi⟩⟩
  rcases h with ⟨i, hi, hfi⟩ | ⟨i, hi, hgi⟩
  · exact ⟨s, t, f, hst, heq, i, hi, hfi⟩
  · exact ⟨t, s, f, hst.symm, heq.symm, i, hi, hgi⟩

nonrec theorem Fintype.linearIndependent_iffₒₛ [DecidableEq ι] [Fintype ι] :
    LinearIndependent R v ↔ forall t, forall (f : ι -> R),
      ∑ i in t, f i • v i = ∑ i ∉ t, f i • v i -> forall i, f i = 0 := by
  rw [linearIndependent_iffₒₛ]
  refine ⟨fun h t f heq i => ?_, fun h t₁ t₂ f ht₁t₂ heq => ?_⟩
  · specialize h t tᶜ f disjoint_compl_right heq
    by_cases hi : i in t
    · exact h.1 i hi
    · exact h.2 i (Finset.mem_compl.2 hi)
  · specialize h t₁ (fun i => if i in t₁ ∨ i in t₂ then f i else 0) ?_
    · rw [← Finset.sum_subset ht₁t₂.le_compl_left]
      · convert! heq using 2 with i hi i hi <;> simp [hi]
      · intro i hi hi'
        simp [Finset.mem_compl.1 hi, hi']
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩ <;> simpa [hi] using h i

/--
theorem `Fintype.not_linearIndependent_iffₒₛ` / 定理 `Fintype.not_linearIndependent_iffₒₛ`

English:
theorem Fintype.not_linearIndependent_iffₒₛ
  given: [DecidableEq ι] [Fintype ι]
  proof: by
  simp only [linearIndependent_iffₒₛ, not_forall, pos_iff_ne_zero]
  refine ⟨fun ⟨t, f, heq, i, hfi⟩ => ?_, fun ⟨t, f, heq, i, hi, hfi⟩ =>
    ⟨t, f, heq, i, hfi⟩⟩
  by_cases hi' : i in t
  · exact ⟨t, f, heq, i, hi', hfi⟩
  · refine ⟨tᶜ, f, ?_, i, Finset.mem_compl.2 hi', hfi⟩
    simp [heq]

中文:
定理 有限类型.not_linearIndependent_iffₒₛ
  条件: [DecidableEq ι] [有限类型 ι]
  证明: by
  simp only [linearIndependent_iffₒₛ, not_forall, pos_iff_ne_zero]
  refine ⟨fun ⟨t, f, heq, i, hfi⟩ => ?_, fun ⟨t, f, heq, i, hi, hfi⟩ =>
    ⟨t, f, heq, i, hfi⟩⟩
  by_cases hi' : i in t
  · exact ⟨t, f, heq, i, hi', hfi⟩
  · refine ⟨tᶜ, f, ?_, i, Finset.mem_compl.2 hi', hfi⟩
    simp [heq]

Depends on / 依赖: Finset, Finset.mem_compl, mem_compl, not_forall, pos_iff_ne_zero
-/
theorem Fintype.not_linearIndependent_iffₒₛ [DecidableEq ι] [Fintype ι] :
    ¬ LinearIndependent R v ↔ exists t, exists (f : ι -> R),
      ∑ i in t, f i • v i = ∑ i ∉ t, f i • v i ∧ exists i in t, 0 < f i := by
  simp only [linearIndependent_iffₒₛ, not_forall, pos_iff_ne_zero]
  refine ⟨fun ⟨t, f, heq, i, hfi⟩ => ?_, fun ⟨t, f, heq, i, hi, hfi⟩ =>
    ⟨t, f, heq, i, hfi⟩⟩
  by_cases hi' : i in t
  · exact ⟨t, f, heq, i, hi', hfi⟩
  · refine ⟨tᶜ, f, ?_, i, Finset.mem_compl.2 hi', hfi⟩
    simp [heq]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `linearIndepOn_finset_iffₒₛ` / 引理 `linearIndepOn_finset_iffₒₛ`

English:
lemma linearIndepOn_finset_iffₒₛ
  given: [DecidableEq ι] {s : Finset ι}
  proof: by
  rw [LinearIndepOn]; rw [Fintype.linearIndependent_iffₒₛ]
  refine ⟨fun h t ht f heq i hi => h { i | i.1 in t } (f ∘ Subtype.val) ?_ ⟨i, hi⟩,
    fun h t f heq i => ?_⟩
  · simp only [Finset.compl_filter, Finset.sum_filter, Function.comp_apply, Finset.coe_sort_coe]
    rw [Finset.sum_coe_sort s fun i => if i in t then f i • v i else 0]; rw [Finset.sum_coe_sort s fun i => if i ∉ t then f i • v i else 0]
    simpa [Finset.inter_eq_right.2 ht, Finset.sum_ite, Finset.filter_notMem_eq_sdiff]
  · specialize h (t.map (Embedding.subtype _)) (Finset.map_subtype_subset _)
      (fun i => if h : i in s then f ⟨i, h⟩ else 0) ?_ i i.2
    · conv =>
        enter [2, 1, 1]
        rw [← s.subtype_map_of_mem (fun x hx => hx)]; rw [Finset.subtype_eq_univ.2 (fun x hx => hx)]
        change Finset.map (Embedding.subtype (· in (s : Set ι))) _
      rw [← Finset.map_sdiff]
      simpa [Embedding.subtype, ← Finset.compl_eq_univ_sdiff]
    simpa using h

中文:
引理 linearIndepOn_finset_iffₒₛ
  条件: [DecidableEq ι] {s : 有限集 ι}
  证明: by
  rw [LinearIndepOn]; rw [Fintype.linearIndependent_iffₒₛ]
  refine ⟨fun h t ht f heq i hi => h { i | i.1 in t } (f ∘ Subtype.val) ?_ ⟨i, hi⟩,
    fun h t f heq i => ?_⟩
  · simp only [Finset.compl_filter, Finset.sum_filter, Function.comp_apply, Finset.coe_sort_coe]
    rw [Finset.sum_coe_sort s fun i => if i in t then f i • v i else 0]; rw [Finset.sum_coe_sort s fun i => if i ∉ t then f i • v i else 0]
    simpa [Finset.inter_eq_right.2 ht, Finset.sum_ite, Finset.filter_notMem_eq_sdiff]
  · specialize h (t.map (Embedding.subtype _)) (Finset.map_subtype_subset _)
      (fun i => if h : i in s then f ⟨i, h⟩ else 0) ?_ i i.2
    · conv =>
        enter [2, 1, 1]
        rw [← s.subtype_map_of_mem (fun x hx => hx)]; rw [Finset.subtype_eq_univ.2 (fun x hx => hx)]
        change Finset.map (Embedding.subtype (· in (s : Set ι))) _
      rw [← Finset.map_sdiff]
      simpa [Embedding.subtype, ← Finset.compl_eq_univ_sdiff]
    simpa using h

Depends on / 依赖: Finset, Finset.coe_sort_coe, Finset.compl_filter, Finset.filter_notMem_eq_sdiff, Finset.inter_eq_right, Finset.sum_coe_sort, Finset.sum_filter, Finset.sum_ite, Fintype, Fintype.linearIndependent_iff, Function, Function.comp_apply, LinearIndepOn, Subtype, Subtype.val, coe_sort_coe, comp_apply, compl_filter, filter_notMem_eq_sdiff, inter_eq_right
-/
lemma linearIndepOn_finset_iffₒₛ [DecidableEq ι] {s : Finset ι} :
    LinearIndepOn R v s ↔ forall t subseteq s, forall (f : ι -> R),
      ∑ i in t, f i • v i = ∑ i in s \ t, f i • v i -> forall i in s, f i = 0 := by
  rw [LinearIndepOn]; rw [Fintype.linearIndependent_iffₒₛ]
  refine ⟨fun h t ht f heq i hi => h { i | i.1 in t } (f ∘ Subtype.val) ?_ ⟨i, hi⟩,
    fun h t f heq i => ?_⟩
  · simp only [Finset.compl_filter, Finset.sum_filter, Function.comp_apply, Finset.coe_sort_coe]
    rw [Finset.sum_coe_sort s fun i => if i in t then f i • v i else 0]; rw [Finset.sum_coe_sort s fun i => if i ∉ t then f i • v i else 0]
    simpa [Finset.inter_eq_right.2 ht, Finset.sum_ite, Finset.filter_notMem_eq_sdiff]
  · specialize h (t.map (Embedding.subtype _)) (Finset.map_subtype_subset _)
      (fun i => if h : i in s then f ⟨i, h⟩ else 0) ?_ i i.2
    · conv =>
        enter [2, 1, 1]
        rw [← s.subtype_map_of_mem (fun x hx => hx)]; rw [Finset.subtype_eq_univ.2 (fun x hx => hx)]
        change Finset.map (Embedding.subtype (· in (s : Set ι))) _
      rw [← Finset.map_sdiff]
      simpa [Embedding.subtype, ← Finset.compl_eq_univ_sdiff]
    simpa using h

/--
lemma `not_linearIndepOn_finset_iffₒₛ` / 引理 `not_linearIndepOn_finset_iffₒₛ`

English:
lemma not_linearIndepOn_finset_iffₒₛ
  given: [DecidableEq ι] {s : Finset ι}
  proof: by
  simp only [linearIndepOn_finset_iffₒₛ, not_forall, pos_iff_ne_zero]
  refine ⟨fun ⟨t, hst, f, heq, i, hi, hfi⟩ => ?_,
    fun ⟨t, hst, f, heq, i, hi, hfi⟩ => ⟨t, hst, f, heq, i, hst hi, hfi⟩⟩
  by_cases hi' : i in t
  · exact ⟨t, hst, f, heq, i, hi', hfi⟩
  · refine ⟨s \ t, Finset.sdiff_subset, f, ?_, i, Finset.mem_sdiff.2 ⟨hi, hi'⟩, hfi⟩
    simpa [Finset.sdiff_sdiff_eq_self hst] using heq.symm

中文:
引理 not_linearIndepOn_finset_iffₒₛ
  条件: [DecidableEq ι] {s : 有限集 ι}
  证明: by
  simp only [linearIndepOn_finset_iffₒₛ, not_forall, pos_iff_ne_zero]
  refine ⟨fun ⟨t, hst, f, heq, i, hi, hfi⟩ => ?_,
    fun ⟨t, hst, f, heq, i, hi, hfi⟩ => ⟨t, hst, f, heq, i, hst hi, hfi⟩⟩
  by_cases hi' : i in t
  · exact ⟨t, hst, f, heq, i, hi', hfi⟩
  · refine ⟨s \ t, Finset.sdiff_subset, f, ?_, i, Finset.mem_sdiff.2 ⟨hi, hi'⟩, hfi⟩
    simpa [Finset.sdiff_sdiff_eq_self hst] using heq.symm

Depends on / 依赖: Finset, Finset.mem_sdiff, Finset.sdiff_sdiff_eq_self, Finset.sdiff_subset, heq.symm, mem_sdiff, not_forall, pos_iff_ne_zero, sdiff_sdiff_eq_self, sdiff_subset
-/
lemma not_linearIndepOn_finset_iffₒₛ [DecidableEq ι] {s : Finset ι} :
    ¬LinearIndepOn R v s ↔ exists t subseteq s, exists (f : ι -> R),
      ∑ i in t, f i • v i = ∑ i in s \ t, f i • v i ∧ exists i in t, 0 < f i := by
  simp only [linearIndepOn_finset_iffₒₛ, not_forall, pos_iff_ne_zero]
  refine ⟨fun ⟨t, hst, f, heq, i, hi, hfi⟩ => ?_,
    fun ⟨t, hst, f, heq, i, hi, hfi⟩ => ⟨t, hst, f, heq, i, hst hi, hfi⟩⟩
  by_cases hi' : i in t
  · exact ⟨t, hst, f, heq, i, hi', hfi⟩
  · refine ⟨s \ t, Finset.sdiff_subset, f, ?_, i, Finset.mem_sdiff.2 ⟨hi, hi'⟩, hfi⟩
    simpa [Finset.sdiff_sdiff_eq_self hst] using heq.symm

end LinearlyCanonicallyOrdered

end Semiring

/-! ### Properties which require `Ring R` -/

section Module

variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']
variable {v : ι -> M} {i : ι}

/--
theorem `LinearIndependent.neg` / 定理 `LinearIndependent.neg`

English:
theorem LinearIndependent.neg
  given: (hv : LinearIndependent R v)
  statement: LinearIndependent R (-v)
  proof: by
  intro f g h
  simp only [Finsupp.linearCombination_apply, Pi.neg_apply, smul_neg, Finsupp.sum_neg, neg_inj] at h
  ext m
  exact DFunLike.congr_fun (hv h) m

中文:
定理 LinearIndependent.neg
  条件: (hv : LinearIndependent R v)
  结论: LinearIndependent R (-v)
  证明: by
  intro f g h
  simp only [Finsupp.linearCombination_apply, Pi.neg_apply, smul_neg, Finsupp.sum_neg, neg_inj] at h
  ext m
  exact DFunLike.congr_fun (hv h) m

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Finsupp, Finsupp.linearCombination_apply, Finsupp.sum_neg, Pi.neg_apply, congr_fun, linearCombination_apply, neg_apply, neg_inj, smul_neg, sum_neg
-/
theorem LinearIndependent.neg (hv : LinearIndependent R v) : LinearIndependent R (-v) := by
  intro f g h
  simp only [Finsupp.linearCombination_apply, Pi.neg_apply, smul_neg, Finsupp.sum_neg, neg_inj] at h
  ext m
  exact DFunLike.congr_fun (hv h) m

/--
theorem `linearIndependent_neg_iff` / 定理 `linearIndependent_neg_iff`

English:
theorem linearIndependent_neg_iff
  proof: by
  refine ⟨fun h => ?_, LinearIndependent.neg⟩
  simpa using h.neg

中文:
定理 linearIndependent_neg_iff
  证明: by
  refine ⟨fun h => ?_, LinearIndependent.neg⟩
  simpa using h.neg
-/
@[simp] theorem linearIndependent_neg_iff :
    LinearIndependent R (-v) ↔ LinearIndependent R v := by
  refine ⟨fun h => ?_, LinearIndependent.neg⟩
  simpa using h.neg

/--
theorem `linearIndependent_iff_ker` / 定理 `linearIndependent_iff_ker`

English:
theorem linearIndependent_iff_ker
  proof: LinearMap.ker_eq_bot.symm

中文:
定理 linearIndependent_iff_ker
  证明: LinearMap.ker_eq_bot.symm

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot.symm, ker_eq_bot
-/
theorem linearIndependent_iff_ker :
    LinearIndependent R v ↔ LinearMap.ker (Finsupp.linearCombination R v) = ⊥ :=
  LinearMap.ker_eq_bot.symm

/--
theorem `linearIndependent_iff` / 定理 `linearIndependent_iff`

English:
theorem linearIndependent_iff
  proof: by
  simp [linearIndependent_iff_ker, LinearMap.ker_eq_bot']

中文:
定理 linearIndependent_iff
  证明: by
  simp [linearIndependent_iff_ker, LinearMap.ker_eq_bot']

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, ker_eq_bot, linearIndependent_iff_ker
-/
theorem linearIndependent_iff :
    LinearIndependent R v ↔ forall l, Finsupp.linearCombination R v l = 0 -> l = 0 := by
  simp [linearIndependent_iff_ker, LinearMap.ker_eq_bot']

/--
theorem `linearIndependent_iff'` / 定理 `linearIndependent_iff'`

English:
theorem linearIndependent_iff'
  proof: by
  rw [linearIndependent_iff'ₛ]
  refine ⟨fun h s f => ?_, fun h s f g => ?_⟩
  · convert! h s f 0; simp_rw [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  · rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    convert! h s (f - g) using 3; simp only [Pi.sub_apply, sub_smul, sub_eq_zero]

中文:
定理 linearIndependent_iff'
  证明: by
  rw [linearIndependent_iff'ₛ]
  refine ⟨fun h s f => ?_, fun h s f g => ?_⟩
  · convert! h s f 0; simp_rw [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  · rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    convert! h s (f - g) using 3; simp only [Pi.sub_apply, sub_smul, sub_eq_zero]
-/
theorem linearIndependent_iff' :
    LinearIndependent R v ↔
      forall s : Finset ι, forall g : ι -> R, ∑ i in s, g i • v i = 0 -> forall i in s, g i = 0 := by
  rw [linearIndependent_iff'ₛ]
  refine ⟨fun h s f => ?_, fun h s f g => ?_⟩
  · convert! h s f 0; simp_rw [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  · rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    convert! h s (f - g) using 3; simp only [Pi.sub_apply, sub_smul, sub_eq_zero]

/--
theorem `linearIndependent_iff''` / 定理 `linearIndependent_iff''`

English:
theorem linearIndependent_iff''
  proof: by
  classical
  exact linearIndependent_iff'.trans
    ⟨fun H s g hg hv i => if his : i in s then H s g hv i his else hg i his, fun H s g hg i hi => by
      convert!
        H s (fun j => if j in s then g j else 0) (fun j hj => if_neg hj)
          (by simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, hg]) i
      exact (if_pos hi).symm⟩

中文:
定理 linearIndependent_iff''
  证明: by
  classical
  exact linearIndependent_iff'.trans
    ⟨fun H s g hg hv i => if his : i in s then H s g hv i his else hg i his, fun H s g hg i hi => by
      convert!
        H s (fun j => if j in s then g j else 0) (fun j hj => if_neg hj)
          (by simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, hg]) i
      exact (if_pos hi).symm⟩
-/
theorem linearIndependent_iff'' :
    LinearIndependent R v ↔
      forall (s : Finset ι) (g : ι -> R), (forall i ∉ s, g i = 0) -> ∑ i in s, g i • v i = 0 -> forall i, g i = 0 := by
  classical
  exact linearIndependent_iff'.trans
    ⟨fun H s g hg hv i => if his : i in s then H s g hv i his else hg i his, fun H s g hg i hi => by
      convert!
        H s (fun j => if j in s then g j else 0) (fun j hj => if_neg hj)
          (by simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, hg]) i
      exact (if_pos hi).symm⟩

/--
theorem `linearIndependent_add_smul_iff` / 定理 `linearIndependent_add_smul_iff`

English:
theorem linearIndependent_add_smul_iff
  given: {c : ι -> R} {i : ι} (h₀ : c i = 0)
  proof: by
  simp [linearIndependent_iff_injective_finsuppLinearCombination,
    ← Finsupp.linearCombination_comp_addSingleEquiv i c h₀]

中文:
定理 linearIndependent_add_smul_iff
  条件: {c : ι -> R} {i : ι} (h₀ : c i = 0)
  证明: by
  simp [linearIndependent_iff_injective_finsuppLinearCombination,
    ← Finsupp.linearCombination_comp_addSingleEquiv i c h₀]

Depends on / 依赖: Finsupp, Finsupp.linearCombination_comp_addSingleEquiv, linearCombination_comp_addSingleEquiv, linearIndependent_iff_injective_finsuppLinearCombination
-/
theorem linearIndependent_add_smul_iff {c : ι -> R} {i : ι} (h₀ : c i = 0) :
    LinearIndependent R (v + (c · • v i)) ↔ LinearIndependent R v := by
  simp [linearIndependent_iff_injective_finsuppLinearCombination,
    ← Finsupp.linearCombination_comp_addSingleEquiv i c h₀]

/--
theorem `not_linearIndependent_iff_linearCombination` / 定理 `not_linearIndependent_iff_linearCombination`

English:
theorem not_linearIndependent_iff_linearCombination
  proof: by
  simp [linearIndependent_iff_ker, LinearMap.ker_eq_bot']

中文:
定理 not_linearIndependent_iff_linearCombination
  证明: by
  simp [linearIndependent_iff_ker, LinearMap.ker_eq_bot']

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, ker_eq_bot, linearIndependent_iff_ker
-/
theorem not_linearIndependent_iff_linearCombination :
    ¬LinearIndependent R v ↔ exists l, (Finsupp.linearCombination R v) l = 0 ∧ l != 0 := by
  simp [linearIndependent_iff_ker, LinearMap.ker_eq_bot']

/--
theorem `not_linearIndependent_iff_finsupp` / 定理 `not_linearIndependent_iff_finsupp`

English:
theorem not_linearIndependent_iff_finsupp
  proof: by
  simp [linearIndependent_iff_ker, LinearMap.ker_eq_bot', Finsupp.linearCombination]

中文:
定理 not_linearIndependent_iff_finsupp
  证明: by
  simp [linearIndependent_iff_ker, LinearMap.ker_eq_bot', Finsupp.linearCombination]

Depends on / 依赖: Finsupp, Finsupp.linearCombination, LinearMap, LinearMap.ker_eq_bot, ker_eq_bot, linearCombination, linearIndependent_iff_ker
-/
theorem not_linearIndependent_iff_finsupp :
    ¬LinearIndependent R v ↔ exists (f : ι ->₀ R), f.sum (fun x r => r • v x) = 0 ∧ f != 0 := by
  simp [linearIndependent_iff_ker, LinearMap.ker_eq_bot', Finsupp.linearCombination]

/--
theorem `not_linearIndependent_iff` / 定理 `not_linearIndependent_iff`

English:
theorem not_linearIndependent_iff
  proof: by
  rw [linearIndependent_iff']
  simp only [exists_prop, not_forall]

中文:
定理 not_linearIndependent_iff
  证明: by
  rw [linearIndependent_iff']
  simp only [exists_prop, not_forall]

Depends on / 依赖: exists_prop, linearIndependent_iff, not_forall
-/
theorem not_linearIndependent_iff :
    ¬LinearIndependent R v ↔
      exists s : Finset ι, exists g : ι -> R, ∑ i in s, g i • v i = 0 ∧ exists i in s, g i != 0 := by
  rw [linearIndependent_iff']
  simp only [exists_prop, not_forall]

/--
theorem `Fintype.linearIndependent_iff` / 定理 `Fintype.linearIndependent_iff`

English:
theorem Fintype.linearIndependent_iff
  given: [Fintype ι]
  proof: by
  refine
    ⟨fun H g => by simpa using linearIndependent_iff'.1 H Finset.univ g, fun H =>
      linearIndependent_iff''.2 fun s g hg hs i => H _ ?_ _⟩
  rw [← hs]
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
  rw [hg i hi]; rw [zero_smul]

中文:
定理 有限类型.linearIndependent_iff
  条件: [有限类型 ι]
  证明: by
  refine
    ⟨fun H g => by simpa using linearIndependent_iff'.1 H Finset.univ g, fun H =>
      linearIndependent_iff''.2 fun s g hg hs i => H _ ?_ _⟩
  rw [← hs]
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
  rw [hg i hi]; rw [zero_smul]

Depends on / 依赖: Finset, Finset.subset_univ, Finset.sum_subset, Finset.univ, linearIndependent_iff, subset_univ, sum_subset, zero_smul
-/
theorem Fintype.linearIndependent_iff [Fintype ι] :
    LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g i = 0 := by
  refine
    ⟨fun H g => by simpa using linearIndependent_iff'.1 H Finset.univ g, fun H =>
      linearIndependent_iff''.2 fun s g hg hs i => H _ ?_ _⟩
  rw [← hs]
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
  rw [hg i hi]; rw [zero_smul]

/--
theorem `Fintype.not_linearIndependent_iff` / 定理 `Fintype.not_linearIndependent_iff`

English:
theorem Fintype.not_linearIndependent_iff
  given: [Fintype ι]
  proof: by
  simpa using not_iff_not.2 Fintype.linearIndependent_iff

中文:
定理 有限类型.not_linearIndependent_iff
  条件: [有限类型 ι]
  证明: by
  simpa using not_iff_not.2 Fintype.linearIndependent_iff

Depends on / 依赖: Fintype, Fintype.linearIndependent_iff, linearIndependent_iff, not_iff_not
-/
theorem Fintype.not_linearIndependent_iff [Fintype ι] :
    ¬LinearIndependent R v ↔ exists g : ι -> R, ∑ i, g i • v i = 0 ∧ exists i, g i != 0 := by
  simpa using not_iff_not.2 Fintype.linearIndependent_iff

/--
lemma `linearIndepOn_finset_iff` / 引理 `linearIndepOn_finset_iff`

English:
lemma linearIndepOn_finset_iff
  given: {s : Finset ι}
  proof: by
  classical
  simp_rw [LinearIndepOn, Fintype.linearIndependent_iff]
  constructor
  · rintro hv f hf i hi
    rw [← s.sum_attach] at hf
    exact hv (f ∘ Subtype.val) hf ⟨i, hi⟩
  · rintro hv f hf₀ i
    simpa using hv (fun j => if hj : j in s then f ⟨j, hj⟩ else 0)
      (by simpa +contextual [← s.sum_attach]) i

中文:
引理 linearIndepOn_finset_iff
  条件: {s : 有限集 ι}
  证明: by
  classical
  simp_rw [LinearIndepOn, Fintype.linearIndependent_iff]
  constructor
  · rintro hv f hf i hi
    rw [← s.sum_attach] at hf
    exact hv (f ∘ Subtype.val) hf ⟨i, hi⟩
  · rintro hv f hf₀ i
    simpa using hv (fun j => if hj : j in s then f ⟨j, hj⟩ else 0)
      (by simpa +contextual [← s.sum_attach]) i

Depends on / 依赖: Fintype, Fintype.linearIndependent_iff, LinearIndepOn, Subtype, Subtype.val, classical, contextual, linearIndependent_iff, s.sum_attach, simp_rw, sum_attach
-/
lemma linearIndepOn_finset_iff {s : Finset ι} :
    LinearIndepOn R v s ↔ forall f : ι -> R, ∑ i in s, f i • v i = 0 -> forall i in s, f i = 0 := by
  classical
  simp_rw [LinearIndepOn, Fintype.linearIndependent_iff]
  constructor
  · rintro hv f hf i hi
    rw [← s.sum_attach] at hf
    exact hv (f ∘ Subtype.val) hf ⟨i, hi⟩
  · rintro hv f hf₀ i
    simpa using hv (fun j => if hj : j in s then f ⟨j, hj⟩ else 0)
      (by simpa +contextual [← s.sum_attach]) i

/--
lemma `not_linearIndepOn_finset_iff` / 引理 `not_linearIndepOn_finset_iff`

English:
lemma not_linearIndepOn_finset_iff
  given: {s : Finset ι}
  proof: by
  simpa using linearIndepOn_finset_iff.not

中文:
引理 not_linearIndepOn_finset_iff
  条件: {s : 有限集 ι}
  证明: by
  simpa using linearIndepOn_finset_iff.not

Depends on / 依赖: linearIndepOn_finset_iff, linearIndepOn_finset_iff.not
-/
lemma not_linearIndepOn_finset_iff {s : Finset ι} :
    ¬LinearIndepOn R v s ↔ exists f : ι -> R, ∑ i in s, f i • v i = 0 ∧ exists i in s, f i != 0 := by
  simpa using linearIndepOn_finset_iff.not

/--
theorem `LinearMap.linearIndependent_iff_of_disjoint` / 定理 `LinearMap.linearIndependent_iff_of_disjoint`

English:
theorem LinearMap.linearIndependent_iff_of_disjoint
  statement: (f : M ->ₗ[R] M')
  proof: f.linearIndependent_iff_of_injOn LinearMap.injOn_of_disjoint_ker le_rfl hf_inj

中文:
定理 线性映射.linearIndependent_iff_of_disjoint
  结论: (f : M ->ₗ[R] M')
  证明: f.linearIndependent_iff_of_injOn LinearMap.injOn_of_disjoint_ker le_rfl hf_inj
-/
protected theorem LinearMap.linearIndependent_iff_of_disjoint (f : M ->ₗ[R] M')
    (hf_inj : Disjoint (span R (Set.range v)) (LinearMap.ker f)) :
    LinearIndependent R (f ∘ v) ↔ LinearIndependent R v :=
f.linearIndependent_iff_of_injOn LinearMap.injOn_of_disjoint_ker le_rfl hf_inj

section LinearIndepOn


/--
theorem `linearIndepOn_iff` / 定理 `linearIndepOn_iff`

English:
theorem linearIndepOn_iff
  statement: LinearIndepOn R v s ↔
  proof: linearIndepOn_iffₛ.trans ⟨fun h l hl => h l hl 0 (zero_mem _), fun h f hf g hg eq =>
    sub_eq_zero.mp (h (f - g) (sub_mem hf hg) <| by rw [map_sub, eq, sub_self])⟩

中文:
定理 linearIndepOn_iff
  结论: LinearIndepOn R v s ↔
  证明: linearIndepOn_iffₛ.trans ⟨fun h l hl => h l hl 0 (zero_mem _), fun h f hf g hg eq =>
    sub_eq_zero.mp (h (f - g) (sub_mem hf hg) <| by rw [map_sub, eq, sub_self])⟩

Depends on / 依赖: map_sub, sub_eq_zero, sub_eq_zero.mp, sub_mem, sub_self, zero_mem
-/
theorem linearIndepOn_iff : LinearIndepOn R v s ↔
      forall l in Finsupp.supported R R s, (Finsupp.linearCombination R v) l = 0 -> l = 0 :=
  linearIndepOn_iffₛ.trans ⟨fun h l hl => h l hl 0 (zero_mem _), fun h f hf g hg eq =>
    sub_eq_zero.mp (h (f - g) (sub_mem hf hg) <| by rw [map_sub, eq, sub_self])⟩

/--
theorem `linearDepOn_iff'` / 定理 `linearDepOn_iff'`

English:
theorem linearDepOn_iff'
  statement: ¬LinearIndepOn R v s ↔
  proof: by
  simp [linearIndepOn_iff]

中文:
定理 linearDepOn_iff'
  结论: ¬LinearIndepOn R v s ↔
  证明: by
  simp [linearIndepOn_iff]
-/
theorem linearDepOn_iff' : ¬LinearIndepOn R v s ↔
      exists f : ι ->₀ R, f in Finsupp.supported R R s ∧ Finsupp.linearCombination R v f = 0 ∧ f != 0 := by
  simp [linearIndepOn_iff]

/--
theorem `linearDepOn_iff` / 定理 `linearDepOn_iff`

English:
theorem linearDepOn_iff
  statement: ¬LinearIndepOn R v s ↔
  proof: linearDepOn_iff'

中文:
定理 linearDepOn_iff
  结论: ¬LinearIndepOn R v s ↔
  证明: linearDepOn_iff'

Depends on / 依赖: linearDepOn_iff
-/
theorem linearDepOn_iff : ¬LinearIndepOn R v s ↔
      exists f : ι ->₀ R, f in Finsupp.supported R R s ∧ ∑ i in f.support, f i • v i = 0 ∧ f != 0 :=
  linearDepOn_iff'

/--
theorem `linearIndepOn_iff_disjoint` / 定理 `linearIndepOn_iff_disjoint`

English:
theorem linearIndepOn_iff_disjoint
  statement: LinearIndepOn R v s ↔
  proof: by
  rw [linearIndepOn_iff]; rw [LinearMap.disjoint_ker]

中文:
定理 linearIndepOn_iff_disjoint
  结论: LinearIndepOn R v s ↔
  证明: by
  rw [linearIndepOn_iff]; rw [LinearMap.disjoint_ker]

Depends on / 依赖: LinearMap, LinearMap.disjoint_ker, disjoint_ker, linearIndepOn_iff
-/
theorem linearIndepOn_iff_disjoint : LinearIndepOn R v s ↔
      Disjoint (Finsupp.supported R R s) (LinearMap.ker <| Finsupp.linearCombination R v) := by
  rw [linearIndepOn_iff]; rw [LinearMap.disjoint_ker]

/--
theorem `linearIndepOn_iff_linearCombinationOn` / 定理 `linearIndepOn_iff_linearCombinationOn`

English:
theorem linearIndepOn_iff_linearCombinationOn
  proof: linearIndepOn_iff_linearCombinationOnₛ.trans
    LinearMap.ker_eq_bot (M := Finsupp.supported R R s).symm

中文:
定理 linearIndepOn_iff_linearCombinationOn
  证明: linearIndepOn_iff_linearCombinationOnₛ.trans
    LinearMap.ker_eq_bot (M := Finsupp.supported R R s).symm

Depends on / 依赖: Finsupp, Finsupp.supported, LinearMap, LinearMap.ker_eq_bot, ker_eq_bot, supported
-/
theorem linearIndepOn_iff_linearCombinationOn :
    LinearIndepOn R v s ↔ (LinearMap.ker <| Finsupp.linearCombinationOn ι M R v s) = ⊥ :=
linearIndepOn_iff_linearCombinationOnₛ.trans
    LinearMap.ker_eq_bot (M := Finsupp.supported R R s).symm

/--
lemma `linearIndepOn_iff'` / 引理 `linearIndepOn_iff'`

English:
lemma linearIndepOn_iff'
  statement: LinearIndepOn R v s ↔ forall (t : Finset ι) (g : ι -> R), (t : Set ι) subseteq s ->
  proof: by
  classical
  rw [LinearIndepOn]; rw [linearIndependent_iff']
  refine ⟨fun h t g hts h0 i hit => ?_, fun h t g h0 i hit => ?_⟩
  · refine h (t.preimage _ Subtype.val_injective.injOn) (fun i => g i) ?_ ⟨i, hts hit⟩ (by simpa)
    rwa [t.sum_preimage ((↑) : s -> ι) Subtype.val_injective.injOn (fun i => g i • v i)]
    simp only [Subtype.range_coe_subtype, ofPred_mem_eq]
.elim exact fun x hxt hxs => (hxs (hts hxt))
  replace h : forall i (hi : i in s), ⟨i, hi⟩ in t -> forall (h : i in s), g ⟨i, h⟩ = 0 := by
    simpa [h0] using h (t.image (↑)) (fun i => if hi : i in s then g ⟨i, hi⟩ else 0)
  apply h _ _ hit

中文:
引理 linearIndepOn_iff'
  结论: LinearIndepOn R v s ↔ 对任意 (t : 有限集 ι) (g : ι -> R), (t : 集合 ι) subseteq s ->
  证明: by
  classical
  rw [LinearIndepOn]; rw [linearIndependent_iff']
  refine ⟨fun h t g hts h0 i hit => ?_, fun h t g h0 i hit => ?_⟩
  · refine h (t.preimage _ Subtype.val_injective.injOn) (fun i => g i) ?_ ⟨i, hts hit⟩ (by simpa)
    rwa [t.sum_preimage ((↑) : s -> ι) Subtype.val_injective.injOn (fun i => g i • v i)]
    simp only [Subtype.range_coe_subtype, ofPred_mem_eq]
.elim exact fun x hxt hxs => (hxs (hts hxt))
  replace h : forall i (hi : i in s), ⟨i, hi⟩ in t -> forall (h : i in s), g ⟨i, h⟩ = 0 := by
    simpa [h0] using h (t.image (↑)) (fun i => if hi : i in s then g ⟨i, hi⟩ else 0)
  apply h _ _ hit

Depends on / 依赖: LinearIndepOn, Subtype, Subtype.range_coe_subtype, Subtype.val_injective.injOn, classical, linearIndependent_iff, ofPred_mem_eq, preimage, range_coe_subtype, replace, sum_preimage, t.preimage, t.sum_preimage, val_injective
-/
lemma linearIndepOn_iff' : LinearIndepOn R v s ↔ forall (t : Finset ι) (g : ι -> R), (t : Set ι) subseteq s ->
    ∑ i in t, g i • v i = 0 -> forall i in t, g i = 0 := by
  classical
  rw [LinearIndepOn]; rw [linearIndependent_iff']
  refine ⟨fun h t g hts h0 i hit => ?_, fun h t g h0 i hit => ?_⟩
  · refine h (t.preimage _ Subtype.val_injective.injOn) (fun i => g i) ?_ ⟨i, hts hit⟩ (by simpa)
    rwa [t.sum_preimage ((↑) : s -> ι) Subtype.val_injective.injOn (fun i => g i • v i)]
    simp only [Subtype.range_coe_subtype, ofPred_mem_eq]
.elim exact fun x hxt hxs => (hxs (hts hxt))
  replace h : forall i (hi : i in s), ⟨i, hi⟩ in t -> forall (h : i in s), g ⟨i, h⟩ = 0 := by
    simpa [h0] using h (t.image (↑)) (fun i => if hi : i in s then g ⟨i, hi⟩ else 0)
  apply h _ _ hit

/--
lemma `linearIndepOn_iff''` / 引理 `linearIndepOn_iff''`

English:
lemma linearIndepOn_iff''
  statement: LinearIndepOn R v s ↔ forall (t : Finset ι) (g : ι -> R), (t : Set ι) subseteq s ->
  proof: by
  classical
  exact linearIndepOn_iff'.trans ⟨fun h t g hts htg h0 => h _ _ hts h0, fun h t g hts h0 =>
    by simpa +contextual [h0] using h t (fun i => if i in t then g i else 0) hts⟩

中文:
引理 linearIndepOn_iff''
  结论: LinearIndepOn R v s ↔ 对任意 (t : 有限集 ι) (g : ι -> R), (t : 集合 ι) subseteq s ->
  证明: by
  classical
  exact linearIndepOn_iff'.trans ⟨fun h t g hts htg h0 => h _ _ hts h0, fun h t g hts h0 =>
    by simpa +contextual [h0] using h t (fun i => if i in t then g i else 0) hts⟩

Depends on / 依赖: classical, contextual, linearIndepOn_iff
-/
lemma linearIndepOn_iff'' : LinearIndepOn R v s ↔ forall (t : Finset ι) (g : ι -> R), (t : Set ι) subseteq s ->
    (forall i ∉ t, g i = 0) -> ∑ i in t, g i • v i = 0 -> forall i in t, g i = 0 := by
  classical
  exact linearIndepOn_iff'.trans ⟨fun h t g hts htg h0 => h _ _ hts h0, fun h t g hts h0 =>
    by simpa +contextual [h0] using h t (fun i => if i in t then g i else 0) hts⟩

end LinearIndepOn

open LinearMap

/--
theorem `linearIndependent_iff_eq_zero_of_smul_mem_span` / 定理 `linearIndependent_iff_eq_zero_of_smul_mem_span`

English:
theorem linearIndependent_iff_eq_zero_of_smul_mem_span
  proof: ⟨fun hv => hv.eq_zero_of_smul_mem_span, fun H =>
    linearIndependent_iff.2 fun l hl => by
      ext i; simp only [Finsupp.zero_apply]
      by_contra hn
      refine hn (H i _ ?_)
      refine (Finsupp.mem_span_image_iff_linearCombination R).2 ⟨Finsupp.single i (l i) - l, ?_, ?_⟩
      · rw [Finsupp.mem_supported']
        intro j hj
        have hij : j = i :=
          Classical.not_not.1 fun hij : j != i =>
            hj ((mem_sdiff _).2 ⟨mem_univ _, fun h => hij (eq_of_mem_singleton h)⟩)
        simp [hij]
      · simp [hl]⟩

中文:
定理 linearIndependent_iff_eq_zero_of_smul_mem_span
  证明: ⟨fun hv => hv.eq_zero_of_smul_mem_span, fun H =>
    linearIndependent_iff.2 fun l hl => by
      ext i; simp only [Finsupp.zero_apply]
      by_contra hn
      refine hn (H i _ ?_)
      refine (Finsupp.mem_span_image_iff_linearCombination R).2 ⟨Finsupp.single i (l i) - l, ?_, ?_⟩
      · rw [Finsupp.mem_supported']
        intro j hj
        have hij : j = i :=
          Classical.not_not.1 fun hij : j != i =>
            hj ((mem_sdiff _).2 ⟨mem_univ _, fun h => hij (eq_of_mem_singleton h)⟩)
        simp [hij]
      · simp [hl]⟩

Depends on / 依赖: Classical, Classical.not_not, Finsupp, Finsupp.mem_span_image_iff_linearCombination, Finsupp.mem_supported, Finsupp.single, Finsupp.zero_apply, eq_of_mem_singleton, eq_zero_of_smul_mem_span, hv.eq_zero_of_smul_mem_span, linearIndependent_iff, mem_sdiff, mem_span_image_iff_linearCombination, mem_supported, mem_univ, not_not, single, zero_apply
-/
theorem linearIndependent_iff_eq_zero_of_smul_mem_span :
    LinearIndependent R v ↔ forall (i : ι) (a : R), a • v i in span R (v '' (univ \ {i})) -> a = 0 :=
  ⟨fun hv => hv.eq_zero_of_smul_mem_span, fun H =>
    linearIndependent_iff.2 fun l hl => by
      ext i; simp only [Finsupp.zero_apply]
      by_contra hn
      refine hn (H i _ ?_)
      refine (Finsupp.mem_span_image_iff_linearCombination R).2 ⟨Finsupp.single i (l i) - l, ?_, ?_⟩
      · rw [Finsupp.mem_supported']
        intro j hj
        have hij : j = i :=
          Classical.not_not.1 fun hij : j != i =>
            hj ((mem_sdiff _).2 ⟨mem_univ _, fun h => hij (eq_of_mem_singleton h)⟩)
        simp [hij]
      · simp [hl]⟩

/--
lemma `LinearIndependent.of_subsingleton'` / 引理 `LinearIndependent.of_subsingleton'`

English:
lemma LinearIndependent.of_subsingleton'
  statement: [Subsingleton ι] (i : ι)
  proof: by
  let := uniqueOfSubsingleton i
  simpa [linearIndependent_iff, Finsupp.linearCombination_unique, Finsupp.ext_iff,
    Unique.forall_iff] using! fun _ => hi _

中文:
引理 LinearIndependent.of_subsingleton'
  结论: [子单例 ι] (i : ι)
  证明: by
  let := uniqueOfSubsingleton i
  simpa [linearIndependent_iff, Finsupp.linearCombination_unique, Finsupp.ext_iff,
    Unique.forall_iff] using! fun _ => hi _

Depends on / 依赖: Finsupp, Finsupp.ext_iff, Finsupp.linearCombination_unique, Unique, Unique.forall_iff, ext_iff, forall_iff, linearCombination_unique, linearIndependent_iff, uniqueOfSubsingleton
-/
lemma LinearIndependent.of_subsingleton' [Subsingleton ι] (i : ι)
    (hi : forall r : R, r • v i = 0 -> r = 0) : LinearIndependent R v := by
  let := uniqueOfSubsingleton i
  simpa [linearIndependent_iff, Finsupp.linearCombination_unique, Finsupp.ext_iff,
    Unique.forall_iff] using! fun _ => hi _

/-- Version of `LinearIndepOn.singleton` that works for the zero ring. -/
@[simp]
/--
lemma `LinearIndepOn.singleton'` / 引理 `LinearIndepOn.singleton'`

English:
lemma LinearIndepOn.singleton'
  given: (hi : forall r : R, r • v i = 0 -> r = 0)
  statement: LinearIndepOn R v {i}
  proof: LinearIndependent.of_subsingleton' ⟨i, rfl⟩ hi

中文:
引理 LinearIndepOn.singleton'
  条件: (hi : 对任意 r : R, r • v i = 0 -> r = 0)
  结论: LinearIndepOn R v {i}
  证明: LinearIndependent.of_subsingleton' ⟨i, rfl⟩ hi

Depends on / 依赖: LinearIndependent, LinearIndependent.of_subsingleton, of_subsingleton
-/
lemma LinearIndepOn.singleton' (hi : forall r : R, r • v i = 0 -> r = 0) : LinearIndepOn R v {i} :=
  LinearIndependent.of_subsingleton' ⟨i, rfl⟩ hi

variable [IsDomain R] [IsTorsionFree R M]

/--
lemma `LinearIndependent.of_subsingleton` / 引理 `LinearIndependent.of_subsingleton`

English:
lemma LinearIndependent.of_subsingleton
  given: [Subsingleton ι] (i : ι) (hi : v i != 0)
  proof: .of_subsingleton' i (by simp [hi])

中文:
引理 LinearIndependent.of_subsingleton
  条件: [子单例 ι] (i : ι) (hi : v i != 0)
  证明: .of_subsingleton' i (by simp [hi])

Depends on / 依赖: of_subsingleton
-/
lemma LinearIndependent.of_subsingleton [Subsingleton ι] (i : ι) (hi : v i != 0) :
    LinearIndependent R v := .of_subsingleton' i (by simp [hi])

/--
lemma `LinearIndepOn.singleton` / 引理 `LinearIndepOn.singleton`

English:
lemma LinearIndepOn.singleton
  given: (hi : v i != 0)
  statement: LinearIndepOn R v {i}
  proof: by simp [hi]

中文:
引理 LinearIndepOn.singleton
  条件: (hi : v i != 0)
  结论: LinearIndepOn R v {i}
  证明: by simp [hi]
-/
lemma LinearIndepOn.singleton (hi : v i != 0) : LinearIndepOn R v {i} := by simp [hi]

end Module

/-!
### Properties which require `DivisionRing K`

These can be considered generalizations of properties of linear independence in vector spaces.
-/


section Module

variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable {v : ι -> V} {s t : Set ι} {x y : V}

open Submodule

/--
theorem `linearIndependent_iff_notMem_span` / 定理 `linearIndependent_iff_notMem_span`

English:
theorem linearIndependent_iff_notMem_span
  proof: by
  apply linearIndependent_iff_eq_zero_of_smul_mem_span.trans
  constructor
  · intro h i h_in_span
    apply one_ne_zero (h i 1 (by simp [h_in_span]))
  · intro h i a ha
    by_contra ha'
    exact False.elim (h _ ((smul_mem_iff _ ha').1 ha))

中文:
定理 linearIndependent_iff_notMem_span
  证明: by
  apply linearIndependent_iff_eq_zero_of_smul_mem_span.trans
  constructor
  · intro h i h_in_span
    apply one_ne_zero (h i 1 (by simp [h_in_span]))
  · intro h i a ha
    by_contra ha'
    exact False.elim (h _ ((smul_mem_iff _ ha').1 ha))

Depends on / 依赖: False.elim, h_in_span, linearIndependent_iff_eq_zero_of_smul_mem_span, linearIndependent_iff_eq_zero_of_smul_mem_span.trans, one_ne_zero, smul_mem_iff
-/
theorem linearIndependent_iff_notMem_span :
    LinearIndependent K v ↔ forall i, v i ∉ span K (v '' (univ \ {i})) := by
  apply linearIndependent_iff_eq_zero_of_smul_mem_span.trans
  constructor
  · intro h i h_in_span
    apply one_ne_zero (h i 1 (by simp [h_in_span]))
  · intro h i a ha
    by_contra ha'
    exact False.elim (h _ ((smul_mem_iff _ ha').1 ha))

/--
lemma `linearIndepOn_iff_notMem_span` / 引理 `linearIndepOn_iff_notMem_span`

English:
lemma linearIndepOn_iff_notMem_span
  proof: by
  rw [LinearIndepOn]; rw [linearIndependent_iff_notMem_span]; rw [← Function.comp_def]
  simp_rw [Set.image_comp]
  simp [Set.image_sdiff Subtype.val_injective]

中文:
引理 linearIndepOn_iff_notMem_span
  证明: by
  rw [LinearIndepOn]; rw [linearIndependent_iff_notMem_span]; rw [← Function.comp_def]
  simp_rw [Set.image_comp]
  simp [Set.image_sdiff Subtype.val_injective]

Depends on / 依赖: Function, Function.comp_def, LinearIndepOn, Set.image_comp, Set.image_sdiff, Subtype, Subtype.val_injective, comp_def, image_comp, image_sdiff, linearIndependent_iff_notMem_span, simp_rw, val_injective
-/
lemma linearIndepOn_iff_notMem_span :
    LinearIndepOn K v s ↔ forall i in s, v i ∉ span K (v '' (s \ {i})) := by
  rw [LinearIndepOn]; rw [linearIndependent_iff_notMem_span]; rw [← Function.comp_def]
  simp_rw [Set.image_comp]
  simp [Set.image_sdiff Subtype.val_injective]

end Module
