/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Data.Set.Restrict
public import Mathlib.Util.Delaborators

/-!
# Functions depending only on some variables

When dealing with a function `f : Π i, α i` depending on many variables, some operations
may get rid of the dependency on some variables (see `Function.updateFinset` or
`MeasureTheory.lmarginal` for example). However considering this new function
as having a different domain with fewer points is not comfortable in Lean, as it requires the use
of subtypes and can lead to tedious writing.

On the other hand one wants to be able for example to describe some function as constant
with respect to some variables, and be able to deduce this when applying transformations
mentioned above. This is why we introduce the predicate `DependsOn f s`, which states that
if `x` and `y` coincide over the set `s`, then `f x = f y`.
This is equivalent to `Function.FactorsThrough f s.domRestrict`.

## Main definition

* `DependsOn f s`: If `x` and `y` coincide over the set `s`, then `f x` equals `f y`.

## Main statement

* `dependsOn_iff_factorsThrough`: A function `f` depends on `s` if and only if it factors
  through `s.domRestrict`.

## Implementation notes

When we write `DependsOn f s`, i.e. `f` only depends on `s`, it should be interpreted as
"`f` _potentially_ depends only on variables in `s`". However it might be the case
that `f` does not depend at all on variables in `s`, for example if `f` is constant.
As a consequence, `DependsOn f univ` is always true, see `dependsOn_univ`.

The predicate `DependsOn f s` can also be interpreted as saying that `f` is independent of all
the variables which are not in `s`. Although this phrasing might seem more natural, we choose to go
with `DependsOn` because writing mathematically "independent of variables in `s`" would boil down to
`∀ x y, (∀ i ∉ s, x i = y i) → f x = f y`, which is the same as `DependsOn f sᶜ`.

## Tags

depends on
-/

@[expose] public section

open Function Set

variable {ι : Type*} {α : ι -> Type*} {β : Type*}

/--
Definition of `DependsOn` / `DependsOn` 的定义

English:
definition DependsOn
  signature: (f : (Π i, α i) -> β) (s : Set ι)
  body: forall ⦃x y⦄, (forall i in s, x i = y i) -> f x = f y

中文:
定义 DependsOn
  签名: (f : (Π i, α i) -> β) (s : 集合 ι)
  定义体: forall ⦃x y⦄, (forall i in s, x i = y i) -> f x = f y
-/
def DependsOn (f : (Π i, α i) -> β) (s : Set ι) : Prop :=
  forall ⦃x y⦄, (forall i in s, x i = y i) -> f x = f y

/--
lemma `dependsOn_iff_factorsThrough` / 引理 `dependsOn_iff_factorsThrough`

English:
lemma dependsOn_iff_factorsThrough
  given: {f : (Π i, α i) -> β} {s : Set ι}
  proof: by
  rw [DependsOn]; rw [FactorsThrough]
  simp [funext_iff]

中文:
引理 dependsOn_iff_factorsThrough
  条件: {f : (Π i, α i) -> β} {s : 集合 ι}
  证明: by
  rw [DependsOn]; rw [FactorsThrough]
  simp [funext_iff]

Depends on / 依赖: DependsOn, FactorsThrough, funext_iff
-/
lemma dependsOn_iff_factorsThrough {f : (Π i, α i) -> β} {s : Set ι} :
    DependsOn f s ↔ FactorsThrough f s.domRestrict := by
  rw [DependsOn]; rw [FactorsThrough]
  simp [funext_iff]

/--
lemma `dependsOn_iff_exists_comp` / 引理 `dependsOn_iff_exists_comp`

English:
lemma dependsOn_iff_exists_comp
  given: [Nonempty β] {f : (Π i, α i) -> β} {s : Set ι}
  proof: by
  rw [dependsOn_iff_factorsThrough]; rw [factorsThrough_iff]

中文:
引理 dependsOn_iff_存在_comp
  条件: [非空 β] {f : (Π i, α i) -> β} {s : 集合 ι}
  证明: by
  rw [dependsOn_iff_factorsThrough]; rw [factorsThrough_iff]

Depends on / 依赖: dependsOn_iff_factorsThrough, factorsThrough_iff
-/
lemma dependsOn_iff_exists_comp [Nonempty β] {f : (Π i, α i) -> β} {s : Set ι} :
    DependsOn f s ↔ exists g : (Π i : s, α i) -> β, f = g ∘ s.domRestrict := by
  rw [dependsOn_iff_factorsThrough]; rw [factorsThrough_iff]

/--
lemma `dependsOn_univ` / 引理 `dependsOn_univ`

English:
lemma dependsOn_univ
  given: (f : (Π i, α i) -> β)
  statement: DependsOn f univ
  proof: fun _ _ h => congrArg _ funext fun i => h i trivial

中文:
引理 dependsOn_univ
  条件: (f : (Π i, α i) -> β)
  结论: DependsOn f univ
  证明: fun _ _ h => congrArg _ funext fun i => h i trivial
-/
lemma dependsOn_univ (f : (Π i, α i) -> β) : DependsOn f univ :=
fun _ _ h => congrArg _ funext fun i => h i trivial

variable {f : (Π i, α i) -> β}

/--
lemma `dependsOn_const` / 引理 `dependsOn_const`

English:
lemma dependsOn_const
  given: (b : β)
  statement: DependsOn (fun _ : Π i, α i => b) ∅
  proof: by simp [DependsOn]

中文:
引理 dependsOn_const
  条件: (b : β)
  结论: DependsOn (fun _ : Π i, α i => b) ∅
  证明: by simp [DependsOn]

Depends on / 依赖: DependsOn
-/
lemma dependsOn_const (b : β) : DependsOn (fun _ : Π i, α i => b) ∅ := by simp [DependsOn]

/--
lemma `DependsOn.mono` / 引理 `DependsOn.mono`

English:
lemma DependsOn.mono
  given: {s t : Set ι} (hst : s subseteq t) (hf : DependsOn f s)
  statement: DependsOn f t
  proof: fun _ _ h => hf fun i hi => h i (hst hi)

中文:
引理 DependsOn.mono
  条件: {s t : 集合 ι} (hst : s subseteq t) (hf : DependsOn f s)
  结论: DependsOn f t
  证明: fun _ _ h => hf fun i hi => h i (hst hi)
-/
lemma DependsOn.mono {s t : Set ι} (hst : s subseteq t) (hf : DependsOn f s) : DependsOn f t :=
  fun _ _ h => hf fun i hi => h i (hst hi)

/--
lemma `DependsOn.empty` / 引理 `DependsOn.empty`

English:
lemma DependsOn.empty
  given: (hf : DependsOn f ∅) (x y : Π i, α i)
  statement: f x = f y
  proof: hf (by simp)

中文:
引理 DependsOn.empty
  条件: (hf : DependsOn f ∅) (x y : Π i, α i)
  结论: f x = f y
  证明: hf (by simp)
-/
lemma DependsOn.empty (hf : DependsOn f ∅) (x y : Π i, α i) : f x = f y := hf (by simp)

/--
lemma `Set.dependsOn_domRestrict` / 引理 `Set.dependsOn_domRestrict`

English:
lemma Set.dependsOn_domRestrict
  given: (s : Set ι)
  statement: DependsOn (s.domRestrict (π := α)) s
  proof: fun _ _ h => funext fun i => h i.1 i.2

@[deprecated (since := "2026-07-19")] alias Set.dependsOn_restrict := Set.dependsOn_domRestrict

中文:
引理 集合.dependsOn_domRestrict
  条件: (s : 集合 ι)
  结论: DependsOn (s.domRestrict (π := α)) s
  证明: fun _ _ h => funext fun i => h i.1 i.2

@[deprecated (since := "2026-07-19")] alias Set.dependsOn_restrict := Set.dependsOn_domRestrict
-/
lemma Set.dependsOn_domRestrict (s : Set ι) : DependsOn (s.domRestrict (π := α)) s :=
  fun _ _ h => funext fun i => h i.1 i.2

@[deprecated (since := "2026-07-19")] alias Set.dependsOn_restrict := Set.dependsOn_domRestrict
