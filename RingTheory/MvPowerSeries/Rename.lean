/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Bingyu Xia
-/
module

public import Mathlib.Order.Filter.TendstoCofinite
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Renaming variables of power series

This file establishes the `rename` operation on multivariate power series
under a map with finite fibers, which modifies the set of variables.

Unlike polynomials, renaming variables in power series requires a finiteness condition
on the map `f : σ → τ` between the index types. Specifically, we require that `f` has
finite fibers, which is formalized as `Filter.TendstoCofinite f`.
To see why this is necessary, consider a map from infinitely many variables to a single
variable sending each `X_i` to `X`. The sum `X_0 + X_1 + ⋯` is a valid power series in
`ℤ⟦X_0, X_1, ...⟧`, but we cannot rename each `X_i` to `X` since its image `X + X + ⋯`
would have an infinite coefficient for `X`.

To avoid writing this assumption everywhere, we usually work with the typeclass assumption
`Filter.TendstoCofinite f`. Note that this holds automatically if `f` is injective
or if `σ` is finite.

This file is patterned after `Mathlib/Algebra/MvPolynomial/Rename.lean`.

## Main declarations

* `MvPowerSeries.rename`
* `MvPowerSeries.renameEquiv`
* `MvPowerSeries.killCompl`

-/

@[expose] public section

noncomputable section

open Finsupp Filter

variable {σ τ γ R S : Type*} (f : σ -> τ) (g : τ -> γ) [TendstoCofinite f]

namespace MvPowerSeries

section Semiring

variable [Semiring R] [Semiring S]

/--
Definition of `renameFun` / `renameFun` 的定义

English:
definition renameFun
  signature: : MvPowerSeries σ R -> MvPowerSeries τ R
  body: TendstoCofinite.mapDomain (Finsupp.mapDomain f)

中文:
定义 renameFun
  签名: : MvPowerSeries σ R -> MvPowerSeries τ R
  定义体: TendstoCofinite.mapDomain (Finsupp.mapDomain f)

Depends on / 依赖: Finsupp, Finsupp.mapDomain, TendstoCofinite, TendstoCofinite.mapDomain, mapDomain
-/
def renameFun : MvPowerSeries σ R -> MvPowerSeries τ R :=
  TendstoCofinite.mapDomain (Finsupp.mapDomain f)

/--
lemma `coeff_renameFun` / 引理 `coeff_renameFun`

English:
lemma coeff_renameFun
  given: {p : MvPowerSeries σ R} {x : τ ->₀ Nat}
  statement: (renameFun f p).coeff x =
  proof: rfl

中文:
引理 coeff_renameFun
  条件: {p : MvPowerSeries σ R} {x : τ ->₀ 自然数}
  结论: (renameFun f p).coeff x =
  证明: rfl
-/
private lemma coeff_renameFun {p : MvPowerSeries σ R} {x : τ ->₀ Nat} : (renameFun f p).coeff x =
    (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) x).toFinset.sum (p.coeff ·) :=
  rfl

/--
lemma `renameFun_monomial` / 引理 `renameFun_monomial`

English:
lemma renameFun_monomial
  given: (x : σ ->₀ Nat) (r : R)
  proof: by
  classical
  ext; simp [coeff_renameFun, coeff_monomial, eq_comm]

中文:
引理 renameFun_monomial
  条件: (x : σ ->₀ 自然数) (r : R)
  证明: by
  classical
  ext; simp [coeff_renameFun, coeff_monomial, eq_comm]
-/
private lemma renameFun_monomial (x : σ ->₀ Nat) (r : R) :
    renameFun f (monomial x r) = monomial (mapDomain f x) r := by
  classical
  ext; simp [coeff_renameFun, coeff_monomial, eq_comm]

/--
theorem `renameFunAux` / 定理 `renameFunAux`

English:
theorem renameFunAux
  given: [DecidableEq σ] (x : τ ->₀ Nat)
  proof: by
  apply Set.Finite.subset
    (s := ↑((TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) x).toFinset.sup
    (fun y => Finset.product {y} (Finset.antidiagonal y))))
  · exact Finset.finite_toSet ..
  · intro; simp
    grind

中文:
定理 renameFunAux
  条件: [DecidableEq σ] (x : τ ->₀ 自然数)
  证明: by
  apply Set.Finite.subset
    (s := ↑((TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) x).toFinset.sup
    (fun y => Finset.product {y} (Finset.antidiagonal y))))
  · exact Finset.finite_toSet ..
  · intro; simp
    grind
-/
private theorem renameFunAux [DecidableEq σ] (x : τ ->₀ Nat) :
    {p : (σ ->₀ Nat) × (σ ->₀ Nat) × (σ ->₀ Nat) | (p.1).mapDomain f = x ∧
      p.2 in Finset.antidiagonal p.1}.Finite := by
  apply Set.Finite.subset
    (s := ↑((TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) x).toFinset.sup
    (fun y => Finset.product {y} (Finset.antidiagonal y))))
  · exact Finset.finite_toSet ..
  · intro; simp
    grind

/--
theorem `renameFunAux'` / 定理 `renameFunAux'`

English:
theorem renameFunAux'
  given: [DecidableEq τ] (x : τ ->₀ Nat)
  proof: by
  classical
  apply Set.Finite.subset (s := ↑((Finset.antidiagonal x).sup (fun q => Finset.product {q}
    ((TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) q.1).toFinset ×ˢ
      (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) q.2).toFinset))))
  · exact Finset.f

中文:
定理 renameFunAux'
  条件: [DecidableEq τ] (x : τ ->₀ 自然数)
  证明: by
  classical
  apply Set.Finite.subset (s := ↑((Finset.antidiagonal x).sup (fun q => Finset.product {q}
    ((TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) q.1).toFinset ×ˢ
      (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) q.2).toFinset))))
  · exact Finset.f
-/
private theorem renameFunAux' [DecidableEq τ] (x : τ ->₀ Nat) :
    {p : ((τ ->₀ Nat) × (τ ->₀ Nat)) × (σ ->₀ Nat) × (σ ->₀ Nat) | p.1 in Finset.antidiagonal x
      ∧ p.2 in (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) p.1.1).toFinset ×ˢ
    (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) p.1.2).toFinset}.Finite := by
  classical
  apply Set.Finite.subset (s := ↑((Finset.antidiagonal x).sup (fun q => Finset.product {q}
    ((TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) q.1).toFinset ×ˢ
      (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) q.2).toFinset))))
  · exact Finset.finite_toSet ..
  · intro; simp
    grind

/--
theorem `renameFunAuxImage` / 定理 `renameFunAuxImage`

English:
theorem renameFunAuxImage
  given: [DecidableEq σ] [DecidableEq τ] (x : τ ->₀ Nat)
  proof: by
  ext ⟨_, _, _⟩
  simp; grind [Finsupp.mapDomain_add]

中文:
定理 renameFunAuxImage
  条件: [DecidableEq σ] [DecidableEq τ] (x : τ ->₀ 自然数)
  证明: by
  ext ⟨_, _, _⟩
  simp; grind [Finsupp.mapDomain_add]
-/
private theorem renameFunAuxImage [DecidableEq σ] [DecidableEq τ] (x : τ ->₀ Nat) :
    (renameFunAux' f x).toFinset.image (fun (_, b) => (b.1 + b.2, b)) =
      (renameFunAux f x).toFinset := by
  ext ⟨_, _, _⟩
  simp; grind [Finsupp.mapDomain_add]

open Finset in
/--
theorem `renameFun_mul` / 定理 `renameFun_mul`

English:
theorem renameFun_mul
  given: (p q : MvPowerSeries σ R)
  proof: by
  classical
  ext x
  simp only [coeff_renameFun, coeff_mul, sum_mul_sum, ← sum_product']
  rw [← sum_finset_product' (renameFunAux f x).toFinset _ _ (by simp)]; rw [← sum_finset_product' (renameFunAux' f x).toFinset _ _ (by simp)]; rw [← renameFunAuxImage f x]; rw [sum_image fun _ => by simp; gr

中文:
定理 renameFun_mul
  条件: (p q : MvPowerSeries σ R)
  证明: by
  classical
  ext x
  simp only [coeff_renameFun, coeff_mul, sum_mul_sum, ← sum_product']
  rw [← sum_finset_product' (renameFunAux f x).toFinset _ _ (by simp)]; rw [← sum_finset_product' (renameFunAux' f x).toFinset _ _ (by simp)]; rw [← renameFunAuxImage f x]; rw [sum_image fun _ => by simp; gr
-/
private theorem renameFun_mul (p q : MvPowerSeries σ R) :
    renameFun f (p * q) = renameFun f p * renameFun f q := by
  classical
  ext x
  simp only [coeff_renameFun, coeff_mul, sum_mul_sum, ← sum_product']
  rw [← sum_finset_product' (renameFunAux f x).toFinset _ _ (by simp)]; rw [← sum_finset_product' (renameFunAux' f x).toFinset _ _ (by simp)]; rw [← renameFunAuxImage f x]; rw [sum_image fun _ => by simp; grind]

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S]

/-- Rename all the variables in a multivariable power series by a map with finite fibers. -/
@[no_expose]
/--
Definition of `rename` / `rename` 的定义

English:
definition rename
  signature: : MvPowerSeries σ R ->ₐ[R] MvPowerSeries τ R where
  body: renameFun f
  map_one' := renameFun_monomial f 0 1
  map_mul' := renameFun_mul f
  map_zero' := by ext; simp [coeff_renameFun]
  map_add' _ _ := by ext; simp [coeff_renameFun, Finset.sum_add_distrib]
  commutes' := renameFun_monomial f 0

中文:
定义 rename
  签名: : MvPowerSeries σ R ->ₐ[R] MvPowerSeries τ R where
  定义体: renameFun f
  map_one' := renameFun_monomial f 0 1
  map_mul' := renameFun_mul f
  map_zero' := by ext; simp [coeff_renameFun]
  map_add' _ _ := by ext; simp [coeff_renameFun, Finset.sum_add_distrib]
  commutes' := renameFun_monomial f 0

Depends on / 依赖: renameFun
-/
def rename : MvPowerSeries σ R ->ₐ[R] MvPowerSeries τ R where
  toFun := renameFun f
  map_one' := renameFun_monomial f 0 1
  map_mul' := renameFun_mul f
  map_zero' := by ext; simp [coeff_renameFun]
  map_add' _ _ := by ext; simp [coeff_renameFun, Finset.sum_add_distrib]
  commutes' := renameFun_monomial f 0

/--
theorem `coeff_rename` / 定理 `coeff_rename`

English:
theorem coeff_rename
  given: (p : MvPowerSeries σ R) (x : τ ->₀ Nat)
  statement: coeff x (rename f p) =
  proof: by rfl

中文:
定理 coeff_rename
  条件: (p : MvPowerSeries σ R) (x : τ ->₀ 自然数)
  结论: coeff x (rename f p) =
  证明: by rfl

Depends on / 依赖: NeBot.ne_bot, ne_bot
-/
theorem coeff_rename (p : MvPowerSeries σ R) (x : τ ->₀ Nat) : coeff x (rename f p) =
    (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) x).toFinset.sum
      (p.coeff ·) := by rfl

/--
theorem `rename_monomial` / 定理 `rename_monomial`

English:
theorem rename_monomial
  given: (x : σ ->₀ Nat) (r : R)
  statement: rename f (monomial x r) =
  proof: renameFun_monomial f ..

@[simp]

中文:
定理 rename_monomial
  条件: (x : σ ->₀ 自然数) (r : R)
  结论: rename f (monomial x r) =
  证明: renameFun_monomial f ..

@[simp]

Depends on / 依赖: renameFun_monomial
-/
theorem rename_monomial (x : σ ->₀ Nat) (r : R) : rename f (monomial x r) =
    monomial (mapDomain f x) r := renameFun_monomial f ..

@[simp]
/--
theorem `coeff_embDomain_rename` / 定理 `coeff_embDomain_rename`

English:
theorem coeff_embDomain_rename
  given: (e : σ ↪ τ) (p : MvPowerSeries σ R) (x : σ ->₀ Nat)
  proof: by
  rw [coeff_rename]; rw [Finset.sum_eq_single x _ (by simp [← embDomain_eq_mapDomain])]
  simpa using fun _ h h' => by simp [← embDomain_eq_mapDomain, embDomain_inj, h'] at h

中文:
定理 coeff_embDomain_rename
  条件: (e : σ ↪ τ) (p : MvPowerSeries σ R) (x : σ ->₀ 自然数)
  证明: by
  rw [coeff_rename]; rw [Finset.sum_eq_single x _ (by simp [← embDomain_eq_mapDomain])]
  simpa using fun _ h h' => by simp [← embDomain_eq_mapDomain, embDomain_inj, h'] at h

Depends on / 依赖: Finset, Finset.sum_eq_single, coeff_rename, embDomain_eq_mapDomain, embDomain_inj, sum_eq_single
-/
theorem coeff_embDomain_rename (e : σ ↪ τ) (p : MvPowerSeries σ R) (x : σ ->₀ Nat) :
    coeff (embDomain e x) (rename e p) = p.coeff x := by
  rw [coeff_rename]; rw [Finset.sum_eq_single x _ (by simp [← embDomain_eq_mapDomain])]
  simpa using fun _ h h' => by simp [← embDomain_eq_mapDomain, embDomain_inj, h'] at h

/--
theorem `coeff_rename_eq_zero` / 定理 `coeff_rename_eq_zero`

English:
theorem coeff_rename_eq_zero
  statement: (p : MvPowerSeries σ R) {x : τ ->₀ Nat}
  proof: by
  simp [coeff_rename, Set.Finite.toFinset, Set.preimage_singleton_eq_empty.mpr h']

@[simp]

中文:
定理 coeff_rename_eq_zero
  结论: (p : MvPowerSeries σ R) {x : τ ->₀ 自然数}
  证明: by
  simp [coeff_rename, Set.Finite.toFinset, Set.preimage_singleton_eq_empty.mpr h']

@[simp]

Depends on / 依赖: Finite, Set.Finite.toFinset, Set.preimage_singleton_eq_empty.mpr, coeff_rename, preimage_singleton_eq_empty, toFinset
-/
theorem coeff_rename_eq_zero (p : MvPowerSeries σ R) {x : τ ->₀ Nat}
    (h' : x ∉ Set.range (Finsupp.mapDomain f)) : (rename f p).coeff x = 0 := by
  simp [coeff_rename, Set.Finite.toFinset, Set.preimage_singleton_eq_empty.mpr h']

@[simp]
/--
theorem `rename_C` / 定理 `rename_C`

English:
theorem rename_C
  given: (r : R)
  statement: rename f (C r : MvPowerSeries σ R) = C r
  proof: rename_monomial f 0 r

@[simp]

中文:
定理 rename_C
  条件: (r : R)
  结论: rename f (C r : MvPowerSeries σ R) = C r
  证明: rename_monomial f 0 r

@[simp]

Depends on / 依赖: rename_monomial
-/
theorem rename_C (r : R) : rename f (C r : MvPowerSeries σ R) = C r := rename_monomial f 0 r

@[simp]
/--
theorem `rename_X` / 定理 `rename_X`

English:
theorem rename_X
  given: (i : σ)
  statement: rename f (X i : MvPowerSeries σ R) = X (f i)
  proof: by
  simpa using! rename_monomial f (single i 1) 1

@[simp]

中文:
定理 rename_X
  条件: (i : σ)
  结论: rename f (X i : MvPowerSeries σ R) = X (f i)
  证明: by
  simpa using! rename_monomial f (single i 1) 1

@[simp]

Depends on / 依赖: rename_monomial, single
-/
theorem rename_X (i : σ) : rename f (X i : MvPowerSeries σ R) = X (f i) := by
  simpa using! rename_monomial f (single i 1) 1

@[simp]
/--
theorem `rename_rename` / 定理 `rename_rename`

English:
theorem rename_rename
  given: [TendstoCofinite g] (p : MvPowerSeries σ R)
  proof: by
  classical
  ext y; simp only [coeff_rename]
  rw [← Finset.sum_finset_product' ((TendstoCofinite.finite_preimage_singleton
    (Finsupp.mapDomain (g ∘ f)) y).toFinset.image (fun u => (Finsupp.mapDomain f u]; rw [u))) _ _
      (by simp; grind [mapDomain_comp]), Finset.sum_image (by simp)]

中文:
定理 rename_rename
  条件: [TendstoCofinite g] (p : MvPowerSeries σ R)
  证明: by
  classical
  ext y; simp only [coeff_rename]
  rw [← Finset.sum_finset_product' ((TendstoCofinite.finite_preimage_singleton
    (Finsupp.mapDomain (g ∘ f)) y).toFinset.image (fun u => (Finsupp.mapDomain f u]; rw [u))) _ _
      (by simp; grind [mapDomain_comp]), Finset.sum_image (by simp)]

Depends on / 依赖: Finset, Finset.sum_finset_product, Finset.sum_image, Finsupp, Finsupp.mapDomain, TendstoCofinite, TendstoCofinite.finite_preimage_singleton, classical, coeff_rename, finite_preimage_singleton, mapDomain, mapDomain_comp, sum_finset_product, sum_image, toFinset, toFinset.image
-/
theorem rename_rename [TendstoCofinite g] (p : MvPowerSeries σ R) :
    rename g (rename f p) = rename (g ∘ f) p := by
  classical
  ext y; simp only [coeff_rename]
  rw [← Finset.sum_finset_product' ((TendstoCofinite.finite_preimage_singleton
    (Finsupp.mapDomain (g ∘ f)) y).toFinset.image (fun u => (Finsupp.mapDomain f u]; rw [u))) _ _
      (by simp; grind [mapDomain_comp]), Finset.sum_image (by simp)]

/--
lemma `rename_comp_rename` / 引理 `rename_comp_rename`

English:
lemma rename_comp_rename
  given: [TendstoCofinite g]
  proof: AlgHom.ext fun p => rename_rename f g p

@[simp]

中文:
引理 rename_comp_rename
  条件: [TendstoCofinite g]
  证明: AlgHom.ext fun p => rename_rename f g p

@[simp]

Depends on / 依赖: isTrue
-/
lemma rename_comp_rename [TendstoCofinite g] :
    (rename (R := R) g).comp (rename f) = rename (g ∘ f) :=
  AlgHom.ext fun p => rename_rename f g p

@[simp]
/--
theorem `rename_id` / 定理 `rename_id`

English:
theorem rename_id
  statement: rename id = AlgHom.id R (MvPowerSeries σ R)
  proof: by
  ext _ y
  simpa [coeff_rename] using Finset.sum_eq_single y (by simp) (by simp)

中文:
定理 rename_id
  结论: rename id = AlgHom.id R (MvPowerSeries σ R)
  证明: by
  ext _ y
  simpa [coeff_rename] using Finset.sum_eq_single y (by simp) (by simp)

Depends on / 依赖: Finset, Finset.sum_eq_single, coeff_rename, sum_eq_single
-/
theorem rename_id : rename id = AlgHom.id R (MvPowerSeries σ R) := by
  ext _ y
  simpa [coeff_rename] using Finset.sum_eq_single y (by simp) (by simp)

/--
lemma `rename_id_apply` / 引理 `rename_id_apply`

English:
lemma rename_id_apply
  given: (p : MvPowerSeries σ R)
  statement: rename id p = p
  proof: by simp

@[simp]

中文:
引理 rename_id_apply
  条件: (p : MvPowerSeries σ R)
  结论: rename id p = p
  证明: by simp

@[simp]
-/
lemma rename_id_apply (p : MvPowerSeries σ R) : rename id p = p := by simp

@[simp]
/--
theorem `constantCoeff_rename` / 定理 `constantCoeff_rename`

English:
theorem constantCoeff_rename
  given: (p : MvPowerSeries σ R)
  proof: by
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_rename]; rw [Finset.sum_eq_single 0 (by
      simp [mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits]) (by simp)]

中文:
定理 constantCoeff_rename
  条件: (p : MvPowerSeries σ R)
  证明: by
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_rename]; rw [Finset.sum_eq_single 0 (by
      simp [mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits]) (by simp)]

Depends on / 依赖: Finset, Finset.coe_map, Finset.sum_eq_single, L.eventually_le_support, L.neBot_or_eq_bot, coe_map, coeff_rename, coeff_zero_eq_constantCoeff_apply, eventually_le_support, eventually_map, filter_upwards, image_subset_iff, mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits, map_filter, neBot_or_eq_bot, sum_eq_single, support_map
-/
theorem constantCoeff_rename (p : MvPowerSeries σ R) :
    constantCoeff (rename f p) = constantCoeff p := by
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_rename]; rw [Finset.sum_eq_single 0 (by
      simp [mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits]) (by simp)]

/--
theorem `rename_injective` / 定理 `rename_injective`

English:
theorem rename_injective
  given: (e : σ ↪ τ)
  statement: Function.Injective (rename (R := R) e)
  proof: by
  intro _ _ h; ext x
  simpa using MvPowerSeries.ext_iff.mp h (embDomain e x)

中文:
定理 rename_injective
  条件: (e : σ ↪ τ)
  结论: Function.Injective (rename (R := R) e)
  证明: by
  intro _ _ h; ext x
  simpa using MvPowerSeries.ext_iff.mp h (embDomain e x)

Depends on / 依赖: Finset, Finset.coe_preimage, L.eventually_le_support, MvPowerSeries, MvPowerSeries.ext_iff.mp, Set.preimage_mono, coe_preimage, comap_filter, embDomain, eventually_le_support, eventually_map, ext_iff, filter_upwards, preimage_mono, support_comap
-/
theorem rename_injective (e : σ ↪ τ) : Function.Injective (rename (R := R) e) := by
  intro _ _ h; ext x
  simpa using MvPowerSeries.ext_iff.mp h (embDomain e x)

/--
theorem `rename_inj` / 定理 `rename_inj`

English:
theorem rename_inj
  given: (e : σ ↪ τ) (p q : MvPowerSeries σ R)
  proof: (rename_injective e).eq_iff

中文:
定理 rename_inj
  条件: (e : σ ↪ τ) (p q : MvPowerSeries σ R)
  证明: (rename_injective e).eq_iff

Depends on / 依赖: eq_iff, rename_injective, support_eq_univ_iff
-/
theorem rename_inj (e : σ ↪ τ) (p q : MvPowerSeries σ R) :
    rename e p = rename e q ↔ p = q := (rename_injective e).eq_iff

/--
theorem `rename_map` / 定理 `rename_map`

English:
theorem rename_map
  given: (φ : R ->+* S) (p : MvPowerSeries σ R)
  proof: by
  ext; simp [coeff_rename]

中文:
定理 rename_map
  条件: (φ : R ->+* S) (p : MvPowerSeries σ R)
  证明: by
  ext; simp [coeff_rename]

Depends on / 依赖: coeff_rename
-/
theorem rename_map (φ : R ->+* S) (p : MvPowerSeries σ R) :
    rename f (map φ p) = map φ (rename f p) := by
  ext; simp [coeff_rename]

/--
theorem `rename_coe` / 定理 `rename_coe`

English:
theorem rename_coe
  given: (p : MvPolynomial σ R)
  statement: rename f (p : MvPowerSeries σ R) = p.rename f
  proof: by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P n hP => simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, hP, rename_X,
    MvPolynomial.rename_X]

中文:
定理 rename_coe
  条件: (p : MvPolynomial σ R)
  结论: rename f (p : MvPowerSeries σ R) = p.rename f
  证明: by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P n hP => simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, hP, rename_X,
    MvPolynomial.rename_X]

Depends on / 依赖: MvPolynomial, MvPolynomial.coe_X, MvPolynomial.coe_mul, MvPolynomial.induction_on, MvPolynomial.rename_X, coe_X, coe_mul, induction_on, map_mul, mul_X, rename_X
-/
theorem rename_coe (p : MvPolynomial σ R) : rename f (p : MvPowerSeries σ R) = p.rename f := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P n hP => simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, hP, rename_X,
    MvPolynomial.rename_X]

variable (R) in
/-- `rename` is an equivalence when the underlying map is an equivalence. -/
@[simps apply]
/--
Definition of `renameEquiv` / `renameEquiv` 的定义

English:
definition renameEquiv
  signature: (e : σ ≃ τ)
  body: rename e
  invFun := rename e.symm
  left_inv _ := by simp
  right_inv _ := by simp

@[simp]

中文:
定义 renameEquiv
  签名: (e : σ ≃ τ)
  定义体: rename e
  invFun := rename e.symm
  left_inv _ := by simp
  right_inv _ := by simp

@[simp]
-/
def renameEquiv (e : σ ≃ τ) : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries τ R where
  __ := rename e
  invFun := rename e.symm
  left_inv _ := by simp
  right_inv _ := by simp

@[simp]
/--
theorem `renameEquiv_refl` / 定理 `renameEquiv_refl`

English:
theorem renameEquiv_refl
  statement: renameEquiv R (Equiv.refl σ) = AlgEquiv.refl
  proof: AlgEquiv.ext (by simp)

@[simp]

中文:
定理 renameEquiv_refl
  结论: renameEquiv R (Equiv.refl σ) = AlgEquiv.refl
  证明: AlgEquiv.ext (by simp)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ext
-/
theorem renameEquiv_refl : renameEquiv R (Equiv.refl σ) = AlgEquiv.refl := AlgEquiv.ext (by simp)

@[simp]
/--
theorem `renameEquiv_symm` / 定理 `renameEquiv_symm`

English:
theorem renameEquiv_symm
  given: (f : σ ≃ τ)
  statement: (renameEquiv R f).symm = renameEquiv R f.symm
  proof: rfl

@[simp]

中文:
定理 renameEquiv_symm
  条件: (f : σ ≃ τ)
  结论: (renameEquiv R f).symm = renameEquiv R f.symm
  证明: rfl

@[simp]
-/
theorem renameEquiv_symm (f : σ ≃ τ) : (renameEquiv R f).symm = renameEquiv R f.symm := rfl

@[simp]
/--
theorem `renameEquiv_trans` / 定理 `renameEquiv_trans`

English:
theorem renameEquiv_trans
  given: (e : σ ≃ τ) (f : τ ≃ γ)
  statement: (renameEquiv R e).trans (renameEquiv R f) =
  proof: AlgEquiv.ext (rename_rename e f)

中文:
定理 renameEquiv_trans
  条件: (e : σ ≃ τ) (f : τ ≃ γ)
  结论: (renameEquiv R e).trans (renameEquiv R f) =
  证明: AlgEquiv.ext (rename_rename e f)

Depends on / 依赖: AlgEquiv, AlgEquiv.ext, rename_rename
-/
theorem renameEquiv_trans (e : σ ≃ τ) (f : τ ≃ γ) : (renameEquiv R e).trans (renameEquiv R f) =
    renameEquiv R (e.trans f) := AlgEquiv.ext (rename_rename e f)

variable {e : σ ↪ τ}

/--
Definition of `killComplFun` / `killComplFun` 的定义

English:
definition killComplFun
  signature: (e : σ ↪ τ) (p : MvPowerSeries τ R)
  body: fun x => coeff (embDomain e x) p

中文:
定义 killComplFun
  签名: (e : σ ↪ τ) (p : MvPowerSeries τ R)
  定义体: fun x => coeff (embDomain e x) p

Depends on / 依赖: embDomain
-/
def killComplFun (e : σ ↪ τ) (p : MvPowerSeries τ R) : MvPowerSeries σ R :=
  fun x => coeff (embDomain e x) p

/--
theorem `coeff_killComplFun` / 定理 `coeff_killComplFun`

English:
theorem coeff_killComplFun
  given: (p : MvPowerSeries τ R) (x : σ ->₀ Nat)
  proof: rfl

中文:
定理 coeff_killComplFun
  条件: (p : MvPowerSeries τ R) (x : σ ->₀ 自然数)
  证明: rfl
-/
private theorem coeff_killComplFun (p : MvPowerSeries τ R) (x : σ ->₀ Nat) :
    coeff x (killComplFun e p) = coeff (embDomain e x) p := rfl

/--
theorem `killComplFun_monomial_embDomain` / 定理 `killComplFun_monomial_embDomain`

English:
theorem killComplFun_monomial_embDomain
  given: (x : σ ->₀ Nat) (r : R)
  proof: by
  classical
  ext; simp [coeff_killComplFun, coeff_monomial, embDomain_inj]

中文:
定理 killComplFun_monomial_embDomain
  条件: (x : σ ->₀ 自然数) (r : R)
  证明: by
  classical
  ext; simp [coeff_killComplFun, coeff_monomial, embDomain_inj]
-/
private theorem killComplFun_monomial_embDomain (x : σ ->₀ Nat) (r : R) :
    killComplFun e (monomial (embDomain e x) r) = monomial x r := by
  classical
  ext; simp [coeff_killComplFun, coeff_monomial, embDomain_inj]

/--
theorem `killComplFun_monomial_eq_zero` / 定理 `killComplFun_monomial_eq_zero`

English:
theorem killComplFun_monomial_eq_zero
  statement: {x : τ ->₀ Nat} (r : R)
  proof: by
  classical
  ext; simp [coeff_killComplFun, coeff_monomial]
  grind

中文:
定理 killComplFun_monomial_eq_zero
  结论: {x : τ ->₀ 自然数} (r : R)
  证明: by
  classical
  ext; simp [coeff_killComplFun, coeff_monomial]
  grind
-/
private theorem killComplFun_monomial_eq_zero {x : τ ->₀ Nat} (r : R)
    (h : x ∉ Set.range (embDomain e)) : killComplFun e (monomial x r) = 0 := by
  classical
  ext; simp [coeff_killComplFun, coeff_monomial]
  grind

/--
theorem `killComplFun_mul` / 定理 `killComplFun_mul`

English:
theorem killComplFun_mul
  given: (p q : MvPowerSeries τ R)
  proof: by
  classical
  ext
  simp [coeff_killComplFun, coeff_mul, ← image_prodMap_embDomain_antidiagonal, Finset.sum_image
    ((Function.Injective.injOn (Prod.map_injective.mpr ⟨embDomain_injective e,
      embDomain_injective e⟩)))]

中文:
定理 killComplFun_mul
  条件: (p q : MvPowerSeries τ R)
  证明: by
  classical
  ext
  simp [coeff_killComplFun, coeff_mul, ← image_prodMap_embDomain_antidiagonal, Finset.sum_image
    ((Function.Injective.injOn (Prod.map_injective.mpr ⟨embDomain_injective e,
      embDomain_injective e⟩)))]
-/
private theorem killComplFun_mul (p q : MvPowerSeries τ R) :
    killComplFun e (p * q) = killComplFun e p * killComplFun e q := by
  classical
  ext
  simp [coeff_killComplFun, coeff_mul, ← image_prodMap_embDomain_antidiagonal, Finset.sum_image
    ((Function.Injective.injOn (Prod.map_injective.mpr ⟨embDomain_injective e,
      embDomain_injective e⟩)))]

/-- Given an embedding `e : σ ↪ τ`, `MvPowerSeries.killComplFun e` is the function from
`R⟦τ⟧` to `R⟦σ⟧` that is left inverse to `rename e.injective.fiberFinite : R⟦σ⟧ → R⟦τ⟧`
and sends the variables in the complement of the range of `e` to `0`. -/
@[no_expose]
/--
Definition of `killCompl` / `killCompl` 的定义

English:
definition killCompl
  signature: (e : σ ↪ τ)
  body: killComplFun e
  map_one' := by simpa using! killComplFun_monomial_embDomain 0 1
  map_mul' := killComplFun_mul
  map_zero' := by ext; simp [coeff_killComplFun]
  map_add' _ _ := by ext; simp [coeff_killComplFun]
  commutes' := by simpa using! killComplFun_monomial_embDomain 0

中文:
定义 killCompl
  签名: (e : σ ↪ τ)
  定义体: killComplFun e
  map_one' := by simpa using! killComplFun_monomial_embDomain 0 1
  map_mul' := killComplFun_mul
  map_zero' := by ext; simp [coeff_killComplFun]
  map_add' _ _ := by ext; simp [coeff_killComplFun]
  commutes' := by simpa using! killComplFun_monomial_embDomain 0

Depends on / 依赖: killComplFun
-/
def killCompl (e : σ ↪ τ) : MvPowerSeries τ R ->ₐ[R] MvPowerSeries σ R where
  toFun := killComplFun e
  map_one' := by simpa using! killComplFun_monomial_embDomain 0 1
  map_mul' := killComplFun_mul
  map_zero' := by ext; simp [coeff_killComplFun]
  map_add' _ _ := by ext; simp [coeff_killComplFun]
  commutes' := by simpa using! killComplFun_monomial_embDomain 0

/--
lemma `coeff_killCompl` / 引理 `coeff_killCompl`

English:
lemma coeff_killCompl
  given: (p : MvPowerSeries τ R) (x : σ ->₀ Nat)
  proof: by rfl

中文:
引理 coeff_killCompl
  条件: (p : MvPowerSeries τ R) (x : σ ->₀ 自然数)
  证明: by rfl
-/
lemma coeff_killCompl (p : MvPowerSeries τ R) (x : σ ->₀ Nat) :
    coeff x (killCompl e p) = coeff (embDomain e x) p := by rfl

/--
lemma `killCompl_monomial_embDomain` / 引理 `killCompl_monomial_embDomain`

English:
lemma killCompl_monomial_embDomain
  given: (x : σ ->₀ Nat) (r : R)
  proof: killComplFun_monomial_embDomain x r

中文:
引理 killCompl_monomial_embDomain
  条件: (x : σ ->₀ 自然数) (r : R)
  证明: killComplFun_monomial_embDomain x r

Depends on / 依赖: killComplFun_monomial_embDomain
-/
lemma killCompl_monomial_embDomain (x : σ ->₀ Nat) (r : R) :
    killCompl e (monomial (embDomain e x) r) = monomial x r :=
  killComplFun_monomial_embDomain x r

/--
lemma `killCompl_monomial_eq_zero` / 引理 `killCompl_monomial_eq_zero`

English:
lemma killCompl_monomial_eq_zero
  statement: {x : τ ->₀ Nat} (r : R)
  proof: killComplFun_monomial_eq_zero r h

@[simp]

中文:
引理 killCompl_monomial_eq_zero
  结论: {x : τ ->₀ 自然数} (r : R)
  证明: killComplFun_monomial_eq_zero r h

@[simp]

Depends on / 依赖: killComplFun_monomial_eq_zero
-/
lemma killCompl_monomial_eq_zero {x : τ ->₀ Nat} (r : R)
    (h : x ∉ Set.range (embDomain e)) : killCompl e (monomial x r) = 0 :=
  killComplFun_monomial_eq_zero r h

@[simp]
/--
lemma `killCompl_C` / 引理 `killCompl_C`

English:
lemma killCompl_C
  given: (r : R)
  statement: killCompl e (C r) = C r
  proof: by
  simpa using killCompl_monomial_embDomain 0 r

@[simp]

中文:
引理 killCompl_C
  条件: (r : R)
  结论: killCompl e (C r) = C r
  证明: by
  simpa using killCompl_monomial_embDomain 0 r

@[simp]

Depends on / 依赖: killCompl_monomial_embDomain
-/
lemma killCompl_C (r : R) : killCompl e (C r) = C r := by
  simpa using killCompl_monomial_embDomain 0 r

@[simp]
/--
theorem `killCompl_X` / 定理 `killCompl_X`

English:
theorem killCompl_X
  given: (i : σ)
  statement: killCompl (R := R) e (X (e i)) = X i
  proof: by
  classical
  ext; simp [coeff_X, coeff_killCompl, ← embDomain_single]

中文:
定理 killCompl_X
  条件: (i : σ)
  结论: killCompl (R := R) e (X (e i)) = X i
  证明: by
  classical
  ext; simp [coeff_X, coeff_killCompl, ← embDomain_single]

Depends on / 依赖: classical, coeff_X, coeff_killCompl, embDomain_single
-/
theorem killCompl_X (i : σ) : killCompl (R := R) e (X (e i)) = X i := by
  classical
  ext; simp [coeff_X, coeff_killCompl, ← embDomain_single]

/--
theorem `killCompl_X_eq_zero` / 定理 `killCompl_X_eq_zero`

English:
theorem killCompl_X_eq_zero
  given: {t : τ} (h : t ∉ Set.range e)
  proof: by
  replace h : single t 1 ∉ Set.range (embDomain e) := by
    rwa [mem_range_embDomain_iff, support_single _ (by simp), Finset.coe_singleton,
      Set.singleton_subset_iff]
  simpa using! killCompl_monomial_eq_zero (1 : R) h

中文:
定理 killCompl_X_eq_zero
  条件: {t : τ} (h : t ∉ Set.range e)
  证明: by
  replace h : single t 1 ∉ Set.range (embDomain e) := by
    rwa [mem_range_embDomain_iff, support_single _ (by simp), Finset.coe_singleton,
      Set.singleton_subset_iff]
  simpa using! killCompl_monomial_eq_zero (1 : R) h

Depends on / 依赖: Finset, Finset.coe_singleton, Set.range, Set.singleton_subset_iff, coe_singleton, embDomain, killCompl_monomial_eq_zero, mem_range_embDomain_iff, replace, single, singleton_subset_iff, support_single
-/
theorem killCompl_X_eq_zero {t : τ} (h : t ∉ Set.range e) :
    killCompl (R := R) e (X t) = 0 := by
  replace h : single t 1 ∉ Set.range (embDomain e) := by
    rwa [mem_range_embDomain_iff, support_single _ (by simp), Finset.coe_singleton,
      Set.singleton_subset_iff]
  simpa using! killCompl_monomial_eq_zero (1 : R) h

/--
theorem `killCompl_comp_rename` / 定理 `killCompl_comp_rename`

English:
theorem killCompl_comp_rename
  statement: (killCompl e).comp (rename e) = AlgHom.id R _
  proof: by
  ext; simp [coeff_killCompl]

@[simp]

中文:
定理 killCompl_comp_rename
  结论: (killCompl e).comp (rename e) = AlgHom.id R _
  证明: by
  ext; simp [coeff_killCompl]

@[simp]

Depends on / 依赖: coeff_killCompl
-/
theorem killCompl_comp_rename : (killCompl e).comp (rename e) = AlgHom.id R _ := by
  ext; simp [coeff_killCompl]

@[simp]
/--
theorem `killCompl_rename_app` / 定理 `killCompl_rename_app`

English:
theorem killCompl_rename_app
  given: (p : MvPowerSeries σ R)
  statement: killCompl e (rename e p) = p
  proof: AlgHom.congr_fun (killCompl_comp_rename) p

中文:
定理 killCompl_rename_app
  条件: (p : MvPowerSeries σ R)
  结论: killCompl e (rename e p) = p
  证明: AlgHom.congr_fun (killCompl_comp_rename) p

Depends on / 依赖: AlgHom, AlgHom.congr_fun, congr_fun, killCompl_comp_rename
-/
theorem killCompl_rename_app (p : MvPowerSeries σ R) : killCompl e (rename e p) = p :=
  AlgHom.congr_fun (killCompl_comp_rename) p

/--
theorem `killCompl_map` / 定理 `killCompl_map`

English:
theorem killCompl_map
  given: (φ : R ->+* S) (p : MvPowerSeries τ R)
  proof: by
  ext; simp [coeff_killCompl]

中文:
定理 killCompl_map
  条件: (φ : R ->+* S) (p : MvPowerSeries τ R)
  证明: by
  ext; simp [coeff_killCompl]

Depends on / 依赖: coeff_killCompl
-/
theorem killCompl_map (φ : R ->+* S) (p : MvPowerSeries τ R) :
    killCompl e (map φ p) = map φ (killCompl e p) := by
  ext; simp [coeff_killCompl]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (p : MvPowerSeries σ R)

/--
lemma `HasSubst.X_comp` / 引理 `HasSubst.X_comp`

English:
lemma HasSubst.X_comp
  statement: HasSubst (X ∘ f : σ -> MvPowerSeries τ R) where
  proof: by simp
  coeff_zero d := Set.Finite.subset (d.support.finite_toSet.biUnion'
    (fun i _ => TendstoCofinite.finite_preimage_singleton f i)) (fun x => by
      contrapose; intro _ _; classical simp_all [coeff_X])

中文:
引理 HasSubst.X_comp
  结论: HasSubst (X ∘ f : σ -> MvPowerSeries τ R) where
  证明: by simp
  coeff_zero d := Set.Finite.subset (d.support.finite_toSet.biUnion'
    (fun i _ => TendstoCofinite.finite_preimage_singleton f i)) (fun x => by
      contrapose; intro _ _; classical simp_all [coeff_X])

Depends on / 依赖: Finite, Set.Finite.subset, TendstoCofinite, TendstoCofinite.finite_preimage_singleton, biUnion, classical, coeff_X, coeff_zero, contrapose, d.support.finite_toSet.biUnion, finite_preimage_singleton, finite_toSet, subset, support
-/
lemma HasSubst.X_comp : HasSubst (X ∘ f : σ -> MvPowerSeries τ R) where
  const_coeff := by simp
  coeff_zero d := Set.Finite.subset (d.support.finite_toSet.biUnion'
    (fun i _ => TendstoCofinite.finite_preimage_singleton f i)) (fun x => by
      contrapose; intro _ _; classical simp_all [coeff_X])

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `rename_eq_subst` / 定理 `rename_eq_subst`

English:
theorem rename_eq_subst
  statement: rename f p = p.subst (X ∘ f)
  proof: by
  classical
  ext n
  rw [coeff_rename]; rw [coeff_subst (HasSubst.X_comp _) p n]; rw [finsum_eq_sum _
    (coeff_subst_finite (HasSubst.X_comp _) p n)]
  have (d : σ ->₀ Nat) (hd : (coeff d) p * (coeff n) (d.prod fun s e => X (f s) ^ e) != 0) :
      mapDomain f d = n := by
    simp_rw [← monomi

中文:
定理 rename_eq_subst
  结论: rename f p = p.subst (X ∘ f)
  证明: by
  classical
  ext n
  rw [coeff_rename]; rw [coeff_subst (HasSubst.X_comp _) p n]; rw [finsum_eq_sum _
    (coeff_subst_finite (HasSubst.X_comp _) p n)]
  have (d : σ ->₀ Nat) (hd : (coeff d) p * (coeff n) (d.prod fun s e => X (f s) ^ e) != 0) :
      mapDomain f d = n := by
    simp_rw [← monomi

Depends on / 依赖: Finite, Finset, Finset.sum_subset_zero_on_sdiff, HasSubst, HasSubst.X_comp, Set.Finite.toFinset_mono, X_comp, classical, coeff_rename, coeff_subst, coeff_subst_finite, contextua, d.prod, eq_of_coeff_monomial_ne_zero, finsum_eq_sum, mapDomain, monomial_mapDomain_apply_one, right_ne_zero_of_mul, simp_rw, sum_subset_zero_on_sdiff
-/
theorem rename_eq_subst : rename f p = p.subst (X ∘ f) := by
  classical
  ext n
  rw [coeff_rename]; rw [coeff_subst (HasSubst.X_comp _) p n]; rw [finsum_eq_sum _
    (coeff_subst_finite (HasSubst.X_comp _) p n)]
  have (d : σ ->₀ Nat) (hd : (coeff d) p * (coeff n) (d.prod fun s e => X (f s) ^ e) != 0) :
      mapDomain f d = n := by
    simp_rw [← monomial_mapDomain_apply_one] at hd
    exact (eq_of_coeff_monomial_ne_zero (right_ne_zero_of_mul hd)).symm
  refine (Finset.sum_subset_zero_on_sdiff ?_ ?_ (fun x hx => ?_)).symm
  · exact Set.Finite.toFinset_mono this
  · simp +contextual [← monomial_mapDomain_apply_one]
  · simp only [Set.Finite.mem_toFinset] at hx
    simp [← this _ hx, ← monomial_mapDomain_apply_one, coeff_monomial_same]

end CommRing

end MvPowerSeries
