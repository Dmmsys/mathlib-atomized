/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Logic.Embedding.Basic

/-!
# Embedding a finitely supported function into a sigma type summand

This file provides `Finsupp.embSigma`, which embeds a finitely supported function `ι k →₀ M`
into the corresponding summand of `(Σ k, ι k) →₀ M`.

## Main declarations

* `Finsupp.embSigma`: Embed `ι k →₀ M` into `(Σ k, ι k) →₀ M` for a specific `k`.

## Implementation notes

This is a special case of `Finsupp.embDomain` using `Function.Embedding.sigmaMk`.
-/

@[expose] public section

noncomputable section

open Function

variable {κ : Type*} {ι : κ -> Type*} {M : Type*}

namespace Finsupp

section EmbSigma

variable [Zero M]

/--
Definition of `embSigma` / `embSigma` 的定义

English:
definition embSigma
  signature: {k : κ} (f : ι k ->₀ M)
  body: embDomain (Embedding.sigmaMk k) f

@[grind =]

中文:
定义 embSigma
  签名: {k : κ} (f : ι k ->₀ M)
  定义体: embDomain (Embedding.sigmaMk k) f

@[grind =]

Depends on / 依赖: Embedding, Embedding.sigmaMk, embDomain, sigmaMk
-/
def embSigma {k : κ} (f : ι k ->₀ M) : (Σ k, ι k) ->₀ M :=
  embDomain (Embedding.sigmaMk k) f

@[grind =]
/--
theorem `embSigma_apply` / 定理 `embSigma_apply`

English:
theorem embSigma_apply
  given: [DecidableEq κ] {k : κ} (f : ι k ->₀ M) (i : Σ k, ι k)
  proof: by
  rcases i with ⟨k, i⟩
  split_ifs with h
  · subst h
    simp only [embSigma, Embedding.sigmaMk]
    apply embDomain_apply_self
  · simp only [embSigma, Embedding.sigmaMk]
    rw [embDomain_of_notMem_range]
    simp_all

@[simp]

中文:
定理 embSigma_apply
  条件: [DecidableEq κ] {k : κ} (f : ι k ->₀ M) (i : Σ k, ι k)
  证明: by
  rcases i with ⟨k, i⟩
  split_ifs with h
  · subst h
    simp only [embSigma, Embedding.sigmaMk]
    apply embDomain_apply_self
  · simp only [embSigma, Embedding.sigmaMk]
    rw [embDomain_of_notMem_range]
    simp_all

@[simp]

Depends on / 依赖: Embedding, Embedding.sigmaMk, embDomain_apply_self, embDomain_of_notMem_range, embSigma, sigmaMk, split_ifs
-/
theorem embSigma_apply [DecidableEq κ] {k : κ} (f : ι k ->₀ M) (i : Σ k, ι k) :
    embSigma f i = if h : i.1 = k then f (h ▸ i.2) else 0 := by
  rcases i with ⟨k, i⟩
  split_ifs with h
  · subst h
    simp only [embSigma, Embedding.sigmaMk]
    apply embDomain_apply_self
  · simp only [embSigma, Embedding.sigmaMk]
    rw [embDomain_of_notMem_range]
    simp_all

@[simp]
/--
theorem `embSigma_apply_self` / 定理 `embSigma_apply_self`

English:
theorem embSigma_apply_self
  given: {k : κ} (f : ι k ->₀ M) (i : ι k)
  proof: by
  rw [embSigma]
  exact embDomain_apply_self (Embedding.sigmaMk k) f i

中文:
定理 embSigma_apply_self
  条件: {k : κ} (f : ι k ->₀ M) (i : ι k)
  证明: by
  rw [embSigma]
  exact embDomain_apply_self (Embedding.sigmaMk k) f i

Depends on / 依赖: Embedding, Embedding.sigmaMk, embDomain_apply_self, embSigma, sigmaMk
-/
theorem embSigma_apply_self {k : κ} (f : ι k ->₀ M) (i : ι k) :
    embSigma f ⟨k, i⟩ = f i := by
  rw [embSigma]
  exact embDomain_apply_self (Embedding.sigmaMk k) f i

/--
theorem `embSigma_apply_of_ne` / 定理 `embSigma_apply_of_ne`

English:
theorem embSigma_apply_of_ne
  given: {k k' : κ} (f : ι k ->₀ M) (hk : k' != k) (i : ι k')
  proof: by
  apply embDomain_of_notMem_range
  grind

@[simp, grind =]

中文:
定理 embSigma_apply_of_ne
  条件: {k k' : κ} (f : ι k ->₀ M) (hk : k' != k) (i : ι k')
  证明: by
  apply embDomain_of_notMem_range
  grind

@[simp, grind =]

Depends on / 依赖: embDomain_of_notMem_range
-/
theorem embSigma_apply_of_ne {k k' : κ} (f : ι k ->₀ M) (hk : k' != k) (i : ι k') :
    embSigma f ⟨k', i⟩ = 0 := by
  apply embDomain_of_notMem_range
  grind

@[simp, grind =]
/--
theorem `support_embSigma` / 定理 `support_embSigma`

English:
theorem support_embSigma
  given: {k : κ} (f : ι k ->₀ M)
  proof: by
  simp [embSigma]

@[simp]

中文:
定理 support_embSigma
  条件: {k : κ} (f : ι k ->₀ M)
  证明: by
  simp [embSigma]

@[simp]

Depends on / 依赖: embSigma
-/
theorem support_embSigma {k : κ} (f : ι k ->₀ M) :
    (embSigma f).support = f.support.map (Embedding.sigmaMk k) := by
  simp [embSigma]

@[simp]
/--
theorem `embSigma_zero` / 定理 `embSigma_zero`

English:
theorem embSigma_zero
  given: {k : κ}
  statement: embSigma (0 : ι k ->₀ M) = 0
  proof: by
  simp [embSigma]

@[simp]

中文:
定理 embSigma_zero
  条件: {k : κ}
  结论: embSigma (0 : ι k ->₀ M) = 0
  证明: by
  simp [embSigma]

@[simp]

Depends on / 依赖: embSigma
-/
theorem embSigma_zero {k : κ} : embSigma (0 : ι k ->₀ M) = 0 := by
  simp [embSigma]

@[simp]
/--
theorem `embSigma_eq_zero` / 定理 `embSigma_eq_zero`

English:
theorem embSigma_eq_zero
  given: {k : κ} {f : ι k ->₀ M}
  proof: by
  simp [embSigma]

中文:
定理 embSigma_eq_zero
  条件: {k : κ} {f : ι k ->₀ M}
  证明: by
  simp [embSigma]

Depends on / 依赖: embSigma
-/
theorem embSigma_eq_zero {k : κ} {f : ι k ->₀ M} :
    embSigma f = 0 ↔ f = 0 := by
  simp [embSigma]

/--
theorem `embSigma_injective` / 定理 `embSigma_injective`

English:
theorem embSigma_injective
  given: {k : κ}
  proof: by
  intro f g h
  ext i
  have := congr_fun (congrArg (⇑) h) ⟨k, i⟩
  simpa using this

@[simp]

中文:
定理 embSigma_injective
  条件: {k : κ}
  证明: by
  intro f g h
  ext i
  have := congr_fun (congrArg (⇑) h) ⟨k, i⟩
  simpa using this

@[simp]

Depends on / 依赖: congr_fun
-/
theorem embSigma_injective {k : κ} :
    Injective (embSigma : (ι k ->₀ M) -> (Σ k, ι k) ->₀ M) := by
  intro f g h
  ext i
  have := congr_fun (congrArg (⇑) h) ⟨k, i⟩
  simpa using this

@[simp]
/--
theorem `embSigma_inj` / 定理 `embSigma_inj`

English:
theorem embSigma_inj
  given: {k : κ} {f g : ι k ->₀ M}
  proof: embSigma_injective.eq_iff

中文:
定理 embSigma_inj
  条件: {k : κ} {f g : ι k ->₀ M}
  证明: embSigma_injective.eq_iff

Depends on / 依赖: embSigma_injective, embSigma_injective.eq_iff, eq_iff
-/
theorem embSigma_inj {k : κ} {f g : ι k ->₀ M} :
    embSigma f = embSigma g ↔ f = g :=
  embSigma_injective.eq_iff

end EmbSigma

section EmbSigmaAdd

variable [AddMonoid M]

/--
theorem `embSigma_add` / 定理 `embSigma_add`

English:
theorem embSigma_add
  given: {k : κ} (f g : ι k ->₀ M)
  proof: by
  ext ⟨k', i⟩
  by_cases hk : k' = k
  · subst hk
    simp
  · simp [embSigma_apply_of_ne _ hk]

中文:
定理 embSigma_add
  条件: {k : κ} (f g : ι k ->₀ M)
  证明: by
  ext ⟨k', i⟩
  by_cases hk : k' = k
  · subst hk
    simp
  · simp [embSigma_apply_of_ne _ hk]

Depends on / 依赖: embSigma_apply_of_ne
-/
theorem embSigma_add {k : κ} (f g : ι k ->₀ M) :
    embSigma (f + g) = embSigma f + embSigma g := by
  ext ⟨k', i⟩
  by_cases hk : k' = k
  · subst hk
    simp
  · simp [embSigma_apply_of_ne _ hk]

-- TODO: `embSigma` could be bundled as e.g. an additive or linear map, when needed.

end EmbSigmaAdd

section EmbSigmaSingle

@[simp]
/--
theorem `embSigma_single` / 定理 `embSigma_single`

English:
theorem embSigma_single
  given: [Zero M] {k : κ} (i : ι k) (m : M)
  proof: by
  classical
  grind

中文:
定理 embSigma_single
  条件: [零 M] {k : κ} (i : ι k) (m : M)
  证明: by
  classical
  grind

Depends on / 依赖: classical
-/
theorem embSigma_single [Zero M] {k : κ} (i : ι k) (m : M) :
    embSigma (single i m) = single ⟨k, i⟩ m := by
  classical
  grind

end EmbSigmaSingle

section Split

variable [Zero M]

/-- `embSigma` is a left inverse to `split` at the same index. -/
@[simp]
/--
theorem `split_embSigma_self` / 定理 `split_embSigma_self`

English:
theorem split_embSigma_self
  given: {k : κ} (f : ι k ->₀ M)
  proof: by
  ext i
  simp [split_apply]

中文:
定理 split_embSigma_self
  条件: {k : κ} (f : ι k ->₀ M)
  证明: by
  ext i
  simp [split_apply]

Depends on / 依赖: split_apply
-/
theorem split_embSigma_self {k : κ} (f : ι k ->₀ M) :
    split (embSigma f) k = f := by
  ext i
  simp [split_apply]

/--
theorem `split_embSigma_of_ne` / 定理 `split_embSigma_of_ne`

English:
theorem split_embSigma_of_ne
  given: {k k' : κ} (f : ι k ->₀ M) (hk : k' != k)
  proof: by
  ext i
  simp [split_apply, embSigma_apply_of_ne _ hk]

中文:
定理 split_embSigma_of_ne
  条件: {k k' : κ} (f : ι k ->₀ M) (hk : k' != k)
  证明: by
  ext i
  simp [split_apply, embSigma_apply_of_ne _ hk]

Depends on / 依赖: embSigma_apply_of_ne, split_apply
-/
theorem split_embSigma_of_ne {k k' : κ} (f : ι k ->₀ M) (hk : k' != k) :
    split (embSigma f) k' = 0 := by
  ext i
  simp [split_apply, embSigma_apply_of_ne _ hk]

end Split

end Finsupp
