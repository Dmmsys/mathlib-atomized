/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler, Andrew Yang
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.UniformConvergence
public import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Infinite sum and products that converge uniformly

## Main definitions
- `HasProdUniformlyOn f g s` : `∏ i, f i b` converges uniformly on `s` to `g`.
- `HasProdLocallyUniformlyOn f g s` : `∏ i, f i b` converges locally uniformly on `s` to `g`.
- `HasProdUniformly f g` : `∏ i, f i b` converges uniformly to `g`.
- `HasProdLocallyUniformly f g` : `∏ i, f i b` converges locally uniformly to `g`.
-/

@[expose] public section

noncomputable section

open Filter Function

open scoped Topology

variable {α β ι : Type*} [CommMonoid α] {f : ι -> β -> α} {g : β -> α}
  {x : β} {s : Set β} {I : Finset ι} [UniformSpace α]

/-!
## Uniform convergence of sums and products
-/

section UniformlyOn

variable (f g s) in
/-- `HasProdUniformlyOn f g s` means that the (potentially infinite) product `∏' i, f i b`
for `b : β` converges uniformly on `s` to `g`. -/
@[to_additive /-- `HasSumUniformlyOn f g s` means that the (potentially infinite) sum `∑' i, f i b`
for `b : β` converges uniformly on `s` to `g`. -/]
/--
Definition of `HasProdUniformlyOn` / `HasProdUniformlyOn` 的定义

English:
definition HasProdUniformlyOn
  signature: : Prop
  body: HasProd (UniformOnFun.ofFun {s} ∘ f) (UniformOnFun.ofFun {s} g)

中文:
定义 HasProdUniformlyOn
  签名: : 命题
  定义体: HasProd (UniformOnFun.ofFun {s} ∘ f) (UniformOnFun.ofFun {s} g)

Depends on / 依赖: HasProd, UniformOnFun, UniformOnFun.ofFun
-/
def HasProdUniformlyOn : Prop := HasProd (UniformOnFun.ofFun {s} ∘ f) (UniformOnFun.ofFun {s} g)

variable (f g s) in
/-- `MultipliableUniformlyOn f s` means that there is some infinite product to which
`f` converges uniformly on `s`. Use `fun x ↦ ∏' i, f i x` to get the product function. -/
@[to_additive /-- `SummableUniformlyOn f s` means that there is some infinite sum to
which `f` converges uniformly on `s`. Use fun x ↦ ∑' i, f i x to get the sum function. -/]
/--
Definition of `MultipliableUniformlyOn` / `MultipliableUniformlyOn` 的定义

English:
definition MultipliableUniformlyOn
  signature: : Prop
  body: Multipliable (UniformOnFun.ofFun {s} ∘ f)

@[to_additive]

中文:
定义 MultipliableUniformlyOn
  签名: : 命题
  定义体: Multipliable (UniformOnFun.ofFun {s} ∘ f)

@[to_additive]

Depends on / 依赖: Multipliable, UniformOnFun, UniformOnFun.ofFun
-/
def MultipliableUniformlyOn : Prop := Multipliable (UniformOnFun.ofFun {s} ∘ f)

@[to_additive]
/--
lemma `MultipliableUniformlyOn.exists` / 引理 `MultipliableUniformlyOn.exists`

English:
lemma MultipliableUniformlyOn.exists
  given: (h : MultipliableUniformlyOn f s)
  proof: h

@[to_additive]

中文:
引理 MultipliableUniformlyOn.exists
  条件: (h : MultipliableUniformlyOn f s)
  证明: h

@[to_additive]
-/
lemma MultipliableUniformlyOn.exists (h : MultipliableUniformlyOn f s) :
    exists g, HasProdUniformlyOn f g s :=
  h

@[to_additive]
/--
theorem `HasProdUniformlyOn.multipliableUniformlyOn` / 定理 `HasProdUniformlyOn.multipliableUniformlyOn`

English:
theorem HasProdUniformlyOn.multipliableUniformlyOn
  given: (h : HasProdUniformlyOn f g s)
  proof: ⟨g, h⟩

@[to_additive]

中文:
定理 HasProdUniformlyOn.multipliableUniformlyOn
  条件: (h : HasProdUniformlyOn f g s)
  证明: ⟨g, h⟩

@[to_additive]
-/
theorem HasProdUniformlyOn.multipliableUniformlyOn (h : HasProdUniformlyOn f g s) :
    MultipliableUniformlyOn f s :=
  ⟨g, h⟩

@[to_additive]
/--
lemma `hasProdUniformlyOn_iff_tendstoUniformlyOn` / 引理 `hasProdUniformlyOn_iff_tendstoUniformlyOn`

English:
lemma hasProdUniformlyOn_iff_tendstoUniformlyOn
  proof: by
  simpa [HasProdUniformlyOn, HasProd, ← UniformOnFun.ofFun_prod, Finset.prod_fn] using!
    UniformOnFun.tendsto_iff_tendstoUniformlyOn (𝔖 := {s})

@[to_additive]
alias ⟨HasProdUniformlyOn.tendstoUniformlyOn, _⟩ := hasProdUniformlyOn_iff_tendstoUniformlyOn

@[to_additive]

中文:
引理 hasProdUniformlyOn_iff_tendstoUniformlyOn
  证明: by
  simpa [HasProdUniformlyOn, HasProd, ← UniformOnFun.ofFun_prod, Finset.prod_fn] using!
    UniformOnFun.tendsto_iff_tendstoUniformlyOn (𝔖 := {s})

@[to_additive]
alias ⟨HasProdUniformlyOn.tendstoUniformlyOn, _⟩ := hasProdUniformlyOn_iff_tendstoUniformlyOn

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_fn, HasProd, HasProdUniformlyOn, UniformOnFun, UniformOnFun.ofFun_prod, UniformOnFun.tendsto_iff_tendstoUniformlyOn, ofFun_prod, prod_fn, tendsto_iff_tendstoUniformlyOn
-/
lemma hasProdUniformlyOn_iff_tendstoUniformlyOn :
    HasProdUniformlyOn f g s ↔ TendstoUniformlyOn (∏ i in ·, f i ·) g atTop s := by
  simpa [HasProdUniformlyOn, HasProd, ← UniformOnFun.ofFun_prod, Finset.prod_fn] using!
    UniformOnFun.tendsto_iff_tendstoUniformlyOn (𝔖 := {s})

@[to_additive]
alias ⟨HasProdUniformlyOn.tendstoUniformlyOn, _⟩ := hasProdUniformlyOn_iff_tendstoUniformlyOn

@[to_additive]
/--
lemma `HasProdUniformlyOn.congr` / 引理 `HasProdUniformlyOn.congr`

English:
lemma HasProdUniformlyOn.congr
  statement: {f' : ι -> β -> α}
  proof: hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr (h.tendstoUniformlyOn.congr hff')

@[to_additive]

中文:
引理 HasProdUniformlyOn.congr
  结论: {f' : ι -> β -> α}
  证明: hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr (h.tendstoUniformlyOn.congr hff')

@[to_additive]

Depends on / 依赖: h.tendstoUniformlyOn.congr, hasProdUniformlyOn_iff_tendstoUniformlyOn, hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr, tendstoUniformlyOn
-/
lemma HasProdUniformlyOn.congr {f' : ι -> β -> α}
    (h : HasProdUniformlyOn f g s)
    (hff' : forallᶠ (n : Finset ι) in atTop, s.EqOn (∏ i in n, f i ·) (∏ i in n, f' i ·)) :
    HasProdUniformlyOn f' g s :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr (h.tendstoUniformlyOn.congr hff')

@[to_additive]
/--
lemma `HasProdUniformlyOn.congr_right` / 引理 `HasProdUniformlyOn.congr_right`

English:
lemma HasProdUniformlyOn.congr_right
  statement: {g' : β -> α}
  proof: hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr (h.tendstoUniformlyOn.congr_right hgg')

@[to_additive]

中文:
引理 HasProdUniformlyOn.congr_right
  结论: {g' : β -> α}
  证明: hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr (h.tendstoUniformlyOn.congr_right hgg')

@[to_additive]

Depends on / 依赖: congr_right, h.tendstoUniformlyOn.congr_right, hasProdUniformlyOn_iff_tendstoUniformlyOn, hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr, tendstoUniformlyOn
-/
lemma HasProdUniformlyOn.congr_right {g' : β -> α}
    (h : HasProdUniformlyOn f g s) (hgg' : s.EqOn g g') :
    HasProdUniformlyOn f g' s :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr (h.tendstoUniformlyOn.congr_right hgg')

@[to_additive]
/--
lemma `HasProdUniformlyOn.tendstoUniformlyOn_finsetRange` / 引理 `HasProdUniformlyOn.tendstoUniformlyOn_finsetRange`

English:
lemma HasProdUniformlyOn.tendstoUniformlyOn_finsetRange
  proof: (tendsto_finset_range.eventually <| h.tendstoUniformlyOn · ·)

@[to_additive]

中文:
引理 HasProdUniformlyOn.tendstoUniformlyOn_finsetRange
  证明: (tendsto_finset_range.eventually <| h.tendstoUniformlyOn · ·)

@[to_additive]

Depends on / 依赖: eventually, h.tendstoUniformlyOn, tendstoUniformlyOn, tendsto_finset_range, tendsto_finset_range.eventually
-/
lemma HasProdUniformlyOn.tendstoUniformlyOn_finsetRange
    {f : Nat -> β -> α} (h : HasProdUniformlyOn f g s) :
    TendstoUniformlyOn (∏ i in .range ·, f i ·) g atTop s :=
  (tendsto_finset_range.eventually <| h.tendstoUniformlyOn · ·)

@[to_additive]
/--
theorem `HasProdUniformlyOn.hasProd` / 定理 `HasProdUniformlyOn.hasProd`

English:
theorem HasProdUniformlyOn.hasProd
  given: (h : HasProdUniformlyOn f g s) (hx : x in s)
  proof: h.tendstoUniformlyOn.tendsto_at hx

@[to_additive]

中文:
定理 HasProdUniformlyOn.hasProd
  条件: (h : HasProdUniformlyOn f g s) (hx : x in s)
  证明: h.tendstoUniformlyOn.tendsto_at hx

@[to_additive]

Depends on / 依赖: h.tendstoUniformlyOn.tendsto_at, tendstoUniformlyOn, tendsto_at
-/
theorem HasProdUniformlyOn.hasProd (h : HasProdUniformlyOn f g s) (hx : x in s) :
    HasProd (f · x) (g x) :=
  h.tendstoUniformlyOn.tendsto_at hx

@[to_additive]
/--
theorem `HasProdUniformlyOn.tprod_eqOn` / 定理 `HasProdUniformlyOn.tprod_eqOn`

English:
theorem HasProdUniformlyOn.tprod_eqOn
  given: [T2Space α] (h : HasProdUniformlyOn f g s)
  proof: fun _ hx => (h.hasProd hx).tprod_eq

@[to_additive]

中文:
定理 HasProdUniformlyOn.tprod_eqOn
  条件: [T2Space α] (h : HasProdUniformlyOn f g s)
  证明: fun _ hx => (h.hasProd hx).tprod_eq

@[to_additive]

Depends on / 依赖: h.hasProd, hasProd, tprod_eq
-/
theorem HasProdUniformlyOn.tprod_eqOn [T2Space α] (h : HasProdUniformlyOn f g s) :
    s.EqOn (∏' b, f b ·) g :=
  fun _ hx => (h.hasProd hx).tprod_eq

@[to_additive]
/--
theorem `MultipliableUniformlyOn.multipliable` / 定理 `MultipliableUniformlyOn.multipliable`

English:
theorem MultipliableUniformlyOn.multipliable
  given: (h : MultipliableUniformlyOn f s) (hx : x in s)
  proof: (h.exists.choose_spec.hasProd hx).multipliable

@[to_additive]

中文:
定理 MultipliableUniformlyOn.multipliable
  条件: (h : MultipliableUniformlyOn f s) (hx : x in s)
  证明: (h.exists.choose_spec.hasProd hx).multipliable

@[to_additive]

Depends on / 依赖: choose_spec, h.exists.choose_spec.hasProd, hasProd, multipliable
-/
theorem MultipliableUniformlyOn.multipliable (h : MultipliableUniformlyOn f s) (hx : x in s) :
    Multipliable (f · x) :=
  (h.exists.choose_spec.hasProd hx).multipliable

@[to_additive]
/--
theorem `MultipliableUniformlyOn.hasProdUniformlyOn` / 定理 `MultipliableUniformlyOn.hasProdUniformlyOn`

English:
theorem MultipliableUniformlyOn.hasProdUniformlyOn
  given: (h : MultipliableUniformlyOn f s)
  proof: by
  obtain ⟨g, hg⟩ := h.exists
  have hp := hg
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at hg ⊢
  exact hg.congr_inseparable_right fun x hx =>
    tendsto_nhds_unique_inseparable (hp.hasProd hx) (hp.hasProd hx).multipliable.hasProd

@[to_additive]

中文:
定理 MultipliableUniformlyOn.hasProdUniformlyOn
  条件: (h : MultipliableUniformlyOn f s)
  证明: by
  obtain ⟨g, hg⟩ := h.exists
  have hp := hg
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at hg ⊢
  exact hg.congr_inseparable_right fun x hx =>
    tendsto_nhds_unique_inseparable (hp.hasProd hx) (hp.hasProd hx).multipliable.hasProd

@[to_additive]

Depends on / 依赖: congr_inseparable_right, h.exists, hasProd, hasProdUniformlyOn_iff_tendstoUniformlyOn, hg.congr_inseparable_right, hp.hasProd, multipliable, multipliable.hasProd, tendsto_nhds_unique_inseparable
-/
theorem MultipliableUniformlyOn.hasProdUniformlyOn (h : MultipliableUniformlyOn f s) :
    HasProdUniformlyOn f (∏' i, f i ·) s := by
  obtain ⟨g, hg⟩ := h.exists
  have hp := hg
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at hg ⊢
  exact hg.congr_inseparable_right fun x hx =>
    tendsto_nhds_unique_inseparable (hp.hasProd hx) (hp.hasProd hx).multipliable.hasProd

@[to_additive]
/--
theorem `multipliableUniformlyOn_iff_hasProdUniformlyOn` / 定理 `multipliableUniformlyOn_iff_hasProdUniformlyOn`

English:
theorem multipliableUniformlyOn_iff_hasProdUniformlyOn
  proof: ⟨MultipliableUniformlyOn.hasProdUniformlyOn, HasProdUniformlyOn.multipliableUniformlyOn⟩

@[to_additive]

中文:
定理 multipliableUniformlyOn_iff_hasProdUniformlyOn
  证明: ⟨MultipliableUniformlyOn.hasProdUniformlyOn, HasProdUniformlyOn.multipliableUniformlyOn⟩

@[to_additive]

Depends on / 依赖: HasProdUniformlyOn, HasProdUniformlyOn.multipliableUniformlyOn, MultipliableUniformlyOn, MultipliableUniformlyOn.hasProdUniformlyOn, hasProdUniformlyOn, multipliableUniformlyOn
-/
theorem multipliableUniformlyOn_iff_hasProdUniformlyOn :
    MultipliableUniformlyOn f s ↔ HasProdUniformlyOn f (∏' i, f i ·) s :=
  ⟨MultipliableUniformlyOn.hasProdUniformlyOn, HasProdUniformlyOn.multipliableUniformlyOn⟩

@[to_additive]
/--
lemma `HasProdUniformlyOn.mono` / 引理 `HasProdUniformlyOn.mono`

English:
lemma HasProdUniformlyOn.mono
  statement: {t : Set β}
  proof: hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr h.tendstoUniformlyOn.mono hst

@[to_additive]

中文:
引理 HasProdUniformlyOn.mono
  结论: {t : Set β}
  证明: hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr h.tendstoUniformlyOn.mono hst

@[to_additive]

Depends on / 依赖: h.tendstoUniformlyOn.mono, hasProdUniformlyOn_iff_tendstoUniformlyOn, hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr, tendstoUniformlyOn
-/
lemma HasProdUniformlyOn.mono {t : Set β}
    (h : HasProdUniformlyOn f g t) (hst : s subseteq t) : HasProdUniformlyOn f g s :=
hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr h.tendstoUniformlyOn.mono hst

@[to_additive]
/--
lemma `MultipliableUniformlyOn.mono` / 引理 `MultipliableUniformlyOn.mono`

English:
lemma MultipliableUniformlyOn.mono
  statement: {t : Set β}
  proof: (h.exists.choose_spec.mono hst).multipliableUniformlyOn

中文:
引理 MultipliableUniformlyOn.mono
  结论: {t : Set β}
  证明: (h.exists.choose_spec.mono hst).multipliableUniformlyOn

Depends on / 依赖: choose_spec, h.exists.choose_spec.mono, multipliableUniformlyOn
-/
lemma MultipliableUniformlyOn.mono {t : Set β}
    (h : MultipliableUniformlyOn f t) (hst : s subseteq t) : MultipliableUniformlyOn f s :=
  (h.exists.choose_spec.mono hst).multipliableUniformlyOn

end UniformlyOn

section LocallyUniformlyOn
/-!
## Locally uniform convergence of sums and products
-/

variable [TopologicalSpace β]

variable (f g s) in
/-- `HasProdLocallyUniformlyOn f g s` means that the (potentially infinite) product `∏' i, f i b`
for `b : β` converges locally uniformly on `s` to `g b` (in the sense of
`TendstoLocallyUniformlyOn`). -/
@[to_additive /-- `HasSumLocallyUniformlyOn f g s` means that the (potentially infinite) sum
`∑' i, f i b` for `b : β` converges locally uniformly on `s` to `g b` (in the sense of
`TendstoLocallyUniformlyOn`). -/]
/--
Definition of `HasProdLocallyUniformlyOn` / `HasProdLocallyUniformlyOn` 的定义

English:
definition HasProdLocallyUniformlyOn
  signature: : Prop
  body: TendstoLocallyUniformlyOn (∏ i in ·, f i ·) g atTop s

中文:
定义 HasProdLocallyUniformlyOn
  签名: : 命题
  定义体: TendstoLocallyUniformlyOn (∏ i in ·, f i ·) g atTop s

Depends on / 依赖: TendstoLocallyUniformlyOn
-/
def HasProdLocallyUniformlyOn : Prop := TendstoLocallyUniformlyOn (∏ i in ·, f i ·) g atTop s

variable (f g s) in
/-- `MultipliableLocallyUniformlyOn f s` means that the product `∏' i, f i b` converges locally
uniformly on `s` to something. -/
@[to_additive /-- `SummableLocallyUniformlyOn f s` means that `∑' i, f i b` converges locally
uniformly on `s` to something. -/]
/--
Definition of `MultipliableLocallyUniformlyOn` / `MultipliableLocallyUniformlyOn` 的定义

English:
definition MultipliableLocallyUniformlyOn
  signature: : Prop
  body: exists g, HasProdLocallyUniformlyOn f g s

@[to_additive]

中文:
定义 MultipliableLocallyUniformlyOn
  签名: : 命题
  定义体: exists g, HasProdLocallyUniformlyOn f g s

@[to_additive]

Depends on / 依赖: HasProdLocallyUniformlyOn
-/
def MultipliableLocallyUniformlyOn : Prop := exists g, HasProdLocallyUniformlyOn f g s

@[to_additive]
/--
lemma `hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn` / 引理 `hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn`

English:
lemma hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn
  proof: Iff.rfl

中文:
引理 hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn :
    HasProdLocallyUniformlyOn f g s ↔ TendstoLocallyUniformlyOn (∏ i in ·, f i ·) g atTop s :=
  Iff.rfl

/-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∏' i, f i b` converges uniformly
to `g`, then the product converges locally uniformly on `s` to `g`. Note that this is not a
tautology, and the converse is only true if the domain is locally compact. -/
@[to_additive /-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∑' i, f i b`
converges uniformly to `g`, then the sum converges locally uniformly. Note that this is not a
tautology, and the converse is only true if the domain is locally compact. -/]
/--
lemma `hasProdLocallyUniformlyOn_of_of_forall_exists_nhds` / 引理 `hasProdLocallyUniformlyOn_of_of_forall_exists_nhds`

English:
lemma hasProdLocallyUniformlyOn_of_of_forall_exists_nhds
  proof: tendstoLocallyUniformlyOn_of_forall_exists_nhds by
    simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

中文:
引理 hasProdLocallyUniformlyOn_of_of_forall_exists_nhds
  证明: tendstoLocallyUniformlyOn_of_forall_exists_nhds by
    simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

Depends on / 依赖: hasProdUniformlyOn_iff_tendstoUniformlyOn, tendstoLocallyUniformlyOn_of_forall_exists_nhds
-/
lemma hasProdLocallyUniformlyOn_of_of_forall_exists_nhds
    (h : forall x in s, exists t in 𝓝[s] x, HasProdUniformlyOn f g t) : HasProdLocallyUniformlyOn f g s :=
tendstoLocallyUniformlyOn_of_forall_exists_nhds by
    simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

/--
lemma `HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact` / 引理 `HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact`

English:
lemma HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact
  proof: by
  rwa [hasProdUniformlyOn_iff_tendstoUniformlyOn,
    ← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hs]

中文:
引理 HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact
  证明: by
  rwa [hasProdUniformlyOn_iff_tendstoUniformlyOn,
    ← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hs]

Depends on / 依赖: hasProdUniformlyOn_iff_tendstoUniformlyOn, tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
-/
lemma HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact
    (h : HasProdLocallyUniformlyOn f g s) (hs : IsCompact s) : HasProdUniformlyOn f g s := by
  rwa [hasProdUniformlyOn_iff_tendstoUniformlyOn,
    ← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hs]

/--
lemma `HasProdLocallyUniformlyOn.exists_hasProdUniformlyOn` / 引理 `HasProdLocallyUniformlyOn.exists_hasProdUniformlyOn`

English:
lemma HasProdLocallyUniformlyOn.exists_hasProdUniformlyOn
  statement: [LocallyCompactSpace β]
  proof: by
  obtain ⟨K, ⟨hK1, hK2⟩, hK3⟩ := (compact_basis_nhds x).mem_iff.mp hx
  exact ⟨K, nhdsWithin_le_nhds hK1,
    HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact (h.mono hK3) hK2⟩

@[to_additive]

中文:
引理 HasProdLocallyUniformlyOn.exists_hasProdUniformlyOn
  结论: [LocallyCompactSpace β]
  证明: by
  obtain ⟨K, ⟨hK1, hK2⟩, hK3⟩ := (compact_basis_nhds x).mem_iff.mp hx
  exact ⟨K, nhdsWithin_le_nhds hK1,
    HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact (h.mono hK3) hK2⟩

@[to_additive]

Depends on / 依赖: HasProdLocallyUniformlyOn, HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact, compact_basis_nhds, h.mono, hasProdUniformlyOn_of_isCompact, mem_iff, mem_iff.mp, nhdsWithin_le_nhds
-/
lemma HasProdLocallyUniformlyOn.exists_hasProdUniformlyOn [LocallyCompactSpace β]
    (h : HasProdLocallyUniformlyOn f g s) (hx : s in 𝓝 x) :
    exists t in 𝓝[s] x, HasProdUniformlyOn f g t := by
  obtain ⟨K, ⟨hK1, hK2⟩, hK3⟩ := (compact_basis_nhds x).mem_iff.mp hx
  exact ⟨K, nhdsWithin_le_nhds hK1,
    HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact (h.mono hK3) hK2⟩

@[to_additive]
/--
lemma `HasProdUniformlyOn.hasProdLocallyUniformlyOn` / 引理 `HasProdUniformlyOn.hasProdLocallyUniformlyOn`

English:
lemma HasProdUniformlyOn.hasProdLocallyUniformlyOn
  given: (h : HasProdUniformlyOn f g s)
  proof: by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn, HasProdLocallyUniformlyOn] at *
  exact h.tendstoLocallyUniformlyOn

@[to_additive]

中文:
引理 HasProdUniformlyOn.hasProdLocallyUniformlyOn
  条件: (h : HasProdUniformlyOn f g s)
  证明: by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn, HasProdLocallyUniformlyOn] at *
  exact h.tendstoLocallyUniformlyOn

@[to_additive]

Depends on / 依赖: HasProdLocallyUniformlyOn, h.tendstoLocallyUniformlyOn, hasProdUniformlyOn_iff_tendstoUniformlyOn, tendstoLocallyUniformlyOn
-/
lemma HasProdUniformlyOn.hasProdLocallyUniformlyOn (h : HasProdUniformlyOn f g s) :
    HasProdLocallyUniformlyOn f g s := by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn, HasProdLocallyUniformlyOn] at *
  exact h.tendstoLocallyUniformlyOn

@[to_additive]
/--
lemma `hasProdLocallyUniformlyOn_of_forall_compact` / 引理 `hasProdLocallyUniformlyOn_of_forall_compact`

English:
lemma hasProdLocallyUniformlyOn_of_forall_compact
  statement: (hs : IsOpen s) [LocallyCompactSpace β]
  proof: by
  rw [HasProdLocallyUniformlyOn]; rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]

中文:
引理 hasProdLocallyUniformlyOn_of_forall_compact
  结论: (hs : IsOpen s) [LocallyCompactSpace β]
  证明: by
  rw [HasProdLocallyUniformlyOn]; rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]

Depends on / 依赖: HasProdLocallyUniformlyOn, hasProdUniformlyOn_iff_tendstoUniformlyOn, tendstoLocallyUniformlyOn_iff_forall_isCompact
-/
lemma hasProdLocallyUniformlyOn_of_forall_compact (hs : IsOpen s) [LocallyCompactSpace β]
    (h : forall K subseteq s, IsCompact K -> HasProdUniformlyOn f g K) : HasProdLocallyUniformlyOn f g s := by
  rw [HasProdLocallyUniformlyOn]; rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]
/--
theorem `HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn` / 定理 `HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn`

English:
theorem HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
  proof: ⟨g, h⟩

@[to_additive]

中文:
定理 HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
  证明: ⟨g, h⟩

@[to_additive]
-/
theorem HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
    (h : HasProdLocallyUniformlyOn f g s) : MultipliableLocallyUniformlyOn f s :=
  ⟨g, h⟩

@[to_additive]
/--
lemma `HasProdLocallyUniformlyOn.mono` / 引理 `HasProdLocallyUniformlyOn.mono`

English:
lemma HasProdLocallyUniformlyOn.mono
  statement: {t : Set β}
  proof: TendstoLocallyUniformlyOn.mono h hst

@[to_additive]

中文:
引理 HasProdLocallyUniformlyOn.mono
  结论: {t : Set β}
  证明: TendstoLocallyUniformlyOn.mono h hst

@[to_additive]

Depends on / 依赖: TendstoLocallyUniformlyOn, TendstoLocallyUniformlyOn.mono
-/
lemma HasProdLocallyUniformlyOn.mono {t : Set β}
    (h : HasProdLocallyUniformlyOn f g t) (hst : s subseteq t) : HasProdLocallyUniformlyOn f g s :=
  TendstoLocallyUniformlyOn.mono h hst

@[to_additive]
/--
lemma `MultipliableLocallyUniformlyOn.mono` / 引理 `MultipliableLocallyUniformlyOn.mono`

English:
lemma MultipliableLocallyUniformlyOn.mono
  statement: {t : Set β}
  proof: (h.choose_spec.mono hst).multipliableLocallyUniformlyOn

中文:
引理 MultipliableLocallyUniformlyOn.mono
  结论: {t : Set β}
  证明: (h.choose_spec.mono hst).multipliableLocallyUniformlyOn

Depends on / 依赖: choose_spec, h.choose_spec.mono, multipliableLocallyUniformlyOn
-/
lemma MultipliableLocallyUniformlyOn.mono {t : Set β}
    (h : MultipliableLocallyUniformlyOn f t) (hst : s subseteq t) : MultipliableLocallyUniformlyOn f s :=
  (h.choose_spec.mono hst).multipliableLocallyUniformlyOn

/-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∏' i, f i b` converges uniformly,
then the product converges locally uniformly on `s`. Note that this is not a tautology, and the
converse is only true if the domain is locally compact. -/
@[to_additive /-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∑' i, f i b`
converges uniformly, then the sum converges locally uniformly. Note that this is not a tautology,
and the converse is only true if the domain is locally compact. -/]
/--
lemma `multipliableLocallyUniformlyOn_of_of_forall_exists_nhds` / 引理 `multipliableLocallyUniformlyOn_of_of_forall_exists_nhds`

English:
lemma multipliableLocallyUniformlyOn_of_of_forall_exists_nhds
  proof: (hasProdLocallyUniformlyOn_of_of_forall_exists_nhds <| fun x hx => match h x hx with
  | ⟨t, ht, htr⟩ => ⟨t, ht, htr.hasProdUniformlyOn⟩).multipliableLocallyUniformlyOn

中文:
引理 multipliableLocallyUniformlyOn_of_of_forall_exists_nhds
  证明: (hasProdLocallyUniformlyOn_of_of_forall_exists_nhds <| fun x hx => match h x hx with
  | ⟨t, ht, htr⟩ => ⟨t, ht, htr.hasProdUniformlyOn⟩).multipliableLocallyUniformlyOn

Depends on / 依赖: hasProdLocallyUniformlyOn_of_of_forall_exists_nhds, hasProdUniformlyOn, htr.hasProdUniformlyOn, multipliableLocallyUniformlyOn
-/
lemma multipliableLocallyUniformlyOn_of_of_forall_exists_nhds
    (h : forall x in s, exists t in 𝓝[s] x, MultipliableUniformlyOn f t) :
    MultipliableLocallyUniformlyOn f s :=
  (hasProdLocallyUniformlyOn_of_of_forall_exists_nhds <| fun x hx => match h x hx with
  | ⟨t, ht, htr⟩ => ⟨t, ht, htr.hasProdUniformlyOn⟩).multipliableLocallyUniformlyOn

/--
lemma `MultipliableLocallyUniformlyOn.multipliableUniformlyOn_of_isCompact` / 引理 `MultipliableLocallyUniformlyOn.multipliableUniformlyOn_of_isCompact`

English:
lemma MultipliableLocallyUniformlyOn.multipliableUniformlyOn_of_isCompact
  proof: (h.choose_spec.hasProdUniformlyOn_of_isCompact hs).multipliableUniformlyOn

中文:
引理 MultipliableLocallyUniformlyOn.multipliableUniformlyOn_of_isCompact
  证明: (h.choose_spec.hasProdUniformlyOn_of_isCompact hs).multipliableUniformlyOn

Depends on / 依赖: choose_spec, h.choose_spec.hasProdUniformlyOn_of_isCompact, hasProdUniformlyOn_of_isCompact, multipliableUniformlyOn
-/
lemma MultipliableLocallyUniformlyOn.multipliableUniformlyOn_of_isCompact
    (h : MultipliableLocallyUniformlyOn f s) (hs : IsCompact s) : MultipliableUniformlyOn f s :=
  (h.choose_spec.hasProdUniformlyOn_of_isCompact hs).multipliableUniformlyOn

/--
lemma `MultipliableLocallyUniformlyOn.exists_multipliableUniformlyOn` / 引理 `MultipliableLocallyUniformlyOn.exists_multipliableUniformlyOn`

English:
lemma MultipliableLocallyUniformlyOn.exists_multipliableUniformlyOn
  statement: [LocallyCompactSpace β]
  proof: let H := (h.choose_spec.exists_hasProdUniformlyOn hx).choose_spec
  ⟨_, H.1, H.2.multipliableUniformlyOn⟩

@[to_additive]

中文:
引理 MultipliableLocallyUniformlyOn.exists_multipliableUniformlyOn
  结论: [LocallyCompactSpace β]
  证明: let H := (h.choose_spec.exists_hasProdUniformlyOn hx).choose_spec
  ⟨_, H.1, H.2.multipliableUniformlyOn⟩

@[to_additive]

Depends on / 依赖: choose_spec, exists_hasProdUniformlyOn, h.choose_spec.exists_hasProdUniformlyOn, multipliableUniformlyOn
-/
lemma MultipliableLocallyUniformlyOn.exists_multipliableUniformlyOn [LocallyCompactSpace β]
    (h : MultipliableLocallyUniformlyOn f s) (hx : s in 𝓝 x) :
    exists t in 𝓝[s] x, MultipliableUniformlyOn f t :=
  let H := (h.choose_spec.exists_hasProdUniformlyOn hx).choose_spec
  ⟨_, H.1, H.2.multipliableUniformlyOn⟩

@[to_additive]
/--
theorem `HasProdLocallyUniformlyOn.hasProd` / 定理 `HasProdLocallyUniformlyOn.hasProd`

English:
theorem HasProdLocallyUniformlyOn.hasProd
  given: (h : HasProdLocallyUniformlyOn f g s) (hx : x in s)
  proof: h.tendsto_at hx

@[to_additive]

中文:
定理 HasProdLocallyUniformlyOn.hasProd
  条件: (h : HasProdLocallyUniformlyOn f g s) (hx : x in s)
  证明: h.tendsto_at hx

@[to_additive]

Depends on / 依赖: h.tendsto_at, tendsto_at
-/
theorem HasProdLocallyUniformlyOn.hasProd (h : HasProdLocallyUniformlyOn f g s) (hx : x in s) :
    HasProd (f · x) (g x) :=
  h.tendsto_at hx

@[to_additive]
/--
theorem `MultipliableLocallyUniformlyOn.multipliable` / 定理 `MultipliableLocallyUniformlyOn.multipliable`

English:
theorem MultipliableLocallyUniformlyOn.multipliable
  proof: match h with | ⟨_, hg⟩ => (hg.hasProd hx).multipliable

@[to_additive]

中文:
定理 MultipliableLocallyUniformlyOn.multipliable
  证明: match h with | ⟨_, hg⟩ => (hg.hasProd hx).multipliable

@[to_additive]

Depends on / 依赖: hasProd, hg.hasProd, multipliable
-/
theorem MultipliableLocallyUniformlyOn.multipliable
    (h : MultipliableLocallyUniformlyOn f s) (hx : x in s) : Multipliable (f · x) :=
  match h with | ⟨_, hg⟩ => (hg.hasProd hx).multipliable

@[to_additive]
/--
theorem `MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn` / 定理 `MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn`

English:
theorem MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn
  proof: h.elim fun _ hg => hg.congr_inseparable_right fun _ hx =>
    tendsto_nhds_unique_inseparable (hg.hasProd hx) (hg.hasProd hx).multipliable.hasProd

@[to_additive]

中文:
定理 MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn
  证明: h.elim fun _ hg => hg.congr_inseparable_right fun _ hx =>
    tendsto_nhds_unique_inseparable (hg.hasProd hx) (hg.hasProd hx).multipliable.hasProd

@[to_additive]

Depends on / 依赖: congr_inseparable_right, h.elim, hasProd, hg.congr_inseparable_right, hg.hasProd, multipliable, multipliable.hasProd, tendsto_nhds_unique_inseparable
-/
theorem MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn
    (h : MultipliableLocallyUniformlyOn f s) :
    HasProdLocallyUniformlyOn f (∏' i, f i ·) s :=
  h.elim fun _ hg => hg.congr_inseparable_right fun _ hx =>
    tendsto_nhds_unique_inseparable (hg.hasProd hx) (hg.hasProd hx).multipliable.hasProd

@[to_additive]
/--
theorem `HasProdLocallyUniformlyOn.tprod_eqOn` / 定理 `HasProdLocallyUniformlyOn.tprod_eqOn`

English:
theorem HasProdLocallyUniformlyOn.tprod_eqOn
  statement: [T2Space α]
  proof: fun _ hx => (h.hasProd hx).tprod_eq

@[to_additive]

中文:
定理 HasProdLocallyUniformlyOn.tprod_eqOn
  结论: [T2Space α]
  证明: fun _ hx => (h.hasProd hx).tprod_eq

@[to_additive]

Depends on / 依赖: h.hasProd, hasProd, tprod_eq
-/
theorem HasProdLocallyUniformlyOn.tprod_eqOn [T2Space α]
    (h : HasProdLocallyUniformlyOn f g s) : Set.EqOn (∏' i, f i ·) g s :=
  fun _ hx => (h.hasProd hx).tprod_eq

@[to_additive]
/--
lemma `MultipliableLocallyUniformlyOn_congr` / 引理 `MultipliableLocallyUniformlyOn_congr`

English:
lemma MultipliableLocallyUniformlyOn_congr
  proof: by
  apply HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
  exact (h2.hasProdLocallyUniformlyOn).congr fun v => eqOn_fun_finsetProd h v

@[to_additive]

中文:
引理 MultipliableLocallyUniformlyOn_congr
  证明: by
  apply HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
  exact (h2.hasProdLocallyUniformlyOn).congr fun v => eqOn_fun_finsetProd h v

@[to_additive]

Depends on / 依赖: HasProdLocallyUniformlyOn, HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn, eqOn_fun_finsetProd, h2.hasProdLocallyUniformlyOn, hasProdLocallyUniformlyOn, multipliableLocallyUniformlyOn
-/
lemma MultipliableLocallyUniformlyOn_congr
    {f f' : ι -> β -> α} (h : forall i, s.EqOn (f i) (f' i))
    (h2 : MultipliableLocallyUniformlyOn f s) : MultipliableLocallyUniformlyOn f' s := by
  apply HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
  exact (h2.hasProdLocallyUniformlyOn).congr fun v => eqOn_fun_finsetProd h v

@[to_additive]
/--
theorem `HasProdLocallyUniformlyOn.comp` / 定理 `HasProdLocallyUniformlyOn.comp`

English:
theorem HasProdLocallyUniformlyOn.comp
  statement: {γ : Type*} [TopologicalSpace γ] {t : Set γ}
  proof: TendstoLocallyUniformlyOn.comp h h' hh chh

@[to_additive]

中文:
定理 HasProdLocallyUniformlyOn.comp
  结论: {γ : 类型} [TopologicalSpace γ] {t : Set γ}
  证明: TendstoLocallyUniformlyOn.comp h h' hh chh

@[to_additive]

Depends on / 依赖: TendstoLocallyUniformlyOn, TendstoLocallyUniformlyOn.comp
-/
theorem HasProdLocallyUniformlyOn.comp {γ : Type*} [TopologicalSpace γ] {t : Set γ}
    (h : HasProdLocallyUniformlyOn f g s) (h' : γ -> β) (hh : Set.MapsTo h' t s)
    (chh : ContinuousOn h' t) :
    HasProdLocallyUniformlyOn (fun i y => f i (h' y)) (g ∘ h') t :=
  TendstoLocallyUniformlyOn.comp h h' hh chh

@[to_additive]
/--
theorem `MultipliableLocallyUniformlyOn.comp` / 定理 `MultipliableLocallyUniformlyOn.comp`

English:
theorem MultipliableLocallyUniformlyOn.comp
  statement: {γ : Type*} [TopologicalSpace γ] {t : Set γ}
  proof: (h.hasProdLocallyUniformlyOn.comp h' hh chh).multipliableLocallyUniformlyOn

@[to_additive]

中文:
定理 MultipliableLocallyUniformlyOn.comp
  结论: {γ : 类型} [TopologicalSpace γ] {t : Set γ}
  证明: (h.hasProdLocallyUniformlyOn.comp h' hh chh).multipliableLocallyUniformlyOn

@[to_additive]

Depends on / 依赖: h.hasProdLocallyUniformlyOn.comp, hasProdLocallyUniformlyOn, multipliableLocallyUniformlyOn
-/
theorem MultipliableLocallyUniformlyOn.comp {γ : Type*} [TopologicalSpace γ] {t : Set γ}
    (h : MultipliableLocallyUniformlyOn f s) (h' : γ -> β) (hh : Set.MapsTo h' t s)
    (chh : ContinuousOn h' t) : MultipliableLocallyUniformlyOn (fun i y => f i (h' y)) t :=
  (h.hasProdLocallyUniformlyOn.comp h' hh chh).multipliableLocallyUniformlyOn

@[to_additive]
/--
lemma `HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange` / 引理 `HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange`

English:
lemma HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
  proof: by
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h
  intro v hv r hr
  obtain ⟨t, ht, htr⟩ := h v hv r hr
  exact ⟨t, ht, Filter.tendsto_finset_range.eventually htr⟩

@[to_additive]

中文:
引理 HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
  证明: by
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h
  intro v hv r hr
  obtain ⟨t, ht, htr⟩ := h v hv r hr
  exact ⟨t, ht, Filter.tendsto_finset_range.eventually htr⟩

@[to_additive]

Depends on / 依赖: Filter, Filter.tendsto_finset_range.eventually, eventually, hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn, tendsto_finset_range
-/
lemma HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
    {f : Nat -> β -> α} (h : HasProdLocallyUniformlyOn f g s) :
    TendstoLocallyUniformlyOn (fun N b => ∏ i in Finset.range N, f i b) g atTop s := by
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h
  intro v hv r hr
  obtain ⟨t, ht, htr⟩ := h v hv r hr
  exact ⟨t, ht, Filter.tendsto_finset_range.eventually htr⟩

@[to_additive]
/--
theorem `multipliableLocallyUniformlyOn_iff_hasProdLocallyUniformlyOn` / 定理 `multipliableLocallyUniformlyOn_iff_hasProdLocallyUniformlyOn`

English:
theorem multipliableLocallyUniformlyOn_iff_hasProdLocallyUniformlyOn
  proof: ⟨MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn,
    HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn⟩

中文:
定理 multipliableLocallyUniformlyOn_iff_hasProdLocallyUniformlyOn
  证明: ⟨MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn,
    HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn⟩

Depends on / 依赖: HasProdLocallyUniformlyOn, HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn, MultipliableLocallyUniformlyOn, MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn, hasProdLocallyUniformlyOn, multipliableLocallyUniformlyOn
-/
theorem multipliableLocallyUniformlyOn_iff_hasProdLocallyUniformlyOn :
    MultipliableLocallyUniformlyOn f s ↔ HasProdLocallyUniformlyOn f (∏' i, f i ·) s :=
  ⟨MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn,
    HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn⟩

end LocallyUniformlyOn

section Uniformly

variable (f g) in
/-- `HasProdUniformly f g` means that
the product `∏ i, f i b` converges uniformly (wrt `b`) to `g`. -/
@[to_additive /-- `HasSumUniformly f g` means that
the sum `∑ i, f i b` converges uniformly (wrt `b`) to `g`. -/]
/--
Definition of `HasProdUniformly` / `HasProdUniformly` 的定义

English:
definition HasProdUniformly
  signature: : Prop
  body: HasProd (UniformFun.ofFun ∘ f) (UniformFun.ofFun g)

中文:
定义 HasProdUniformly
  签名: : 命题
  定义体: HasProd (UniformFun.ofFun ∘ f) (UniformFun.ofFun g)

Depends on / 依赖: HasProd, UniformFun, UniformFun.ofFun
-/
def HasProdUniformly : Prop := HasProd (UniformFun.ofFun ∘ f) (UniformFun.ofFun g)

variable (f g) in
/-- `MultipliableUniformly f` means that there is some infinite product to which
`f` converges uniformly. Use `fun x ↦ ∏' i, f i x` to get the product function. -/
@[to_additive /-- `SummableUniformly f` means that there is some infinite sum to which
`f` converges uniformly. Use `fun x ↦ ∑' i, f i x` to get the product function. -/]
/--
Definition of `MultipliableUniformly` / `MultipliableUniformly` 的定义

English:
definition MultipliableUniformly
  signature: : Prop
  body: Multipliable (UniformFun.ofFun ∘ f)

@[to_additive]

中文:
定义 MultipliableUniformly
  签名: : 命题
  定义体: Multipliable (UniformFun.ofFun ∘ f)

@[to_additive]

Depends on / 依赖: Multipliable, UniformFun, UniformFun.ofFun
-/
def MultipliableUniformly : Prop := Multipliable (UniformFun.ofFun ∘ f)

@[to_additive]
/--
lemma `MultipliableUniformly.exists` / 引理 `MultipliableUniformly.exists`

English:
lemma MultipliableUniformly.exists
  given: (h : MultipliableUniformly f)
  proof: h

@[to_additive]

中文:
引理 MultipliableUniformly.exists
  条件: (h : MultipliableUniformly f)
  证明: h

@[to_additive]
-/
lemma MultipliableUniformly.exists (h : MultipliableUniformly f) :
    exists g, HasProdUniformly f g :=
  h

@[to_additive]
/--
theorem `HasProdUniformly.multipliableUniformly` / 定理 `HasProdUniformly.multipliableUniformly`

English:
theorem HasProdUniformly.multipliableUniformly
  given: (h : HasProdUniformly f g)
  proof: ⟨g, h⟩

@[to_additive]

中文:
定理 HasProdUniformly.multipliableUniformly
  条件: (h : HasProdUniformly f g)
  证明: ⟨g, h⟩

@[to_additive]
-/
theorem HasProdUniformly.multipliableUniformly (h : HasProdUniformly f g) :
    MultipliableUniformly f :=
  ⟨g, h⟩

@[to_additive]
/--
lemma `hasProdUniformly_iff_tendstoUniformly` / 引理 `hasProdUniformly_iff_tendstoUniformly`

English:
lemma hasProdUniformly_iff_tendstoUniformly
  proof: by
  simpa [HasProdUniformly, HasProd, ← UniformFun.ofFun_prod, Finset.prod_fn] using!
    UniformFun.tendsto_iff_tendstoUniformly

@[to_additive]
alias ⟨HasProdUniformly.tendstoUniformly, _⟩ := hasProdUniformly_iff_tendstoUniformly

@[to_additive]

中文:
引理 hasProdUniformly_iff_tendstoUniformly
  证明: by
  simpa [HasProdUniformly, HasProd, ← UniformFun.ofFun_prod, Finset.prod_fn] using!
    UniformFun.tendsto_iff_tendstoUniformly

@[to_additive]
alias ⟨HasProdUniformly.tendstoUniformly, _⟩ := hasProdUniformly_iff_tendstoUniformly

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_fn, HasProd, HasProdUniformly, UniformFun, UniformFun.ofFun_prod, UniformFun.tendsto_iff_tendstoUniformly, ofFun_prod, prod_fn, tendsto_iff_tendstoUniformly
-/
lemma hasProdUniformly_iff_tendstoUniformly :
    HasProdUniformly f g ↔ TendstoUniformly (∏ i in ·, f i ·) g atTop := by
  simpa [HasProdUniformly, HasProd, ← UniformFun.ofFun_prod, Finset.prod_fn] using!
    UniformFun.tendsto_iff_tendstoUniformly

@[to_additive]
alias ⟨HasProdUniformly.tendstoUniformly, _⟩ := hasProdUniformly_iff_tendstoUniformly

@[to_additive]
/--
theorem `HasProdUniformly.hasProdUniformlyOn` / 定理 `HasProdUniformly.hasProdUniformlyOn`

English:
theorem HasProdUniformly.hasProdUniformlyOn
  given: (h : HasProdUniformly f g)
  proof: hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr h.tendstoUniformly.tendstoUniformlyOn

@[to_additive]

中文:
定理 HasProdUniformly.hasProdUniformlyOn
  条件: (h : HasProdUniformly f g)
  证明: hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr h.tendstoUniformly.tendstoUniformlyOn

@[to_additive]

Depends on / 依赖: h.tendstoUniformly.tendstoUniformlyOn, hasProdUniformlyOn_iff_tendstoUniformlyOn, hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr, tendstoUniformly, tendstoUniformlyOn
-/
theorem HasProdUniformly.hasProdUniformlyOn (h : HasProdUniformly f g) :
    HasProdUniformlyOn f g s :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr h.tendstoUniformly.tendstoUniformlyOn

@[to_additive]
/--
lemma `hasProdUniformlyOn_univ_iff` / 引理 `hasProdUniformlyOn_univ_iff`

English:
lemma hasProdUniformlyOn_univ_iff
  proof: by
  simp [hasProdUniformly_iff_tendstoUniformly, hasProdUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_univ]

@[to_additive]

中文:
引理 hasProdUniformlyOn_univ_iff
  证明: by
  simp [hasProdUniformly_iff_tendstoUniformly, hasProdUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_univ]

@[to_additive]

Depends on / 依赖: hasProdUniformlyOn_iff_tendstoUniformlyOn, hasProdUniformly_iff_tendstoUniformly, tendstoUniformlyOn_univ
-/
lemma hasProdUniformlyOn_univ_iff :
    HasProdUniformlyOn f g .univ ↔ HasProdUniformly f g := by
  simp [hasProdUniformly_iff_tendstoUniformly, hasProdUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_univ]

@[to_additive]
/--
theorem `MultipliableUniformly.multipliableUniformlyOn` / 定理 `MultipliableUniformly.multipliableUniformlyOn`

English:
theorem MultipliableUniformly.multipliableUniformlyOn
  given: (h : MultipliableUniformly f)
  proof: h.exists.choose_spec.hasProdUniformlyOn.multipliableUniformlyOn

@[to_additive]

中文:
定理 MultipliableUniformly.multipliableUniformlyOn
  条件: (h : MultipliableUniformly f)
  证明: h.exists.choose_spec.hasProdUniformlyOn.multipliableUniformlyOn

@[to_additive]

Depends on / 依赖: choose_spec, h.exists.choose_spec.hasProdUniformlyOn.multipliableUniformlyOn, hasProdUniformlyOn, multipliableUniformlyOn
-/
theorem MultipliableUniformly.multipliableUniformlyOn (h : MultipliableUniformly f) :
    MultipliableUniformlyOn f s :=
  h.exists.choose_spec.hasProdUniformlyOn.multipliableUniformlyOn

@[to_additive]
/--
lemma `multipliableUniformlyOn_univ_iff` / 引理 `multipliableUniformlyOn_univ_iff`

English:
lemma multipliableUniformlyOn_univ_iff
  proof: ⟨fun h => (hasProdUniformlyOn_univ_iff.mp h.exists.choose_spec).multipliableUniformly,
    MultipliableUniformly.multipliableUniformlyOn⟩

@[to_additive]

中文:
引理 multipliableUniformlyOn_univ_iff
  证明: ⟨fun h => (hasProdUniformlyOn_univ_iff.mp h.exists.choose_spec).multipliableUniformly,
    MultipliableUniformly.multipliableUniformlyOn⟩

@[to_additive]

Depends on / 依赖: MultipliableUniformly, MultipliableUniformly.multipliableUniformlyOn, choose_spec, h.exists.choose_spec, hasProdUniformlyOn_univ_iff, hasProdUniformlyOn_univ_iff.mp, multipliableUniformly, multipliableUniformlyOn
-/
lemma multipliableUniformlyOn_univ_iff :
    MultipliableUniformlyOn f .univ ↔ MultipliableUniformly f :=
  ⟨fun h => (hasProdUniformlyOn_univ_iff.mp h.exists.choose_spec).multipliableUniformly,
    MultipliableUniformly.multipliableUniformlyOn⟩

@[to_additive]
/--
lemma `HasProdUniformly.congr` / 引理 `HasProdUniformly.congr`

English:
lemma HasProdUniformly.congr
  statement: {f' : ι -> β -> α}
  proof: by
  rw [hasProdUniformly_iff_tendstoUniformly] at *
  exact (tendstoUniformly_congr (by simpa only [EventuallyEq, funext_iff])).mp h

@[to_additive]

中文:
引理 HasProdUniformly.congr
  结论: {f' : ι -> β -> α}
  证明: by
  rw [hasProdUniformly_iff_tendstoUniformly] at *
  exact (tendstoUniformly_congr (by simpa only [EventuallyEq, funext_iff])).mp h

@[to_additive]

Depends on / 依赖: EventuallyEq, funext_iff, hasProdUniformly_iff_tendstoUniformly, tendstoUniformly_congr
-/
lemma HasProdUniformly.congr {f' : ι -> β -> α}
    (h : HasProdUniformly f g)
    (hff' : forallᶠ (n : Finset ι) in atTop, forall b, ∏ i in n, f i b = ∏ i in n, f' i b) :
    HasProdUniformly f' g := by
  rw [hasProdUniformly_iff_tendstoUniformly] at *
  exact (tendstoUniformly_congr (by simpa only [EventuallyEq, funext_iff])).mp h

@[to_additive]
/--
lemma `HasProdUniformly.tendstoUniformlyOn_finsetRange` / 引理 `HasProdUniformly.tendstoUniformlyOn_finsetRange`

English:
lemma HasProdUniformly.tendstoUniformlyOn_finsetRange
  given: {f : Nat -> β -> α} (h : HasProdUniformly f g)
  proof: (tendsto_finset_range.eventually <| h.tendstoUniformly · ·)

@[to_additive]

中文:
引理 HasProdUniformly.tendstoUniformlyOn_finsetRange
  条件: {f : 自然数 -> β -> α} (h : HasProdUniformly f g)
  证明: (tendsto_finset_range.eventually <| h.tendstoUniformly · ·)

@[to_additive]

Depends on / 依赖: eventually, h.tendstoUniformly, tendstoUniformly, tendsto_finset_range, tendsto_finset_range.eventually
-/
lemma HasProdUniformly.tendstoUniformlyOn_finsetRange {f : Nat -> β -> α} (h : HasProdUniformly f g) :
    TendstoUniformly (∏ i in Finset.range ·, f i ·) g atTop :=
  (tendsto_finset_range.eventually <| h.tendstoUniformly · ·)

@[to_additive]
/--
theorem `HasProdUniformly.hasProd` / 定理 `HasProdUniformly.hasProd`

English:
theorem HasProdUniformly.hasProd
  given: (h : HasProdUniformly f g)
  statement: HasProd (f · x) (g x)
  proof: h.tendstoUniformly.tendsto_at _

@[to_additive]

中文:
定理 HasProdUniformly.hasProd
  条件: (h : HasProdUniformly f g)
  结论: HasProd (f · x) (g x)
  证明: h.tendstoUniformly.tendsto_at _

@[to_additive]

Depends on / 依赖: h.tendstoUniformly.tendsto_at, tendstoUniformly, tendsto_at
-/
theorem HasProdUniformly.hasProd (h : HasProdUniformly f g) : HasProd (f · x) (g x) :=
  h.tendstoUniformly.tendsto_at _

@[to_additive]
/--
theorem `MultipliableUniformly.multipliable` / 定理 `MultipliableUniformly.multipliable`

English:
theorem MultipliableUniformly.multipliable
  given: (h : MultipliableUniformly f)
  statement: Multipliable (f · x)
  proof: h.exists.choose_spec.hasProd.multipliable

@[to_additive]

中文:
定理 MultipliableUniformly.multipliable
  条件: (h : MultipliableUniformly f)
  结论: Multipliable (f · x)
  证明: h.exists.choose_spec.hasProd.multipliable

@[to_additive]

Depends on / 依赖: choose_spec, h.exists.choose_spec.hasProd.multipliable, hasProd, multipliable
-/
theorem MultipliableUniformly.multipliable (h : MultipliableUniformly f) : Multipliable (f · x) :=
  h.exists.choose_spec.hasProd.multipliable

@[to_additive]
/--
theorem `MultipliableUniformly.hasProdUniformly` / 定理 `MultipliableUniformly.hasProdUniformly`

English:
theorem MultipliableUniformly.hasProdUniformly
  given: (h : MultipliableUniformly f)
  proof: hasProdUniformlyOn_univ_iff.1 (multipliableUniformlyOn_univ_iff.2 h).hasProdUniformlyOn

@[to_additive]

中文:
定理 MultipliableUniformly.hasProdUniformly
  条件: (h : MultipliableUniformly f)
  证明: hasProdUniformlyOn_univ_iff.1 (multipliableUniformlyOn_univ_iff.2 h).hasProdUniformlyOn

@[to_additive]

Depends on / 依赖: hasProdUniformlyOn, hasProdUniformlyOn_univ_iff, multipliableUniformlyOn_univ_iff
-/
theorem MultipliableUniformly.hasProdUniformly (h : MultipliableUniformly f) :
    HasProdUniformly f (∏' i, f i ·) :=
  hasProdUniformlyOn_univ_iff.1 (multipliableUniformlyOn_univ_iff.2 h).hasProdUniformlyOn

@[to_additive]
/--
theorem `multipliableUniformly_iff_hasProdUniformly` / 定理 `multipliableUniformly_iff_hasProdUniformly`

English:
theorem multipliableUniformly_iff_hasProdUniformly
  proof: ⟨MultipliableUniformly.hasProdUniformly, HasProdUniformly.multipliableUniformly⟩

中文:
定理 multipliableUniformly_iff_hasProdUniformly
  证明: ⟨MultipliableUniformly.hasProdUniformly, HasProdUniformly.multipliableUniformly⟩

Depends on / 依赖: HasProdUniformly, HasProdUniformly.multipliableUniformly, MultipliableUniformly, MultipliableUniformly.hasProdUniformly, hasProdUniformly, multipliableUniformly
-/
theorem multipliableUniformly_iff_hasProdUniformly :
    MultipliableUniformly f ↔ HasProdUniformly f (∏' i, f i ·) :=
  ⟨MultipliableUniformly.hasProdUniformly, HasProdUniformly.multipliableUniformly⟩

end Uniformly

section LocallyUniformly
/-!
## Locally uniform convergence of sums and products
-/

variable [TopologicalSpace β]

variable (f g) in
/-- `HasProdLocallyUniformly f g` means that the (potentially infinite) product `∏' i, f i b`
for `b : β` converges locally uniformly to `g b` (in the sense of
`TendstoLocallyUniformly`). -/
@[to_additive /-- `HasSumLocallyUniformly f g` means that the (potentially infinite) sum
`∑' i, f i b` for `b : β` converges locally uniformly to `g b` (in the sense of
`TendstoLocallyUniformly`). -/]
/--
Definition of `HasProdLocallyUniformly` / `HasProdLocallyUniformly` 的定义

English:
definition HasProdLocallyUniformly
  signature: : Prop
  body: TendstoLocallyUniformly (∏ i in ·, f i ·) g atTop

中文:
定义 HasProdLocallyUniformly
  签名: : 命题
  定义体: TendstoLocallyUniformly (∏ i in ·, f i ·) g atTop

Depends on / 依赖: TendstoLocallyUniformly
-/
def HasProdLocallyUniformly : Prop := TendstoLocallyUniformly (∏ i in ·, f i ·) g atTop

variable (f g) in
/-- `MultipliableLocallyUniformly f` means that the product `∏' i, f i b` converges locally
uniformly to something. -/
@[to_additive /-- `SummableLocallyUniformly f` means that `∑' i, f i b` converges locally
uniformly to something. -/]
/--
Definition of `MultipliableLocallyUniformly` / `MultipliableLocallyUniformly` 的定义

English:
definition MultipliableLocallyUniformly
  signature: : Prop
  body: exists g, HasProdLocallyUniformly f g

@[to_additive]

中文:
定义 MultipliableLocallyUniformly
  签名: : 命题
  定义体: exists g, HasProdLocallyUniformly f g

@[to_additive]

Depends on / 依赖: HasProdLocallyUniformly
-/
def MultipliableLocallyUniformly : Prop := exists g, HasProdLocallyUniformly f g

@[to_additive]
/--
lemma `MultipliableLocallyUniformly.exists` / 引理 `MultipliableLocallyUniformly.exists`

English:
lemma MultipliableLocallyUniformly.exists
  given: (h : MultipliableLocallyUniformly f)
  proof: h

@[to_additive]

中文:
引理 MultipliableLocallyUniformly.exists
  条件: (h : MultipliableLocallyUniformly f)
  证明: h

@[to_additive]
-/
lemma MultipliableLocallyUniformly.exists (h : MultipliableLocallyUniformly f) :
    exists g, HasProdLocallyUniformly f g := h

@[to_additive]
/--
theorem `HasProdLocallyUniformly.multipliableLocallyUniformly` / 定理 `HasProdLocallyUniformly.multipliableLocallyUniformly`

English:
theorem HasProdLocallyUniformly.multipliableLocallyUniformly
  proof: ⟨g, h⟩

@[to_additive]

中文:
定理 HasProdLocallyUniformly.multipliableLocallyUniformly
  证明: ⟨g, h⟩

@[to_additive]
-/
theorem HasProdLocallyUniformly.multipliableLocallyUniformly
    (h : HasProdLocallyUniformly f g) : MultipliableLocallyUniformly f :=
  ⟨g, h⟩

@[to_additive]
/--
lemma `hasProdLocallyUniformly_iff_tendstoLocallyUniformly` / 引理 `hasProdLocallyUniformly_iff_tendstoLocallyUniformly`

English:
lemma hasProdLocallyUniformly_iff_tendstoLocallyUniformly
  proof: .rfl

@[to_additive]

中文:
引理 hasProdLocallyUniformly_iff_tendstoLocallyUniformly
  证明: .rfl

@[to_additive]
-/
lemma hasProdLocallyUniformly_iff_tendstoLocallyUniformly :
    HasProdLocallyUniformly f g ↔ TendstoLocallyUniformly (∏ i in ·, f i ·) g atTop :=
  .rfl

@[to_additive]
/--
theorem `HasProdLocallyUniformly.hasProdLocallyUniformlyOn` / 定理 `HasProdLocallyUniformly.hasProdLocallyUniformlyOn`

English:
theorem HasProdLocallyUniformly.hasProdLocallyUniformlyOn
  given: (h : HasProdLocallyUniformly f g)
  proof: h.tendstoLocallyUniformlyOn

@[to_additive]

中文:
定理 HasProdLocallyUniformly.hasProdLocallyUniformlyOn
  条件: (h : HasProdLocallyUniformly f g)
  证明: h.tendstoLocallyUniformlyOn

@[to_additive]

Depends on / 依赖: h.tendstoLocallyUniformlyOn, tendstoLocallyUniformlyOn
-/
theorem HasProdLocallyUniformly.hasProdLocallyUniformlyOn (h : HasProdLocallyUniformly f g) :
    HasProdLocallyUniformlyOn f g s :=
  h.tendstoLocallyUniformlyOn

@[to_additive]
/--
theorem `MultipliableLocallyUniformly.multipliableLocallyUniformlyOn` / 定理 `MultipliableLocallyUniformly.multipliableLocallyUniformlyOn`

English:
theorem MultipliableLocallyUniformly.multipliableLocallyUniformlyOn
  proof: h.exists.choose_spec.hasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn

中文:
定理 MultipliableLocallyUniformly.multipliableLocallyUniformlyOn
  证明: h.exists.choose_spec.hasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn

Depends on / 依赖: choose_spec, h.exists.choose_spec.hasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn, hasProdLocallyUniformlyOn, multipliableLocallyUniformlyOn
-/
theorem MultipliableLocallyUniformly.multipliableLocallyUniformlyOn
    (h : MultipliableLocallyUniformly f) :
    MultipliableLocallyUniformlyOn f s :=
  h.exists.choose_spec.hasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn

/-- If every `x` has a neighbourhood on which `b ↦ ∏' i, f i b` converges uniformly
to `g`, then the product converges locally uniformly to `g`. Note that this is not a
tautology, and the converse is only true if the domain is locally compact. -/
@[to_additive /-- If every `x` has a neighbourhood on which `b ↦ ∑' i, f i b`
converges uniformly to `g`, then the sum converges locally uniformly. Note that this is not a
tautology, and the converse is only true if the domain is locally compact. -/]
/--
lemma `hasProdLocallyUniformly_of_of_forall_exists_nhds` / 引理 `hasProdLocallyUniformly_of_of_forall_exists_nhds`

English:
lemma hasProdLocallyUniformly_of_of_forall_exists_nhds
  proof: tendstoLocallyUniformly_of_forall_exists_nhds by
    simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]

中文:
引理 hasProdLocallyUniformly_of_of_forall_exists_nhds
  证明: tendstoLocallyUniformly_of_forall_exists_nhds by
    simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]

Depends on / 依赖: hasProdUniformlyOn_iff_tendstoUniformlyOn, tendstoLocallyUniformly_of_forall_exists_nhds
-/
lemma hasProdLocallyUniformly_of_of_forall_exists_nhds
    (h : forall x, exists t in 𝓝 x, HasProdUniformlyOn f g t) : HasProdLocallyUniformly f g :=
tendstoLocallyUniformly_of_forall_exists_nhds by
    simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]
/--
lemma `HasProdUniformly.hasProdLocallyUniformly` / 引理 `HasProdUniformly.hasProdLocallyUniformly`

English:
lemma HasProdUniformly.hasProdLocallyUniformly
  given: (h : HasProdUniformly f g)
  proof: by
  simp only [hasProdUniformly_iff_tendstoUniformly, HasProdLocallyUniformly] at *
  exact TendstoUniformly.tendstoLocallyUniformly h

@[to_additive]

中文:
引理 HasProdUniformly.hasProdLocallyUniformly
  条件: (h : HasProdUniformly f g)
  证明: by
  simp only [hasProdUniformly_iff_tendstoUniformly, HasProdLocallyUniformly] at *
  exact TendstoUniformly.tendstoLocallyUniformly h

@[to_additive]

Depends on / 依赖: HasProdLocallyUniformly, TendstoUniformly, TendstoUniformly.tendstoLocallyUniformly, hasProdUniformly_iff_tendstoUniformly, tendstoLocallyUniformly
-/
lemma HasProdUniformly.hasProdLocallyUniformly (h : HasProdUniformly f g) :
    HasProdLocallyUniformly f g := by
  simp only [hasProdUniformly_iff_tendstoUniformly, HasProdLocallyUniformly] at *
  exact TendstoUniformly.tendstoLocallyUniformly h

@[to_additive]
/--
lemma `hasProdLocallyUniformly_of_forall_compact` / 引理 `hasProdLocallyUniformly_of_forall_compact`

English:
lemma hasProdLocallyUniformly_of_forall_compact
  statement: [LocallyCompactSpace β]
  proof: by
  rw [HasProdLocallyUniformly]; rw [tendstoLocallyUniformly_iff_forall_isCompact]
  simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]

中文:
引理 hasProdLocallyUniformly_of_forall_compact
  结论: [LocallyCompactSpace β]
  证明: by
  rw [HasProdLocallyUniformly]; rw [tendstoLocallyUniformly_iff_forall_isCompact]
  simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]

Depends on / 依赖: HasProdLocallyUniformly, hasProdUniformlyOn_iff_tendstoUniformlyOn, tendstoLocallyUniformly_iff_forall_isCompact
-/
lemma hasProdLocallyUniformly_of_forall_compact [LocallyCompactSpace β]
    (h : forall K, IsCompact K -> HasProdUniformlyOn f g K) : HasProdLocallyUniformly f g := by
  rw [HasProdLocallyUniformly]; rw [tendstoLocallyUniformly_iff_forall_isCompact]
  simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]
/--
lemma `multipliableLocallyUniformly_of_of_forall_exists_nhds` / 引理 `multipliableLocallyUniformly_of_of_forall_exists_nhds`

English:
lemma multipliableLocallyUniformly_of_of_forall_exists_nhds
  proof: hasProdLocallyUniformly_of_of_forall_exists_nhds
    (fun x => (h x).imp fun _ ht => ⟨ht.1, ht.2.hasProdUniformlyOn⟩)
.multipliableLocallyUniformly

@[to_additive]

中文:
引理 multipliableLocallyUniformly_of_of_forall_exists_nhds
  证明: hasProdLocallyUniformly_of_of_forall_exists_nhds
    (fun x => (h x).imp fun _ ht => ⟨ht.1, ht.2.hasProdUniformlyOn⟩)
.multipliableLocallyUniformly

@[to_additive]

Depends on / 依赖: hasProdLocallyUniformly_of_of_forall_exists_nhds, hasProdUniformlyOn, multipliableLocallyUniformly
-/
lemma multipliableLocallyUniformly_of_of_forall_exists_nhds
    (h : forall x, exists t in 𝓝 x, MultipliableUniformlyOn f t) :
    MultipliableLocallyUniformly f :=
  hasProdLocallyUniformly_of_of_forall_exists_nhds
    (fun x => (h x).imp fun _ ht => ⟨ht.1, ht.2.hasProdUniformlyOn⟩)
.multipliableLocallyUniformly

@[to_additive]
/--
theorem `HasProdLocallyUniformly.hasProd` / 定理 `HasProdLocallyUniformly.hasProd`

English:
theorem HasProdLocallyUniformly.hasProd
  given: (h : HasProdLocallyUniformly f g)
  statement: HasProd (f · x) (g x)
  proof: h.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x)

@[to_additive]

中文:
定理 HasProdLocallyUniformly.hasProd
  条件: (h : HasProdLocallyUniformly f g)
  结论: HasProd (f · x) (g x)
  证明: h.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x)

@[to_additive]

Depends on / 依赖: Set.mem_univ, h.tendstoLocallyUniformlyOn.tendsto_at, mem_univ, tendstoLocallyUniformlyOn, tendsto_at
-/
theorem HasProdLocallyUniformly.hasProd (h : HasProdLocallyUniformly f g) : HasProd (f · x) (g x) :=
  h.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x)

@[to_additive]
/--
theorem `MultipliableLocallyUniformly.multipliable` / 定理 `MultipliableLocallyUniformly.multipliable`

English:
theorem MultipliableLocallyUniformly.multipliable
  proof: h.choose_spec.hasProd.multipliable

@[to_additive]

中文:
定理 MultipliableLocallyUniformly.multipliable
  证明: h.choose_spec.hasProd.multipliable

@[to_additive]

Depends on / 依赖: choose_spec, h.choose_spec.hasProd.multipliable, hasProd, multipliable
-/
theorem MultipliableLocallyUniformly.multipliable
    (h : MultipliableLocallyUniformly f) : Multipliable (f · x) :=
  h.choose_spec.hasProd.multipliable

@[to_additive]
/--
theorem `MultipliableLocallyUniformly.hasProdLocallyUniformly` / 定理 `MultipliableLocallyUniformly.hasProdLocallyUniformly`

English:
theorem MultipliableLocallyUniformly.hasProdLocallyUniformly
  proof: h.elim fun _ hg => hg.congr_inseparable_right fun _ =>
    tendsto_nhds_unique_inseparable hg.hasProd hg.hasProd.multipliable.hasProd

@[to_additive]

中文:
定理 MultipliableLocallyUniformly.hasProdLocallyUniformly
  证明: h.elim fun _ hg => hg.congr_inseparable_right fun _ =>
    tendsto_nhds_unique_inseparable hg.hasProd hg.hasProd.multipliable.hasProd

@[to_additive]

Depends on / 依赖: congr_inseparable_right, h.elim, hasProd, hg.congr_inseparable_right, hg.hasProd, hg.hasProd.multipliable.hasProd, multipliable, tendsto_nhds_unique_inseparable
-/
theorem MultipliableLocallyUniformly.hasProdLocallyUniformly
    (h : MultipliableLocallyUniformly f) :
    HasProdLocallyUniformly f (∏' i, f i ·) :=
  h.elim fun _ hg => hg.congr_inseparable_right fun _ =>
    tendsto_nhds_unique_inseparable hg.hasProd hg.hasProd.multipliable.hasProd

@[to_additive]
/--
theorem `multipliableLocallyUniformly_iff_hasProdLocallyUniformly` / 定理 `multipliableLocallyUniformly_iff_hasProdLocallyUniformly`

English:
theorem multipliableLocallyUniformly_iff_hasProdLocallyUniformly
  proof: ⟨MultipliableLocallyUniformly.hasProdLocallyUniformly,
    HasProdLocallyUniformly.multipliableLocallyUniformly⟩

@[to_additive]

中文:
定理 multipliableLocallyUniformly_iff_hasProdLocallyUniformly
  证明: ⟨MultipliableLocallyUniformly.hasProdLocallyUniformly,
    HasProdLocallyUniformly.multipliableLocallyUniformly⟩

@[to_additive]

Depends on / 依赖: HasProdLocallyUniformly, HasProdLocallyUniformly.multipliableLocallyUniformly, MultipliableLocallyUniformly, MultipliableLocallyUniformly.hasProdLocallyUniformly, hasProdLocallyUniformly, multipliableLocallyUniformly
-/
theorem multipliableLocallyUniformly_iff_hasProdLocallyUniformly :
    MultipliableLocallyUniformly f ↔ HasProdLocallyUniformly f (∏' i, f i ·) :=
  ⟨MultipliableLocallyUniformly.hasProdLocallyUniformly,
    HasProdLocallyUniformly.multipliableLocallyUniformly⟩

@[to_additive]
/--
lemma `HasProdLocallyUniformly.tendstoLocallyUniformly_finsetRange` / 引理 `HasProdLocallyUniformly.tendstoLocallyUniformly_finsetRange`

English:
lemma HasProdLocallyUniformly.tendstoLocallyUniformly_finsetRange
  proof: by
  simpa only [tendstoLocallyUniformlyOn_univ] using
    (h.hasProdLocallyUniformlyOn (s := .univ)).tendstoLocallyUniformlyOn_finsetRange

中文:
引理 HasProdLocallyUniformly.tendstoLocallyUniformly_finsetRange
  证明: by
  simpa only [tendstoLocallyUniformlyOn_univ] using
    (h.hasProdLocallyUniformlyOn (s := .univ)).tendstoLocallyUniformlyOn_finsetRange

Depends on / 依赖: h.hasProdLocallyUniformlyOn, hasProdLocallyUniformlyOn, tendstoLocallyUniformlyOn_finsetRange, tendstoLocallyUniformlyOn_univ
-/
lemma HasProdLocallyUniformly.tendstoLocallyUniformly_finsetRange
    {f : Nat -> β -> α} (h : HasProdLocallyUniformly f g) :
    TendstoLocallyUniformly (∏ i in Finset.range ·, f i ·) g atTop := by
  simpa only [tendstoLocallyUniformlyOn_univ] using
    (h.hasProdLocallyUniformlyOn (s := .univ)).tendstoLocallyUniformlyOn_finsetRange

end LocallyUniformly
