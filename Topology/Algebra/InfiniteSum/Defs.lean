/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Algebra.BigOperators.Group.Finset.Preimage

/-!
# Infinite sum and product in a topological monoid

This file defines infinite products and sums for (possibly infinite) indexed families of elements
in a commutative topological monoid (resp. add monoid).

To handle convergence questions we use the formalism of *summation filters* (defined in the
file `Mathlib/Topology/Algebra/InfiniteSum/SummationFilter.lean`). These are filters on the finite
subsets of a given type, and we define a function to be *summable* for a summation filter `L` if
its partial sums over finite subsets tend to a limit along `L` (and similarly for products).

This simultaneously generalizes several different kinds of summation: for instance,
*unconditional summation* (which makes sense for any index type) where we take the limit with
respect to the `atTop` filter; but also *conditional summation* for functions on `ℕ`, where the
limit is over the partial sums `∑ i ∈ range n, f i` as `n → ∞` (so there exist
conditionally-summable sequences which are not unconditionally summable).

## Implementation notes

We say that a function `f : β → α` has a product of `a` w.r.t. the summation filter `L` if the
function `fun s : Finset β ↦ ∏ b ∈ s, f b` converges to `a` w.r.t. the filter `L.filter` on
`Finset β`.

In the most important case of unconditional summation, this translates to the following condition:
for every neighborhood `U` of `a`, there exists a finite set `s : Finset β` of indices such
that `∏ b ∈ s', f b ∈ U` for any finite set `s'` which is a superset of `s`.

This may yield some unexpected results. For example, according to this definition, the product
`∏' n : ℕ, (1 : ℝ) / 2` unconditionally exists and is equal to `0`. More strikingly,
the product `∏' n : ℕ, (n : ℝ)` unconditionally exists and is equal to `0`, because one
of its terms is `0` (even though the product of the remaining terms diverges). Users who would
prefer that these products be considered not to exist can carry them out in the unit group `ℝˣ`
rather than in `ℝ`.

## References

* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/

@[expose] public section

/- **NOTE**. This file is intended to be kept short, just enough to state the basic definitions and
six key lemmas relating them together, namely `Summable.hasSum`, `Multipliable.hasProd`,
`HasSum.tsum_eq`, `HasProd.tprod_eq`, `Summable.hasSum_iff`, and `Multipliable.hasProd_iff`.

Do not add further lemmas here -- add them to `InfiniteSum.Basic` or (preferably) another, more
specific file. -/

noncomputable section

open Filter Function SummationFilter

open scoped Topology

variable {α β γ : Type*}

section HasProd

variable [CommMonoid α] [TopologicalSpace α]

/-- `HasProd f a L` means that the (potentially infinite) product of the `f b` for `b : β` converges
to `a` along the SummationFilter `L`.

By default `L` is the `unconditional` one, corresponding to the limit of all finite sets towards
the entire type. So we take the product over bigger and bigger finite sets. This product operation
is invariant under permuting the terms (while products for more general summation filters usually
are not).

For the definition and many statements, `α` does not need to be a topological monoid, only a monoid
with a topology (i.e. the multiplication is not assumed to be continuous). We only add this
assumption later, for the lemmas where it is relevant.

These are defined in an identical way to infinite sums (`HasSum`). For example, we say that
the function `ℕ → ℝ` sending `n` to `1 / 2` has a product of `0`, rather than saying that it does
not converge as some authors would. -/
@[to_additive /-- `HasSum f a L` means that the (potentially infinite) sum of the `f b` for `b : β`
converges to `a` along the SummationFilter `L`.

By default `L` is the `unconditional` one, corresponding to the limit of all finite sets towards
the entire type. So we take the sum over bigger and bigger finite sets. This sum operation is
invariant under permuting the terms (while sums for more general summation filters usually are not).
This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).

In particular, the function `ℕ → ℝ` sending `n` to `(-1) ^ n / (n + 1)` does not have a
sum for this definition, although it is summable for the `conditional` summation filter that
takes limits of sums over `n ∈ {0, ..., X}` as `X → ∞`. However, a series which is *absolutely*
convergent with respect to the conditional summation filter is in fact unconditionally summable.

For the definition and many statements, `α` does not need to be a topological additive monoid,
only an additive monoid with a topology (i.e. the addition is not assumed to be continuous). We
only add this assumption later, for the lemmas where it is relevant. -/]
/--
Definition of `HasProd` / `HasProd` 的定义

English:
definition HasProd
  signature: (f : β -> α) (a : α) (L := unconditional β)
  body: Tendsto (fun s : Finset β => ∏ b in s, f b) L.filter (𝓝 a)

中文:
定义 有积类型
  签名: (f : β -> α) (a : α) (L := unconditional β)
  定义体: Tendsto (fun s : Finset β => ∏ b in s, f b) L.filter (𝓝 a)

Depends on / 依赖: unconditional
-/
def HasProd (f : β -> α) (a : α) (L := unconditional β) : Prop :=
  Tendsto (fun s : Finset β => ∏ b in s, f b) L.filter (𝓝 a)

/-- `Multipliable f` means that `f` has some (infinite) product with respect to `L`. Use `tprod` to
get the value. -/
@[to_additive
/-- `Summable f` means that `f` has some (infinite) sum with respect to `L`. Use `tsum` to get the
value. -/]
/--
Definition of `Multipliable` / `Multipliable` 的定义

English:
definition Multipliable
  signature: (f : β -> α) (L := unconditional β)
  body: exists a, HasProd f a L

@[to_additive]

中文:
定义 Multipliable
  签名: (f : β -> α) (L := unconditional β)
  定义体: exists a, HasProd f a L

@[to_additive]

Depends on / 依赖: unconditional
-/
def Multipliable (f : β -> α) (L := unconditional β) : Prop :=
  exists a, HasProd f a L

@[to_additive]
/--
lemma `Multipliable.mono_filter` / 引理 `Multipliable.mono_filter`

English:
lemma Multipliable.mono_filter
  statement: {f : β -> α} {L₁ L₂ : SummationFilter β}
  proof: match hf with | ⟨a, ha⟩ => ⟨a, ha.mono_left h⟩

中文:
引理 Multipliable.mono_filter
  结论: {f : β -> α} {L₁ L₂ : SummationFilter β}
  证明: match hf with | ⟨a, ha⟩ => ⟨a, ha.mono_left h⟩

Depends on / 依赖: ha.mono_left, mono_left
-/
lemma Multipliable.mono_filter {f : β -> α} {L₁ L₂ : SummationFilter β}
    (hf : Multipliable f L₂) (h : L₁.filter <= L₂.filter) : Multipliable f L₁ :=
  match hf with | ⟨a, ha⟩ => ⟨a, ha.mono_left h⟩

open scoped Classical in
/-- `∏' i, f i` is the unconditional product of `f`, if it exists, or 1 otherwise.

More generally, if `L` is a `SummationFilter`, `∏'[L] i, f i` is the product of `f` with respect to
`L` if it exists, and `1` otherwise.

(Note that even if the unconditional product exists, it might not be unique if the topology is not
separated. When the multiplicative support of `f` is finite, we make the most reasonable choice,
to use the product over the multiplicative support. Otherwise, we choose arbitrarily an `a`
satisfying `HasProd f a`. Similar remarks apply to more general summation filters.) -/
@[to_additive /-- `∑' i, f i` is the unconditional sum of `f` if it exists, or 0 otherwise.

More generally, if `L` is a `SummationFilter`, `∑'[L] i, f i` is the sum of `f` with respect to
`L` if it exists, and `0` otherwise.

(Note that even if the unconditional sum exists, it might not be unique if the topology is not
separated. When the support of `f` is finite, we make the most reasonable choice, to use the sum
over the support. Otherwise, we choose arbitrarily an `a` satisfying `HasSum f a`. Similar remarks
apply to more general summation filters.)
-/]
noncomputable irreducible_def tprod (f : β -> α) (L := unconditional β) :=
  if h : Multipliable f L then
    if L.HasSupport ∧ (mulSupport f inter L.support).Finite then finprod (L.support.mulIndicator f)
    else if HasProd f 1 L then 1
    else h.choose
  else 1

variable {L : SummationFilter β}

@[inherit_doc tprod]
notation3 "∏'[" L "]" (...)", "r:67:(scoped f => tprod f L) => r
@[inherit_doc tsum]
notation3 "∑'[" L "]" (...)", "r:67:(scoped f => tsum f L) => r

-- see note [operator precedence of big operators]
@[inherit_doc tprod]
notation3 "∏' "(...)", "r:67:(scoped f => tprod f (unconditional _)) => r
@[inherit_doc tsum]
notation3 "∑' "(...)", "r:67:(scoped f => tsum f (unconditional _)) => r

@[to_additive]
/--
lemma `hasProd_bot` / 引理 `hasProd_bot`

English:
lemma hasProd_bot
  given: (hL : ¬L.NeBot) (f : β -> α) (a : α)
  proof: by
  have : L.filter = ⊥ := by contrapose! hL; exact ⟨hL⟩
  rw [HasProd]; rw [this]
  exact tendsto_bot

@[to_additive]

中文:
引理 hasProd_bot
  条件: (hL : ¬L.NeBot) (f : β -> α) (a : α)
  证明: by
  have : L.filter = ⊥ := by contrapose! hL; exact ⟨hL⟩
  rw [HasProd]; rw [this]
  exact tendsto_bot

@[to_additive]

Depends on / 依赖: HasProd, L.filter, contrapose, filter, tendsto_bot
-/
lemma hasProd_bot (hL : ¬L.NeBot) (f : β -> α) (a : α) :
    HasProd f a L := by
  have : L.filter = ⊥ := by contrapose! hL; exact ⟨hL⟩
  rw [HasProd]; rw [this]
  exact tendsto_bot

@[to_additive]
/--
lemma `multipliable_bot` / 引理 `multipliable_bot`

English:
lemma multipliable_bot
  given: (hL : ¬L.NeBot) (f : β -> α)
  proof: ⟨1, hasProd_bot hL ..⟩

中文:
引理 multipliable_bot
  条件: (hL : ¬L.NeBot) (f : β -> α)
  证明: ⟨1, hasProd_bot hL ..⟩

Depends on / 依赖: hasProd_bot
-/
lemma multipliable_bot (hL : ¬L.NeBot) (f : β -> α) :
    Multipliable f L :=
  ⟨1, hasProd_bot hL ..⟩

/-- If the summation filter is the trivial filter `⊥`, then the topological product is equal to the
finite product (which is taken to be 1 if the multiplicative support of `f` is infinite).

Note that in this case `HasProd f a` is satisfied for *every* element `a` of the target, so the
value assigned to the `tprod` is a question of conventions. -/
@[to_additive /-- If the summation filter is the trivial filter `⊥`, then the topological sum is
equal to the finite sum (which is taken to be 1 if the support of `f` is infinite).

Note that in this case `HasSum f a` is satisfied for *every* element `a` of the target, so the
value assigned to the `tsum` is a question of conventions. -/]
/--
lemma `tprod_bot` / 引理 `tprod_bot`

English:
lemma tprod_bot
  given: (hL : ¬L.NeBot) (f : β -> α)
  statement: ∏'[L] b, f b = ∏ᶠ b, f b
  proof: by
  simp only [tprod_def, dif_pos (multipliable_bot hL f)]
  have : L.LeAtTop := L.leAtTop_of_not_NeBot hL
  rw [L.support_eq_univ]; rw [Set.inter_univ]; rw [Set.mulIndicator_univ]
  by_cases hf : (mulSupport f).Finite
  · rw [eq_true_intro hf, if_pos]
    simp only [and_true]
    infer_instance
  

中文:
引理 tprod_bot
  条件: (hL : ¬L.NeBot) (f : β -> α)
  结论: ∏'[L] b, f b = ∏ᶠ b, f b
  证明: by
  simp only [tprod_def, dif_pos (multipliable_bot hL f)]
  have : L.LeAtTop := L.leAtTop_of_not_NeBot hL
  rw [L.support_eq_univ]; rw [Set.inter_univ]; rw [Set.mulIndicator_univ]
  by_cases hf : (mulSupport f).Finite
  · rw [eq_true_intro hf, if_pos]
    simp only [and_true]
    infer_instance
  

Depends on / 依赖: Finite, L.LeAtTop, L.leAtTop_of_not_NeBot, L.support_eq_univ, LeAtTop, Set.inter_univ, Set.mulIndicator_univ, and_true, dif_pos, eq_true_intro, finprod_of_infinite_mulSupport, hasProd_bot, if_neg, if_pos, infer_instance, inter_univ, leAtTop_of_not_NeBot, mulIndicator_univ, mulSupport, multipliable_bot
-/
lemma tprod_bot (hL : ¬L.NeBot) (f : β -> α) : ∏'[L] b, f b = ∏ᶠ b, f b := by
  simp only [tprod_def, dif_pos (multipliable_bot hL f)]
  have : L.LeAtTop := L.leAtTop_of_not_NeBot hL
  rw [L.support_eq_univ]; rw [Set.inter_univ]; rw [Set.mulIndicator_univ]
  by_cases hf : (mulSupport f).Finite
  · rw [eq_true_intro hf, if_pos]
    simp only [and_true]
    infer_instance
  · rwa [if_neg (by tauto), if_pos (hasProd_bot hL _ _), finprod_of_infinite_mulSupport]

variable {f : β -> α} {a : α} {s : Finset β}

@[to_additive]
/--
theorem `HasProd.multipliable` / 定理 `HasProd.multipliable`

English:
theorem HasProd.multipliable
  given: (h : HasProd f a L)
  statement: Multipliable f L
  proof: ⟨a, h⟩

@[to_additive]

中文:
定理 有积类型.multipliable
  条件: (h : 有积类型 f a L)
  结论: Multipliable f L
  证明: ⟨a, h⟩

@[to_additive]
-/
theorem HasProd.multipliable (h : HasProd f a L) : Multipliable f L :=
  ⟨a, h⟩

@[to_additive]
/--
theorem `tprod_eq_one_of_not_multipliable` / 定理 `tprod_eq_one_of_not_multipliable`

English:
theorem tprod_eq_one_of_not_multipliable
  given: (h : ¬Multipliable f L)
  statement: ∏'[L] b, f b = 1
  proof: by
  simp [tprod_def, h]

@[to_additive]

中文:
定理 tprod_eq_one_of_not_multipliable
  条件: (h : ¬Multipliable f L)
  结论: ∏'[L] b, f b = 1
  证明: by
  simp [tprod_def, h]

@[to_additive]

Depends on / 依赖: tprod_def
-/
theorem tprod_eq_one_of_not_multipliable (h : ¬Multipliable f L) : ∏'[L] b, f b = 1 := by
  simp [tprod_def, h]

@[to_additive]
/--
theorem `Function.Injective.hasProd_map_iff` / 定理 `Function.Injective.hasProd_map_iff`

English:
theorem Function.Injective.hasProd_map_iff
  given: {L : SummationFilter γ} {g : γ -> β} (hg : Injective g)
  proof: by
  simp [HasProd, Function.comp_def]

@[to_additive]

中文:
定理 函数.单射.hasProd_map_iff
  条件: {L : SummationFilter γ} {g : γ -> β} (hg : 单射 g)
  证明: by
  simp [HasProd, Function.comp_def]

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, HasProd, comp_def
-/
theorem Function.Injective.hasProd_map_iff {L : SummationFilter γ} {g : γ -> β} (hg : Injective g) :
    HasProd f a (L.map ⟨g, hg⟩) ↔ HasProd (f ∘ g) a L := by
  simp [HasProd, Function.comp_def]

@[to_additive]
/--
theorem `Function.Injective.hasProd_comap_iff_of_hasSupport` / 定理 `Function.Injective.hasProd_comap_iff_of_hasSupport`

English:
theorem Function.Injective.hasProd_comap_iff_of_hasSupport
  statement: [L.HasSupport] {g : γ -> β}
  proof: by
  simp only [HasProd, SummationFilter.comap_filter, tendsto_map'_iff, comp_apply,
    Embedding.coeFn_mk, Function.comp_def]
  refine tendsto_congr' ?_
  filter_upwards [L.eventually_le_support] with s hs
  rw [s.prod_preimage]
  exact fun x h h' => hf x (hs h) h'

@[to_additive]

中文:
定理 函数.单射.hasProd_comap_iff_of_hasSupport
  结论: [L.有Support] {g : γ -> β}
  证明: by
  simp only [HasProd, SummationFilter.comap_filter, tendsto_map'_iff, comp_apply,
    Embedding.coeFn_mk, Function.comp_def]
  refine tendsto_congr' ?_
  filter_upwards [L.eventually_le_support] with s hs
  rw [s.prod_preimage]
  exact fun x h h' => hf x (hs h) h'

@[to_additive]

Depends on / 依赖: Embedding, Embedding.coeFn_mk, Function, Function.comp_def, HasProd, L.eventually_le_support, SummationFilter, SummationFilter.comap_filter, _iff, coeFn_mk, comap_filter, comp_apply, comp_def, eventually_le_support, filter_upwards, prod_preimage, s.prod_preimage, tendsto_congr, tendsto_map
-/
theorem Function.Injective.hasProd_comap_iff_of_hasSupport [L.HasSupport] {g : γ -> β}
    (hg : Injective g) (hf : forall x in L.support, x ∉ Set.range g -> f x = 1) :
    HasProd (f ∘ g) a (L.comap ⟨g, hg⟩) ↔ HasProd f a L := by
  simp only [HasProd, SummationFilter.comap_filter, tendsto_map'_iff, comp_apply,
    Embedding.coeFn_mk, Function.comp_def]
  refine tendsto_congr' ?_
  filter_upwards [L.eventually_le_support] with s hs
  rw [s.prod_preimage]
  exact fun x h h' => hf x (hs h) h'

@[to_additive]
/--
theorem `Function.Injective.hasProd_comap_iff` / 定理 `Function.Injective.hasProd_comap_iff`

English:
theorem Function.Injective.hasProd_comap_iff
  statement: {g : γ -> β} (hg : Injective g)
  proof: by
  simp only [HasProd, SummationFilter.comap_filter, tendsto_map'_iff, comp_apply,
    Embedding.coeFn_mk, Function.comp_def]
  refine tendsto_congr fun s => ?_
  rw [s.prod_preimage]
  exact fun x _ h => hf x h

@[to_additive]

中文:
定理 函数.单射.hasProd_comap_iff
  结论: {g : γ -> β} (hg : 单射 g)
  证明: by
  simp only [HasProd, SummationFilter.comap_filter, tendsto_map'_iff, comp_apply,
    Embedding.coeFn_mk, Function.comp_def]
  refine tendsto_congr fun s => ?_
  rw [s.prod_preimage]
  exact fun x _ h => hf x h

@[to_additive]

Depends on / 依赖: Embedding, Embedding.coeFn_mk, Function, Function.comp_def, HasProd, SummationFilter, SummationFilter.comap_filter, _iff, coeFn_mk, comap_filter, comp_apply, comp_def, prod_preimage, s.prod_preimage, tendsto_congr, tendsto_map
-/
theorem Function.Injective.hasProd_comap_iff {g : γ -> β} (hg : Injective g)
    (hf : forall x, x ∉ Set.range g -> f x = 1) :
    HasProd (f ∘ g) a (L.comap ⟨g, hg⟩) ↔ HasProd f a L := by
  simp only [HasProd, SummationFilter.comap_filter, tendsto_map'_iff, comp_apply,
    Embedding.coeFn_mk, Function.comp_def]
  refine tendsto_congr fun s => ?_
  rw [s.prod_preimage]
  exact fun x _ h => hf x h

@[to_additive]
/--
theorem `Function.Injective.hasProd_iff` / 定理 `Function.Injective.hasProd_iff`

English:
theorem Function.Injective.hasProd_iff
  statement: {g : γ -> β} (hg : Injective g)
  proof: by
  rw [← hg.hasProd_comap_iff hf]; rw [SummationFilter.comap_unconditional]

@[to_additive]

中文:
定理 函数.单射.hasProd_iff
  结论: {g : γ -> β} (hg : 单射 g)
  证明: by
  rw [← hg.hasProd_comap_iff hf]; rw [SummationFilter.comap_unconditional]

@[to_additive]

Depends on / 依赖: SummationFilter, SummationFilter.comap_unconditional, comap_unconditional, hasProd_comap_iff, hg.hasProd_comap_iff
-/
theorem Function.Injective.hasProd_iff {g : γ -> β} (hg : Injective g)
    (hf : forall x, x ∉ Set.range g -> f x = 1) :
    HasProd (f ∘ g) a ↔ HasProd f a := by
  rw [← hg.hasProd_comap_iff hf]; rw [SummationFilter.comap_unconditional]

@[to_additive]
/--
theorem `hasProd_subtype_comap_iff_of_mulSupport_subset` / 定理 `hasProd_subtype_comap_iff_of_mulSupport_subset`

English:
theorem hasProd_subtype_comap_iff_of_mulSupport_subset
  given: {s : Set β} (hf : mulSupport f subseteq s)
  proof: Subtype.coe_injective.hasProd_comap_iff by simpa using mulSupport_subset_iff'.1 hf

@[to_additive]

中文:
定理 hasProd_subtype_comap_iff_of_mulSupport_subset
  条件: {s : 集合 β} (hf : mulSupport f subseteq s)
  证明: Subtype.coe_injective.hasProd_comap_iff by simpa using mulSupport_subset_iff'.1 hf

@[to_additive]

Depends on / 依赖: Subtype, Subtype.coe_injective.hasProd_comap_iff, coe_injective, hasProd_comap_iff, mulSupport_subset_iff
-/
theorem hasProd_subtype_comap_iff_of_mulSupport_subset {s : Set β} (hf : mulSupport f subseteq s) :
    HasProd (f ∘ (↑) : s -> α) a (L.comap <| Embedding.subtype _) ↔ HasProd f a L :=
Subtype.coe_injective.hasProd_comap_iff by simpa using mulSupport_subset_iff'.1 hf

@[to_additive]
/--
theorem `hasProd_subtype_iff_of_mulSupport_subset` / 定理 `hasProd_subtype_iff_of_mulSupport_subset`

English:
theorem hasProd_subtype_iff_of_mulSupport_subset
  given: {s : Set β} (hf : mulSupport f subseteq s)
  proof: by
  simpa using hasProd_subtype_comap_iff_of_mulSupport_subset hf (L := unconditional _)

@[to_additive]

中文:
定理 hasProd_subtype_iff_of_mulSupport_subset
  条件: {s : 集合 β} (hf : mulSupport f subseteq s)
  证明: by
  simpa using hasProd_subtype_comap_iff_of_mulSupport_subset hf (L := unconditional _)

@[to_additive]

Depends on / 依赖: hasProd_subtype_comap_iff_of_mulSupport_subset, unconditional
-/
theorem hasProd_subtype_iff_of_mulSupport_subset {s : Set β} (hf : mulSupport f subseteq s) :
    HasProd (f ∘ (↑) : s -> α) a ↔ HasProd f a := by
  simpa using hasProd_subtype_comap_iff_of_mulSupport_subset hf (L := unconditional _)

@[to_additive]
/--
theorem `hasProd_fintype_support` / 定理 `hasProd_fintype_support`

English:
theorem hasProd_fintype_support
  statement: [Fintype β] (f : β -> α) (L : SummationFilter β) [L.HasSupport]
  proof: by
  apply tendsto_nhds_of_eventually_eq
  have h1 : ⋂ b in L.support, {s | b in s} in L.filter :=
    (L.filter.biInter_mem L.support.toFinite).mpr (by tauto)
  have h2 : ⋂ b in L.supportᶜ, {s | b ∉ s} in L.filter :=
    (L.filter.biInter_mem L.supportᶜ.toFinite).mpr
      (fun b hb => (L.eventuall

中文:
定理 hasProd_fintype_support
  结论: [有限类型 β] (f : β -> α) (L : SummationFilter β) [L.有Support]
  证明: by
  apply tendsto_nhds_of_eventually_eq
  have h1 : ⋂ b in L.support, {s | b in s} in L.filter :=
    (L.filter.biInter_mem L.support.toFinite).mpr (by tauto)
  have h2 : ⋂ b in L.supportᶜ, {s | b ∉ s} in L.filter :=
    (L.filter.biInter_mem L.supportᶜ.toFinite).mpr
      (fun b hb => (L.eventuall

Depends on / 依赖: L.eventually_mem_or_not_mem, L.filter, L.filter.biInter_mem, L.support, L.support.toFinite, Set.mem_compl_iff, Set.mem_iInter, Set.mem_ofPred_eq, biInter_mem, eventually_mem_or_not_mem, filter, filter_upwards, mem_compl_iff, mem_iInter, mem_ofPred_eq, resolve_left, support, tendsto_nhds_of_eventually_eq, toFinite
-/
theorem hasProd_fintype_support [Fintype β] (f : β -> α) (L : SummationFilter β) [L.HasSupport]
    [DecidablePred (· in L.support)] : HasProd f (∏ b in L.support, f b) L := by
  apply tendsto_nhds_of_eventually_eq
  have h1 : ⋂ b in L.support, {s | b in s} in L.filter :=
    (L.filter.biInter_mem L.support.toFinite).mpr (by tauto)
  have h2 : ⋂ b in L.supportᶜ, {s | b ∉ s} in L.filter :=
    (L.filter.biInter_mem L.supportᶜ.toFinite).mpr
      (fun b hb => (L.eventually_mem_or_not_mem b).resolve_left hb)
  filter_upwards [h1, h2] with s hs hs'
  congr 1
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_compl_iff] at hs hs'
  grind

@[to_additive]
/--
theorem `hasProd_fintype` / 定理 `hasProd_fintype`

English:
theorem hasProd_fintype
  given: [Fintype β] (f : β -> α) (L := unconditional β) [L.LeAtTop]
  proof: by
  simpa using hasProd_fintype_support f L

@[to_additive]

中文:
定理 hasProd_fintype
  条件: [有限类型 β] (f : β -> α) (L := unconditional β) [L.LeAtTop]
  证明: by
  simpa using hasProd_fintype_support f L

@[to_additive]

Depends on / 依赖: L.LeAtTop, LeAtTop, unconditional
-/
theorem hasProd_fintype [Fintype β] (f : β -> α) (L := unconditional β) [L.LeAtTop] :
    HasProd f (∏ b, f b) L := by
  simpa using hasProd_fintype_support f L

@[to_additive]
/--
theorem `Finset.hasProd_support` / 定理 `Finset.hasProd_support`

English:
theorem Finset.hasProd_support
  statement: (s : Finset β) (f : β -> α) (L := unconditional (s : Set β))
  proof: by
  simpa [prod_attach] using hasProd_fintype_support (f ∘ Subtype.val) L

中文:
定理 有限集.hasProd_support
  结论: (s : 有限集 β) (f : β -> α) (L := unconditional (s : 集合 β))
  证明: by
  simpa [prod_attach] using hasProd_fintype_support (f ∘ Subtype.val) L

Depends on / 依赖: unconditional
-/
theorem Finset.hasProd_support (s : Finset β) (f : β -> α) (L := unconditional (s : Set β))
    [L.HasSupport] [DecidablePred (· in L.support)] :
    HasProd (f ∘ (↑) : (↑s : Set β) -> α)
      (∏ b in (L.support.toFinset.map <| Embedding.subtype _), f b) L := by
  simpa [prod_attach] using hasProd_fintype_support (f ∘ Subtype.val) L

set_option backward.isDefEq.respectTransparency false in
-- note this is not deduced from `Finset.hasProd_support` to avoid needing `[DecidableEq β]`
@[to_additive]
/--
theorem `Finset.hasProd` / 定理 `Finset.hasProd`

English:
theorem Finset.hasProd
  statement: (s : Finset β) (f : β -> α)
  proof: by
  simpa [prod_attach, Embedding.subtype] using Finset.hasProd_support s f L

中文:
定理 有限集.hasProd
  结论: (s : 有限集 β) (f : β -> α)
  证明: by
  simpa [prod_attach, Embedding.subtype] using Finset.hasProd_support s f L
-/
protected theorem Finset.hasProd (s : Finset β) (f : β -> α)
    (L := unconditional (s : Set β)) [L.LeAtTop] :
    HasProd (f ∘ (↑) : (↑s : Set β) -> α) (∏ b in s, f b) L := by
  simpa [prod_attach, Embedding.subtype] using Finset.hasProd_support s f L

/-- If a function `f` is `1` outside of a finite set `s`, then it `HasProd` `∏ b ∈ s, f b`. -/
@[to_additive /-- If a function `f` vanishes outside of a finite set `s`, then it `HasSum`
`∑ b ∈ s, f b`. -/]
/--
theorem `hasProd_prod_support_of_ne_finset_one` / 定理 `hasProd_prod_support_of_ne_finset_one`

English:
theorem hasProd_prod_support_of_ne_finset_one
  statement: (hf : forall b in L.support, b ∉ s -> f b = 1)
  proof: by
  apply tendsto_nhds_of_eventually_eq
  have h1 : ⋂ b in (↑s inter L.support), {s | b in s} in L.filter :=
    (L.filter.biInter_mem (Set.toFinite _)).mpr (fun b hb => hb.2)
  filter_upwards [h1, L.eventually_le_support] with t ht ht'
  simp only [Set.mem_iInter] at ht
  apply Finset.prod_congr_o

中文:
定理 hasProd_prod_support_of_ne_finset_one
  结论: (hf : 对任意 b in L.support, b ∉ s -> f b = 1)
  证明: by
  apply tendsto_nhds_of_eventually_eq
  have h1 : ⋂ b in (↑s inter L.support), {s | b in s} in L.filter :=
    (L.filter.biInter_mem (Set.toFinite _)).mpr (fun b hb => hb.2)
  filter_upwards [h1, L.eventually_le_support] with t ht ht'
  simp only [Set.mem_iInter] at ht
  apply Finset.prod_congr_o

Depends on / 依赖: Finset, Finset.prod_congr_of_eq_on_inter, L.eventually_le_support, L.filter, L.filter.biInter_mem, L.support, Set.mem_iInter, Set.toFinite, biInter_mem, eventually_le_support, filter, filter_upwards, mem_iInter, prod_congr_of_eq_on_inter, support, tendsto_nhds_of_eventually_eq, toFinite
-/
theorem hasProd_prod_support_of_ne_finset_one (hf : forall b in L.support, b ∉ s -> f b = 1)
    [L.HasSupport] [DecidablePred (· in L.support)] :
    HasProd f (∏ b in (↑s inter L.support).toFinset, f b) L := by
  apply tendsto_nhds_of_eventually_eq
  have h1 : ⋂ b in (↑s inter L.support), {s | b in s} in L.filter :=
    (L.filter.biInter_mem (Set.toFinite _)).mpr (fun b hb => hb.2)
  filter_upwards [h1, L.eventually_le_support] with t ht ht'
  simp only [Set.mem_iInter] at ht
  apply Finset.prod_congr_of_eq_on_inter <;> grind

/-- If a function `f` is `1` outside of a finite set `s`, then it `HasProd` `∏ b ∈ s, f b`. -/
@[to_additive /-- If a function `f` vanishes outside of a finite set `s`, then it `HasSum`
`∑ b ∈ s, f b`. -/]
/--
theorem `hasProd_prod_of_ne_finset_one` / 定理 `hasProd_prod_of_ne_finset_one`

English:
theorem hasProd_prod_of_ne_finset_one
  given: (hf : forall b ∉ s, f b = 1) [L.LeAtTop]
  proof: ((hasProd_subtype_iff_of_mulSupport_subset <| mulSupport_subset_iff'.2 hf).1 <| s.hasProd f)
.mono_left L.le_atTop

@[to_additive]

中文:
定理 hasProd_prod_of_ne_finset_one
  条件: (hf : 对任意 b ∉ s, f b = 1) [L.LeAtTop]
  证明: ((hasProd_subtype_iff_of_mulSupport_subset <| mulSupport_subset_iff'.2 hf).1 <| s.hasProd f)
.mono_left L.le_atTop

@[to_additive]

Depends on / 依赖: L.le_atTop, hasProd, hasProd_subtype_iff_of_mulSupport_subset, le_atTop, mono_left, mulSupport_subset_iff, s.hasProd
-/
theorem hasProd_prod_of_ne_finset_one (hf : forall b ∉ s, f b = 1) [L.LeAtTop] :
    HasProd f (∏ b in s, f b) L :=
  ((hasProd_subtype_iff_of_mulSupport_subset <| mulSupport_subset_iff'.2 hf).1 <| s.hasProd f)
.mono_left L.le_atTop

@[to_additive]
/--
theorem `multipliable_of_ne_finset_one` / 定理 `multipliable_of_ne_finset_one`

English:
theorem multipliable_of_ne_finset_one
  given: (hf : forall b ∉ s, f b = 1) [L.HasSupport]
  proof: by
  classical
  exact (hasProd_prod_support_of_ne_finset_one (fun b _ hb => hf b hb)).multipliable

@[to_additive]

中文:
定理 multipliable_of_ne_finset_one
  条件: (hf : 对任意 b ∉ s, f b = 1) [L.有Support]
  证明: by
  classical
  exact (hasProd_prod_support_of_ne_finset_one (fun b _ hb => hf b hb)).multipliable

@[to_additive]

Depends on / 依赖: classical, hasProd_prod_support_of_ne_finset_one, multipliable
-/
theorem multipliable_of_ne_finset_one (hf : forall b ∉ s, f b = 1) [L.HasSupport] :
    Multipliable f L := by
  classical
  exact (hasProd_prod_support_of_ne_finset_one (fun b _ hb => hf b hb)).multipliable

@[to_additive]
/--
theorem `Multipliable.hasProd` / 定理 `Multipliable.hasProd`

English:
theorem Multipliable.hasProd
  given: (ha : Multipliable f L)
  statement: HasProd f (∏'[L] b, f b) L
  proof: by
  -- This is quite delicate because of the fiddly special-casing for finite products.
  classical
  rw [tprod_def]; rw [dif_pos ha]
  split_ifs with h h'
  · convert! hasProd_prod_support_of_ne_finset_one (s := h.2.toFinset) (L := L) _ using 2
    · simp only [Set.inter_eq_left.mpr (show ↑h.2.toF

中文:
定理 Multipliable.hasProd
  条件: (ha : Multipliable f L)
  结论: 有积类型 f (∏'[L] b, f b) L
  证明: by
  -- This is quite delicate because of the fiddly special-casing for finite products.
  classical
  rw [tprod_def]; rw [dif_pos ha]
  split_ifs with h h'
  · convert! hasProd_prod_support_of_ne_finset_one (s := h.2.toFinset) (L := L) _ using 2
    · simp only [Set.inter_eq_left.mpr (show ↑h.2.toF
-/
theorem Multipliable.hasProd (ha : Multipliable f L) : HasProd f (∏'[L] b, f b) L := by
  -- This is quite delicate because of the fiddly special-casing for finite products.
  classical
  rw [tprod_def]; rw [dif_pos ha]
  split_ifs with h h'
  · convert! hasProd_prod_support_of_ne_finset_one (s := h.2.toFinset) (L := L) _ using 2
    · simp only [Set.inter_eq_left.mpr (show ↑h.2.toFinset subseteq L.support by simp)]
      simp only [Set.Finite.coe_toFinset, Finset.toFinset_coe]
      rw [finprod_eq_prod_of_mulSupport_subset (s := h.2.toFinset)]
      · exact Finset.prod_congr rfl (by simp_all)
      · simp
    · grind [Set.Finite.mem_toFinset, mem_mulSupport]
    · exact h.1
  · exact h'
  · exact ha.choose_spec

variable [T2Space α] [L.NeBot]

@[to_additive]
/--
theorem `HasProd.unique` / 定理 `HasProd.unique`

English:
theorem HasProd.unique
  given: {a₁ a₂ : α}
  proof: by
  exact tendsto_nhds_unique

@[to_additive]

中文:
定理 有积类型.unique
  条件: {a₁ a₂ : α}
  证明: by
  exact tendsto_nhds_unique

@[to_additive]

Depends on / 依赖: tendsto_nhds_unique
-/
theorem HasProd.unique {a₁ a₂ : α} :
    HasProd f a₁ L -> HasProd f a₂ L -> a₁ = a₂ := by
  exact tendsto_nhds_unique

@[to_additive]
/--
theorem `HasProd.tprod_eq` / 定理 `HasProd.tprod_eq`

English:
theorem HasProd.tprod_eq
  given: (ha : HasProd f a L)
  statement: ∏'[L] b, f b = a
  proof: (Multipliable.hasProd ⟨a, ha⟩).unique ha

@[to_additive]

中文:
定理 有积类型.tprod_eq
  条件: (ha : 有积类型 f a L)
  结论: ∏'[L] b, f b = a
  证明: (Multipliable.hasProd ⟨a, ha⟩).unique ha

@[to_additive]

Depends on / 依赖: Multipliable, Multipliable.hasProd, hasProd, unique
-/
theorem HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b = a :=
  (Multipliable.hasProd ⟨a, ha⟩).unique ha

@[to_additive]
/--
theorem `Multipliable.hasProd_iff` / 定理 `Multipliable.hasProd_iff`

English:
theorem Multipliable.hasProd_iff
  given: (h : Multipliable f L)
  proof: Iff.intro HasProd.tprod_eq fun eq => eq ▸ h.hasProd

@[to_additive]

中文:
定理 Multipliable.hasProd_iff
  条件: (h : Multipliable f L)
  证明: Iff.intro HasProd.tprod_eq fun eq => eq ▸ h.hasProd

@[to_additive]

Depends on / 依赖: HasProd, HasProd.tprod_eq, Iff.intro, h.hasProd, hasProd, tprod_eq
-/
theorem Multipliable.hasProd_iff (h : Multipliable f L) :
    HasProd f a L ↔ ∏'[L] b, f b = a :=
  Iff.intro HasProd.tprod_eq fun eq => eq ▸ h.hasProd

@[to_additive]
/--
theorem `tprod_eq_of_filter_le` / 定理 `tprod_eq_of_filter_le`

English:
theorem tprod_eq_of_filter_le
  statement: {L₁ L₂ : SummationFilter β} [L₁.NeBot]
  proof: (hf.mono_filter h).hasProd_iff.mp (hf.hasProd.mono_left h)

@[to_additive]

中文:
定理 tprod_eq_of_filter_le
  结论: {L₁ L₂ : SummationFilter β} [L₁.NeBot]
  证明: (hf.mono_filter h).hasProd_iff.mp (hf.hasProd.mono_left h)

@[to_additive]

Depends on / 依赖: hasProd, hasProd_iff, hasProd_iff.mp, hf.hasProd.mono_left, hf.mono_filter, mono_filter, mono_left
-/
theorem tprod_eq_of_filter_le {L₁ L₂ : SummationFilter β} [L₁.NeBot]
    (h : L₁.filter <= L₂.filter) (hf : Multipliable f L₂) : ∏'[L₁] b, f b = ∏'[L₂] b, f b :=
  (hf.mono_filter h).hasProd_iff.mp (hf.hasProd.mono_left h)

@[to_additive]
/--
theorem `tprod_eq_of_multipliable_unconditional` / 定理 `tprod_eq_of_multipliable_unconditional`

English:
theorem tprod_eq_of_multipliable_unconditional
  given: [L.LeAtTop] (hf : Multipliable f)
  proof: tprod_eq_of_filter_le L.le_atTop hf

中文:
定理 tprod_eq_of_multipliable_unconditional
  条件: [L.LeAtTop] (hf : Multipliable f)
  证明: tprod_eq_of_filter_le L.le_atTop hf

Depends on / 依赖: L.le_atTop, le_atTop, tprod_eq_of_filter_le
-/
theorem tprod_eq_of_multipliable_unconditional [L.LeAtTop] (hf : Multipliable f) :
     ∏'[L] b, f b = ∏' b, f b :=
  tprod_eq_of_filter_le L.le_atTop hf

end HasProd
