/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, David Loeffler
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Vertical line test for group homs

This file proves the vertical line test for monoid homomorphisms/isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some monoid homomorphism `f' : H → I`.

Furthermore, if `f` is also surjective on the second factor and its image intersects every
"horizontal line" `{(h, i) | h : H}` at most once, then `f'` is actually an isomorphism
`f' : H ≃ I`.

We also prove specialised versions when `f` is the inclusion of a subgroup of the direct product.
(The version for general homomorphisms can easily be reduced to this special case, but the
homomorphism version is more flexible in applications.)
-/

@[expose] public section

open Function Set

variable {G H I : Type*}

section Monoid
variable [Monoid G] [Monoid H] [Monoid I]

namespace MonoidHom

/-- The graph of a monoid homomorphism as a submonoid.

See also `MonoidHom.graph` for the graph as a subgroup. -/
@[to_additive
/-- The graph of a monoid homomorphism as a submonoid.

See also `AddMonoidHom.graph` for the graph as a subgroup. -/]
/--
Definition of `mgraph` / `mgraph` 的定义

English:
definition mgraph
  signature: (f : G ->* H)
  body: {x | f x.1 = x.2}
  one_mem' := map_one f
  mul_mem' {x y} := by simp +contextual

中文:
定义 mgraph
  签名: (f : G ->* H)
  定义体: {x | f x.1 = x.2}
  one_mem' := map_one f
  mul_mem' {x y} := by simp +contextual
-/
def mgraph (f : G ->* H) : Submonoid (G × H) where
  carrier := {x | f x.1 = x.2}
  one_mem' := map_one f
  mul_mem' {x y} := by simp +contextual

-- TODO: Can `to_additive` be smarter about `simps`?
attribute [simps! coe] mgraph
attribute [simps! coe] AddMonoidHom.mgraph
attribute [to_additive existing] coe_mgraph

@[to_additive (attr := simp)]
/--
lemma `mem_mgraph` / 引理 `mem_mgraph`

English:
lemma mem_mgraph
  given: {f : G ->* H} {x : G × H}
  statement: x in f.mgraph ↔ f x.1 = x.2
  proof: .rfl

@[to_additive mgraph_eq_mrange_prod]

中文:
引理 mem_mgraph
  条件: {f : G ->* H} {x : G × H}
  结论: x in f.mgraph ↔ f x.1 = x.2
  证明: .rfl

@[to_additive mgraph_eq_mrange_prod]
-/
lemma mem_mgraph {f : G ->* H} {x : G × H} : x in f.mgraph ↔ f x.1 = x.2 := .rfl

@[to_additive mgraph_eq_mrange_prod]
/--
lemma `mgraph_eq_mrange_prod` / 引理 `mgraph_eq_mrange_prod`

English:
lemma mgraph_eq_mrange_prod
  given: (f : G ->* H)
  statement: f.mgraph = mrange ((id _).prod f)
  proof: by aesop

中文:
引理 mgraph_eq_mrange_prod
  条件: (f : G ->* H)
  结论: f.mgraph = mrange ((id _).prod f)
  证明: by aesop
-/
lemma mgraph_eq_mrange_prod (f : G ->* H) : f.mgraph = mrange ((id _).prod f) := by aesop

/-- **Vertical line test** for monoid homomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some monoid homomorphism `f' : H → I`. -/
@[to_additive /-- **Vertical line test** for monoid homomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some monoid homomorphism `f' : H → I`. -/]
/--
lemma `exists_mrange_eq_mgraph` / 引理 `exists_mrange_eq_mgraph`

English:
lemma exists_mrange_eq_mgraph
  statement: {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
  proof: by
  obtain ⟨f', hf'⟩ := exists_range_eq_graphOn_univ hf₁ hf
  simp only [Set.ext_iff, Set.mem_range, mem_graphOn, mem_univ, true_and, Prod.forall] at hf'
  use
  { toFun := f'
    map_one' := (hf' _ _).1 ⟨1, map_one _⟩
    map_mul' := by
      simp_rw [hf₁.forall]
      rintro g₁ g₂
      exact (hf

中文:
引理 exists_mrange_eq_mgraph
  结论: {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
  证明: by
  obtain ⟨f', hf'⟩ := exists_range_eq_graphOn_univ hf₁ hf
  simp only [Set.ext_iff, Set.mem_range, mem_graphOn, mem_univ, true_and, Prod.forall] at hf'
  use
  { toFun := f'
    map_one' := (hf' _ _).1 ⟨1, map_one _⟩
    map_mul' := by
      simp_rw [hf₁.forall]
      rintro g₁ g₂
      exact (hf

Depends on / 依赖: Prod.ext_iff, Prod.forall, Set.ext_iff, Set.mem_range, SetLike, SetLike.ext_iff, exists_range_eq_graphOn_univ, ext_iff, map_mul, map_one, mem_graphOn, mem_range, mem_univ, simp_rw, true_and
-/
lemma exists_mrange_eq_mgraph {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 -> (f g₁).2 = (f g₂).2) :
    exists f' : H ->* I, mrange f = f'.mgraph := by
  obtain ⟨f', hf'⟩ := exists_range_eq_graphOn_univ hf₁ hf
  simp only [Set.ext_iff, Set.mem_range, mem_graphOn, mem_univ, true_and, Prod.forall] at hf'
  use
  { toFun := f'
    map_one' := (hf' _ _).1 ⟨1, map_one _⟩
    map_mul' := by
      simp_rw [hf₁.forall]
      rintro g₁ g₂
      exact (hf' _ _).1 ⟨g₁ * g₂, by simp [Prod.ext_iff, (hf' (f _).1 _).1 ⟨_, rfl⟩]⟩ }
  simpa [SetLike.ext_iff] using hf'

/-- **Line test** for monoid isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on both
factors and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` and every
"horizontal line" `{(h, i) | h : H}` at most once. Then the image of `f` is the graph of some monoid
isomorphism `f' : H ≃ I`. -/
@[to_additive /-- **Line test** for monoid isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on both
factors and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` and every
"horizontal line" `{(h, i) | h : H}` at most once. Then the image of `f` is the graph of some
monoid isomorphism `f' : H ≃ I`. -/]
/--
lemma `exists_mulEquiv_mrange_eq_mgraph` / 引理 `exists_mulEquiv_mrange_eq_mgraph`

English:
lemma exists_mulEquiv_mrange_eq_mgraph
  statement: {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
  proof: by
  obtain ⟨e₁, he₁⟩ := f.exists_mrange_eq_mgraph hf₁ fun _ _ => (hf _ _).1
obtain ⟨e₂, he₂⟩ := (MulEquiv.prodComm.toMonoidHom.comp f).exists_mrange_eq_mgraph (by simpa)
    by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    rw [SetLike.ext_iff] at he₁ he₂
    aesop (add simp [Prod.swap_e

中文:
引理 exists_mulEquiv_mrange_eq_mgraph
  结论: {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
  证明: by
  obtain ⟨e₁, he₁⟩ := f.exists_mrange_eq_mgraph hf₁ fun _ _ => (hf _ _).1
obtain ⟨e₂, he₂⟩ := (MulEquiv.prodComm.toMonoidHom.comp f).exists_mrange_eq_mgraph (by simpa)
    by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    rw [SetLike.ext_iff] at he₁ he₂
    aesop (add simp [Prod.swap_e

Depends on / 依赖: MulEquiv, MulEquiv.prodComm.toMonoidHom.comp, Prod.swap_eq_iff_eq_swap, SetLike, SetLike.ext_iff, exists_mrange_eq_mgraph, ext_iff, f.exists_mrange_eq_mgraph, invFun, left_inv, map_mul, prodComm, right_inv, swap_eq_iff_eq_swap, toMonoidHom
-/
lemma exists_mulEquiv_mrange_eq_mgraph {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf₂ : Surjective (Prod.snd ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
    exists e : H ≃* I, mrange f = e.toMonoidHom.mgraph := by
  obtain ⟨e₁, he₁⟩ := f.exists_mrange_eq_mgraph hf₁ fun _ _ => (hf _ _).1
obtain ⟨e₂, he₂⟩ := (MulEquiv.prodComm.toMonoidHom.comp f).exists_mrange_eq_mgraph (by simpa)
    by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    rw [SetLike.ext_iff] at he₁ he₂
    aesop (add simp [Prod.swap_eq_iff_eq_swap])
  exact ⟨
  { toFun := e₁
    map_mul' := e₁.map_mul'
    invFun := e₂
    left_inv := fun h => by rw [← he₁₂]
    right_inv := fun i => by rw [he₁₂] }, he₁⟩

end MonoidHom

/-- **Vertical line test** for monoid homomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that `G` maps bijectively to the
first factor. Then `G` is the graph of some monoid homomorphism `f : H → I`. -/
@[to_additive /-- **Vertical line test** for additive monoid homomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that `G` surjects onto the first
factor and `G` intersects every "vertical line" `{(h, i) | i : I}` at most once. Then `G` is the
graph of some monoid homomorphism `f : H → I`. -/]
/--
lemma `Submonoid.exists_eq_mgraph` / 引理 `Submonoid.exists_eq_mgraph`

English:
lemma Submonoid.exists_eq_mgraph
  given: {G : Submonoid (H × I)} (hG₁ : Bijective (Prod.fst ∘ G.subtype))
  proof: by
  simpa using MonoidHom.exists_mrange_eq_mgraph hG₁.surjective
    fun a b h => congr_arg (Prod.snd ∘ G.subtype) (hG₁.injective h)

中文:
引理 Submonoid.exists_eq_mgraph
  条件: {G : Submonoid (H × I)} (hG₁ : Bijective (Prod.fst ∘ G.subtype))
  证明: by
  simpa using MonoidHom.exists_mrange_eq_mgraph hG₁.surjective
    fun a b h => congr_arg (Prod.snd ∘ G.subtype) (hG₁.injective h)

Depends on / 依赖: G.subtype, MonoidHom, MonoidHom.exists_mrange_eq_mgraph, Prod.snd, congr_arg, exists_mrange_eq_mgraph, injective, subtype, surjective
-/
lemma Submonoid.exists_eq_mgraph {G : Submonoid (H × I)} (hG₁ : Bijective (Prod.fst ∘ G.subtype)) :
    exists f : H ->* I, G = f.mgraph := by
  simpa using MonoidHom.exists_mrange_eq_mgraph hG₁.surjective
    fun a b h => congr_arg (Prod.snd ∘ G.subtype) (hG₁.injective h)

/-- **Goursat's lemma** for monoid isomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that the natural maps from `G` to
both factors are bijective. Then `G` is the graph of some isomorphism `f : H ≃* I`. -/
@[to_additive /-- **Goursat's lemma** for additive monoid isomorphisms.

Let `G ≤ H × I` be a submonoid of a product of additive monoids. Assume that the natural maps from
`G` to both factors are bijective. Then `G` is the graph of some isomorphism `f : H ≃+ I`. -/]
/--
lemma `Submonoid.exists_mulEquiv_eq_mgraph` / 引理 `Submonoid.exists_mulEquiv_eq_mgraph`

English:
lemma Submonoid.exists_mulEquiv_eq_mgraph
  statement: {G : Submonoid (H × I)}
  proof: by
  simpa using MonoidHom.exists_mulEquiv_mrange_eq_mgraph hG₁.surjective hG₂.surjective
    fun _ _ => hG₁.injective.eq_iff.trans hG₂.injective.eq_iff.symm

中文:
引理 Submonoid.exists_mulEquiv_eq_mgraph
  结论: {G : Submonoid (H × I)}
  证明: by
  simpa using MonoidHom.exists_mulEquiv_mrange_eq_mgraph hG₁.surjective hG₂.surjective
    fun _ _ => hG₁.injective.eq_iff.trans hG₂.injective.eq_iff.symm

Depends on / 依赖: MonoidHom, MonoidHom.exists_mulEquiv_mrange_eq_mgraph, eq_iff, exists_mulEquiv_mrange_eq_mgraph, injective, injective.eq_iff.symm, injective.eq_iff.trans, surjective
-/
lemma Submonoid.exists_mulEquiv_eq_mgraph {G : Submonoid (H × I)}
    (hG₁ : Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Bijective (Prod.snd ∘ G.subtype)) :
    exists e : H ≃* I, G = e.toMonoidHom.mgraph := by
  simpa using MonoidHom.exists_mulEquiv_mrange_eq_mgraph hG₁.surjective hG₂.surjective
    fun _ _ => hG₁.injective.eq_iff.trans hG₂.injective.eq_iff.symm

end Monoid

section Group
variable [Group G] [Group H] [Group I]

namespace MonoidHom

/-- The graph of a group homomorphism as a subgroup.

See also `MonoidHom.mgraph` for the graph as a submonoid. -/
@[to_additive
/-- The graph of a group homomorphism as a subgroup.

See also `AddMonoidHom.mgraph` for the graph as a submonoid. -/]
/--
Definition of `graph` / `graph` 的定义

English:
definition graph
  signature: (f : G ->* H)
  body: f.mgraph
  inv_mem' {x} := by simp +contextual

中文:
定义 graph
  签名: (f : G ->* H)
  定义体: f.mgraph
  inv_mem' {x} := by simp +contextual

Depends on / 依赖: f.mgraph, mgraph
-/
def graph (f : G ->* H) : Subgroup (G × H) where
  toSubmonoid := f.mgraph
  inv_mem' {x} := by simp +contextual

-- TODO: Can `to_additive` be smarter about `simps`?
attribute [simps! coe toSubmonoid] graph
attribute [simps! coe toAddSubmonoid] AddMonoidHom.graph
attribute [to_additive existing] coe_graph graph_toSubmonoid

@[to_additive]
/--
lemma `mem_graph` / 引理 `mem_graph`

English:
lemma mem_graph
  given: {f : G ->* H} {x : G × H}
  statement: x in f.graph ↔ f x.1 = x.2
  proof: .rfl

@[to_additive graph_eq_range_prod]

中文:
引理 mem_graph
  条件: {f : G ->* H} {x : G × H}
  结论: x in f.graph ↔ f x.1 = x.2
  证明: .rfl

@[to_additive graph_eq_range_prod]
-/
lemma mem_graph {f : G ->* H} {x : G × H} : x in f.graph ↔ f x.1 = x.2 := .rfl

@[to_additive graph_eq_range_prod]
/--
lemma `graph_eq_range_prod` / 引理 `graph_eq_range_prod`

English:
lemma graph_eq_range_prod
  given: (f : G ->* H)
  statement: f.graph = range ((id _).prod f)
  proof: by aesop

中文:
引理 graph_eq_range_prod
  条件: (f : G ->* H)
  结论: f.graph = range ((id _).prod f)
  证明: by aesop
-/
lemma graph_eq_range_prod (f : G ->* H) : f.graph = range ((id _).prod f) := by aesop

/-- **Vertical line test** for group homomorphisms.

Let `f : G → H × I` be a homomorphism to a product of groups. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some group homomorphism `f' : H → I`. -/
@[to_additive /-- **Vertical line test** for group homomorphisms.

Let `f : G → H × I` be a homomorphism to a product of groups. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some group homomorphism `f' : H → I`. -/]
/--
lemma `exists_range_eq_graph` / 引理 `exists_range_eq_graph`

English:
lemma exists_range_eq_graph
  statement: {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
  proof: by
  simpa [SetLike.ext_iff] using! exists_mrange_eq_mgraph hf₁ hf

中文:
引理 exists_range_eq_graph
  结论: {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
  证明: by
  simpa [SetLike.ext_iff] using! exists_mrange_eq_mgraph hf₁ hf

Depends on / 依赖: SetLike, SetLike.ext_iff, exists_mrange_eq_mgraph, ext_iff
-/
lemma exists_range_eq_graph {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 -> (f g₁).2 = (f g₂).2) :
    exists f' : H ->* I, range f = f'.graph := by
  simpa [SetLike.ext_iff] using! exists_mrange_eq_mgraph hf₁ hf

/-- **Line test** for group isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of groups. Assume that `f` is surjective on both
factors and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` and every
"horizontal line" `{(h, i) | h : H}` at most once. Then the image of `f` is the graph of some group
isomorphism `f' : H ≃ I`. -/
@[to_additive /-- **Line test** for monoid isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of groups. Assume that `f` is surjective on both
factors and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` and every
"horizontal line" `{(h, i) | h : H}` at most once. Then the image of `f` is the graph of some
group isomorphism `f' : H ≃ I`. -/]
/--
lemma `exists_mulEquiv_range_eq_graph` / 引理 `exists_mulEquiv_range_eq_graph`

English:
lemma exists_mulEquiv_range_eq_graph
  statement: {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
  proof: by
  simpa [SetLike.ext_iff] using! exists_mulEquiv_mrange_eq_mgraph hf₁ hf₂ hf

中文:
引理 exists_mulEquiv_range_eq_graph
  结论: {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
  证明: by
  simpa [SetLike.ext_iff] using! exists_mulEquiv_mrange_eq_mgraph hf₁ hf₂ hf

Depends on / 依赖: SetLike, SetLike.ext_iff, exists_mulEquiv_mrange_eq_mgraph, ext_iff
-/
lemma exists_mulEquiv_range_eq_graph {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf₂ : Surjective (Prod.snd ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
    exists e : H ≃* I, range f = e.toMonoidHom.graph := by
  simpa [SetLike.ext_iff] using! exists_mulEquiv_mrange_eq_mgraph hf₁ hf₂ hf

end MonoidHom

/-- **Vertical line test** for group homomorphisms.

Let `G ≤ H × I` be a subgroup of a product of monoids. Assume that `G` maps bijectively to the
first factor. Then `G` is the graph of some monoid homomorphism `f : H → I`. -/
@[to_additive /-- **Vertical line test** for additive monoid homomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that `G` surjects onto the first
factor and `G` intersects every "vertical line" `{(h, i) | i : I}` at most once. Then `G` is the
graph of some monoid homomorphism `f : H → I`. -/]
/--
lemma `Subgroup.exists_eq_graph` / 引理 `Subgroup.exists_eq_graph`

English:
lemma Subgroup.exists_eq_graph
  given: {G : Subgroup (H × I)} (hG₁ : Bijective (Prod.fst ∘ G.subtype))
  proof: by
  simpa [SetLike.ext_iff] using! Submonoid.exists_eq_mgraph hG₁

中文:
引理 Subgroup.exists_eq_graph
  条件: {G : Subgroup (H × I)} (hG₁ : Bijective (Prod.fst ∘ G.subtype))
  证明: by
  simpa [SetLike.ext_iff] using! Submonoid.exists_eq_mgraph hG₁

Depends on / 依赖: SetLike, SetLike.ext_iff, Submonoid, Submonoid.exists_eq_mgraph, exists_eq_mgraph, ext_iff
-/
lemma Subgroup.exists_eq_graph {G : Subgroup (H × I)} (hG₁ : Bijective (Prod.fst ∘ G.subtype)) :
    exists f : H ->* I, G = f.graph := by
  simpa [SetLike.ext_iff] using! Submonoid.exists_eq_mgraph hG₁

/-- **Goursat's lemma** for monoid isomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that the natural maps from `G` to
both factors are bijective. Then `G` is the graph of some isomorphism `f : H ≃* I`. -/
@[to_additive /-- **Goursat's lemma** for additive monoid isomorphisms.

Let `G ≤ H × I` be a submonoid of a product of additive monoids. Assume that the natural maps from
`G` to both factors are bijective. Then `G` is the graph of some isomorphism `f : H ≃+ I`. -/]
/--
lemma `Subgroup.exists_mulEquiv_eq_graph` / 引理 `Subgroup.exists_mulEquiv_eq_graph`

English:
lemma Subgroup.exists_mulEquiv_eq_graph
  statement: {G : Subgroup (H × I)}
  proof: by
  simpa [SetLike.ext_iff] using! Submonoid.exists_mulEquiv_eq_mgraph hG₁ hG₂

中文:
引理 Subgroup.exists_mulEquiv_eq_graph
  结论: {G : Subgroup (H × I)}
  证明: by
  simpa [SetLike.ext_iff] using! Submonoid.exists_mulEquiv_eq_mgraph hG₁ hG₂

Depends on / 依赖: SetLike, SetLike.ext_iff, Submonoid, Submonoid.exists_mulEquiv_eq_mgraph, exists_mulEquiv_eq_mgraph, ext_iff
-/
lemma Subgroup.exists_mulEquiv_eq_graph {G : Subgroup (H × I)}
    (hG₁ : Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Bijective (Prod.snd ∘ G.subtype)) :
    exists e : H ≃* I, G = e.toMonoidHom.graph := by
  simpa [SetLike.ext_iff] using! Submonoid.exists_mulEquiv_eq_mgraph hG₁ hG₂

end Group
