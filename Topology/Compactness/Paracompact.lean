/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Yury Kudryashov
-/
module

public import Mathlib.Data.Option.Basic
public import Mathlib.Topology.Separation.Regular

/-!
# Paracompact topological spaces

A topological space `X` is said to be paracompact if every open covering of `X` admits a locally
finite refinement.

The definition requires that each set of the new covering is a subset of one of the sets of the
initial covering. However, one can ensure that each open covering `s : ι → Set X` admits a *precise*
locally finite refinement, i.e., an open covering `t : ι → Set X` with the same index set such that
`∀ i, t i ⊆ s i`, see lemma `precise_refinement`. We also provide a convenience lemma
`precise_refinement_set` that deals with open coverings of a closed subset of `X` instead of the
whole space.

We also prove the following facts.

* Every compact space is paracompact, see instance `paracompact_of_compact`.

* A locally compact sigma compact Hausdorff space is paracompact, see instance
  `paracompact_of_locallyCompact_sigmaCompact`. Moreover, we can choose a locally finite
  refinement with sets in a given collection of filter bases of `𝓝 x`, `x : X`, see
  `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis`. For example, in a proper metric space
  every open covering `⋃ i, s i` admits a refinement `⋃ i, Metric.ball (c i) (r i)`.

* Every paracompact Hausdorff space is normal. This statement is not an instance to avoid loops in
  the instance graph.

* Every `EMetricSpace` is a paracompact space, see instance `EMetric.instParacompactSpace` in
  `Topology/EMetricSpace/Paracompact`.

## TODO

Prove (some of) [Michael's theorems](https://ncatlab.org/nlab/show/Michael%27s+theorem).

## Tags

compact space, paracompact space, locally finite covering
-/

public section


open Set Filter Function

open Filter Topology

universe u v w

/-- A topological space is called paracompact, if every open covering of this space admits a locally
finite refinement. We use the same universe for all types in the definition to avoid creating a
class like `ParacompactSpace.{u v}`. Due to lemma `precise_refinement` below, every open covering
`s : α → Set X` indexed on `α : Type v` has a *precise* locally finite refinement, i.e., a locally
finite refinement `t : α → Set X` indexed on the same type such that each `∀ i, t i ⊆ s i`. -/
/-
**ParacompactSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type v) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is called paracompact, if every open covering of this space 
admits a locally
finite refinement. We use the same universe for all types in the definition to a
void creating a
class like `ParacompactSpace.{u v}`. Due to lemma `precise_refinement` below, ev
ery open covering
`s : α → Set X` indexed on `α : Type v` has a *precise* locally finite refinemen
t, i.e., a locally
finite refinement `t : α → Set X` indexed on the same type such that each `∀ i, 
t i ⊆ s i`.
-/
class ParacompactSpace (X : Type v) [TopologicalSpace X] : Prop where
  /-- Every open cover of a paracompact space assumes a locally finite refinement. -/
  locallyFinite_refinement :
    ∀ (α : Type v) (s : α → Set X), (∀ a, IsOpen (s a)) → (⋃ a, s a = univ) →
      ∃ (β : Type v) (t : β → Set X),
        (∀ b, IsOpen (t b)) ∧ (⋃ b, t b = univ) ∧ LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a

variable {ι : Type u} {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- Any open cover of a paracompact space has a locally finite *precise* refinement, that is,
one indexed on the same type with each open set contained in the corresponding original one. -/
/-
**precise_refinement** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：precise_refinement [ParacompactSpace X] (u : ι -> Set X) (uo : forall a, I
sOpen (u a)) (uc : ⋃ i, u i = univ) : exists v : ι -> Set X, (forall a, IsOpen (
v a)) ∧ ⋃ i, v i = univ ∧ LocallyFinite v ∧ forall a, v a subseteq u a
参数：u : ι -> Set X；uo : forall a, IsOpen (u a)；uc : ⋃ i, u i = univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ParacompactSpace.locallyFinite_refinement`：∀ {X : Type v} {inst : Topolo
gicalSpace X} [self : ParacompactSpace X] (α : Type v) (s : α → Set X),   (∀ (a 
: α), IsOpen (s a)) →     ⋃ a, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Set.forall_subtype_range_iff`：forall_subtype_range_iff {p : range f -> P
rop} : (forall a : range f, p a) ↔ forall i, p ⟨f i, mem_range_self _⟩
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_range`：sUnion_range (f : ι -> Set β) : ⋃₀ range f = ⋃ x, f x
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Any open cover of a paracompact space has a locally finite *precise* refinement,
 that is,
one indexed on the same type with each open set contained in the corresponding o
riginal one.
-/
theorem precise_refinement [ParacompactSpace X] (u : ι → Set X) (uo : ∀ a, IsOpen (u a))
    (uc : ⋃ i, u i = univ) : ∃ v : ι → Set X, (∀ a, IsOpen (v a)) ∧ ⋃ i, v i = univ ∧
    LocallyFinite v ∧ ∀ a, v a ⊆ u a := by
  -- Apply definition to `range u`, then turn existence quantifiers into functions using `choose`
  have := ParacompactSpace.locallyFinite_refinement (range u) (fun r ↦ (r : Set X))
    (forall_subtype_range_iff.2 uo) (by rwa [← sUnion_range, Subtype.range_coe])
  simp only [exists_subtype_range_iff, iUnion_eq_univ_iff] at this
  choose α t hto hXt htf ind hind using this
  choose t_inv ht_inv using hXt
  choose U hxU hU using htf
  -- Send each `i` to the union of `t a` over `a ∈ ind ⁻¹' {i}`
  refine ⟨fun i ↦ ⋃ (a : α) (_ : ind a = i), t a, ?_, ?_, ?_, ?_⟩
  · exact fun a ↦ isOpen_iUnion fun a ↦ isOpen_iUnion fun _ ↦ hto a
  · simp only [eq_univ_iff_forall, mem_iUnion]
    exact fun x ↦ ⟨ind (t_inv x), _, rfl, ht_inv _⟩
  · refine fun x ↦ ⟨U x, hxU x, ((hU x).image ind).subset ?_⟩
    simp only [subset_def, mem_iUnion, mem_ofPred_eq, Set.Nonempty, mem_inter_iff]
    rintro i ⟨y, ⟨a, rfl, hya⟩, hyU⟩
    exact mem_image_of_mem _ ⟨y, hya, hyU⟩
  · simp only [subset_def, mem_iUnion]
    rintro i x ⟨a, rfl, hxa⟩
    exact hind _ hxa

/-- In a paracompact space, every open covering of a closed set admits a locally finite refinement
indexed by the same type. -/
/-
**precise_refinement_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：precise_refinement_set [ParacompactSpace X] {s : Set X} (hs : IsClosed s) 
(u : ι -> Set X) (uo : forall i, IsOpen (u i)) (us : s subseteq ⋃ i, u i) : exis
ts v : ι -> Set X, (forall i, IsOpen (v i)) ∧ (s subseteq ⋃ i, v i) ∧ LocallyFin
ite v ∧ forall i, v i subseteq u i
参数：hs : IsClosed s；u : ι -> Set X；uo : forall i, IsOpen (u i)；us : s subseteq ⋃ 
i, u i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_union_self`：compl_union_self (s : Set α) : sᶜ union s = univ
· 使用定理 `Set.iUnion_option`：iUnion_option {ι} (s : Option ι -> Set α) : ⋃ o, s o 
= s none union ⋃ i, s (some i)
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用定理 `precise_refinement`：precise_refinement [ParacompactSpace X] (u : ι -> Se
t X) (uo : forall a, IsOpen (u a)) (uc : ⋃ i, u i = univ) : exists v : ι -> Set 
X, (fora…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Option.forall`：∀ {α : Type u_1} {p : Option α → Prop}, (∀ (x : Option α)
, p x) ↔ p none ∧ ∀ (x : α), p (some x)
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LocallyFinite.comp_injective`：comp_injective {g : ι' -> ι} (hf : Locally
Finite f) (hg : Injective g) : LocallyFinite (f ∘ g)
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)

--- 原说明 ---
In a paracompact space, every open covering of a closed set admits a locally fin
ite refinement
indexed by the same type.
-/
theorem precise_refinement_set [ParacompactSpace X] {s : Set X} (hs : IsClosed s) (u : ι → Set X)
    (uo : ∀ i, IsOpen (u i)) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, (∀ i, IsOpen (v i)) ∧ (s ⊆ ⋃ i, v i) ∧ LocallyFinite v ∧ ∀ i, v i ⊆ u i := by
  have uc : (iUnion fun i => Option.elim' sᶜ u i) = univ := by
    apply Subset.antisymm (subset_univ _)
    · simp_rw [← compl_union_self s, Option.elim', iUnion_option]
      apply union_subset_union_right sᶜ us
  rcases precise_refinement (Option.elim' sᶜ u) (Option.forall.2 ⟨isOpen_compl_iff.2 hs, uo⟩)
      uc with
    ⟨v, vo, vc, vf, vu⟩
  refine ⟨v ∘ some, fun i ↦ vo _, ?_, vf.comp_injective (Option.some_injective _), fun i ↦ vu _⟩
  · simp only [iUnion_option, ← compl_subset_iff_union] at vc
    exact Subset.trans (subset_compl_comm.1 <| vu Option.none) vc
/-
**ParacompactSpace.of_hasBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ParacompactSpace.of_hasBasis {ι : X -> Sort*} {p : forall x, ι x -> Prop} 
{s : forall x, ι x -> Set X} (hb : forall x, (𝓝 x).HasBasis (p x) (s x)) (h : fo
rall f : (x : X) -> ι x, (forall x, p x (f x)) -> exists (β : Type u) (t : β -> 
Set X), (forall b, IsOpen (t b)) ∧ (⋃ b, t b) = univ ∧ LocallyFinite t ∧ forall 
b, exists x, t b subseteq s x (f x)) : ParacompactSpace X where locallyFinite_re
finement α S ho hu
参数：hb : forall x, (𝓝 x).HasBasis (p x) (s x)；h : forall f : (x : X) -> ι x, (for
all x, p x (f x)) -> exists (β : Type u) (t : β -> Set X), (forall b, IsOpen (t 
b)) ∧ (⋃ b, t b) = univ ∧ LocallyFinite t ∧ forall b, exists x, t b subseteq s x
 (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Set.iUnion_eq_univ_iff`：iUnion_eq_univ_iff {f : ι -> Set α} : ⋃ i, f i =
 univ ↔ forall x, exists i, x in f i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Set.forall_subtype_range_iff`：forall_subtype_range_iff {p : range f -> P
rop} : (forall a : range f, p a) ↔ forall i, p ⟨f i, mem_range_self _⟩
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_subtype`：iUnion_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋃ x : { x // p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩
· 使用定理 `Set.biUnion_range`：biUnion_range {f : ι -> α} {g : α -> Set β} : ⋃ x in 
range f, g x = ⋃ y, g (f y)
· 使用定理 `LocallyFinite.on_range`：on_range (hf : LocallyFinite f) : LocallyFinite 
((↑) : range f -> Set X)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem ParacompactSpace.of_hasBasis {ι : X → Sort*} {p : ∀ x, ι x → Prop} {s : ∀ x, ι x → Set X}
    (hb : ∀ x, (𝓝 x).HasBasis (p x) (s x))
    (h : ∀ f : (x : X) → ι x, (∀ x, p x (f x)) →
      ∃ (β : Type u) (t : β → Set X), (∀ b, IsOpen (t b)) ∧ (⋃ b, t b) = univ ∧ LocallyFinite t ∧
        ∀ b, ∃ x, t b ⊆ s x (f x)) : ParacompactSpace X where
  locallyFinite_refinement α S ho hu := by
    have := fun x ↦ (iUnion_eq_univ_iff.1 hu x).imp fun a ha ↦ (hb _).mem_iff.1 ((ho a).mem_nhds ha)
    choose a f hp hsub using this
    rcases h f hp with ⟨β, t, hto, ht, htf, hts⟩
    refine ⟨range t, Subtype.val, forall_subtype_range_iff.2 hto, ?_, htf.on_range,
      forall_subtype_range_iff.2 fun b ↦ ?_⟩
    · rwa [iUnion_subtype, biUnion_range]
    · rcases hts b with ⟨x, hx⟩
      exact ⟨_, hx.trans (hsub _)⟩
/-
**Topology.IsClosedEmbedding.paracompactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.paracompactSpace [ParacompactSpace Y] {e : X ->
 Y} (he : IsClosedEmbedding e) : ParacompactSpace X where locallyFinite_refineme
nt α s ho hu
参数：he : IsClosedEmbedding e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `precise_refinement_set`：precise_refinement_set [ParacompactSpace X] {s :
 Set X} (hs : IsClosed s) (u : ι -> Set X) (uo : forall i, IsOpen (u i)) (us : s
 subseteq ⋃ …
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
· 使用定理 `LocallyFinite.preimage_continuous`：preimage_continuous {g : Y -> X} (hf 
: LocallyFinite f) (hg : Continuous g) : LocallyFinite (g ⁻¹' f ·)
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.isOpen_iff`：isOpen_iff (hf : IsInducing f) {s : Set 
X} : IsOpen s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem Topology.IsClosedEmbedding.paracompactSpace [ParacompactSpace Y] {e : X → Y}
    (he : IsClosedEmbedding e) : ParacompactSpace X where
  locallyFinite_refinement α s ho hu := by
    choose U hUo hU using fun a ↦ he.isOpen_iff.1 (ho a)
    simp only [← hU] at hu ⊢
    have heU : range e ⊆ ⋃ i, U i := by
      simpa only [range_subset_iff, mem_iUnion, iUnion_eq_univ_iff] using! hu
    rcases precise_refinement_set he.isClosed_range U hUo heU with ⟨V, hVo, heV, hVf, hVU⟩
    refine ⟨α, fun a ↦ e ⁻¹' (V a), fun a ↦ (hVo a).preimage he.continuous, ?_,
      hVf.preimage_continuous he.continuous, fun a ↦ ⟨a, preimage_mono (hVU a)⟩⟩
    simpa only [range_subset_iff, mem_iUnion, iUnion_eq_univ_iff] using! heV
/-
**Homeomorph.paracompactSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.paracompactSpace_iff (e : X ≃ₜ Y) : ParacompactSpace X ↔ Paraco
mpactSpace Y
参数：e : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.paracompactSpace`：Topology.IsClosedEmbedding.
paracompactSpace [ParacompactSpace Y] {e : X -> Y} (he : IsClosedEmbedding e) : 
ParacompactSpace X where locallyF…
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
-/
theorem Homeomorph.paracompactSpace_iff (e : X ≃ₜ Y) : ParacompactSpace X ↔ ParacompactSpace Y :=
  ⟨fun _ ↦ e.symm.isClosedEmbedding.paracompactSpace, fun _ ↦ e.isClosedEmbedding.paracompactSpace⟩

/-- The product of a compact space and a paracompact space is a paracompact space. The formalization
is based on https://dantopology.wordpress.com/2009/10/24/compact-x-paracompact-is-paracompact/
with some minor modifications.

This version assumes that `X` in `X × Y` is compact and `Y` is paracompact, see next lemma for the
other case. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of a compact space and a paracompact space is a paracompact space. T
he formalization
is based on https://dantopology.wordpress.com/2009/10/24/compact-x-paracompact-i
s-paracompact/
with some minor modifications.

This version assumes that `X` in `X × Y` is compact and `Y` is paracompact, see 
next lemma for the
other case.
-/
instance (priority := 200) [CompactSpace X] [ParacompactSpace Y] : ParacompactSpace (X × Y) where
  locallyFinite_refinement α s ho hu := by
    have : ∀ (x : X) (y : Y), ∃ (a : α) (U : Set X) (V : Set Y),
        IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ×ˢ V ⊆ s a := fun x y ↦
      (iUnion_eq_univ_iff.1 hu (x, y)).imp fun a ha ↦ isOpen_prod_iff.1 (ho a) x y ha
    choose a U V hUo hVo hxU hyV hUV using this
    choose T hT using fun y ↦ CompactSpace.elim_nhds_subcover (U · y) fun x ↦
      (hUo x y).mem_nhds (hxU x y)
    set W : Y → Set Y := fun y ↦ ⋂ x ∈ T y, V x y
    have hWo : ∀ y, IsOpen (W y) := fun y ↦ isOpen_biInter_finset fun _ _ ↦ hVo _ _
    have hW : ∀ y, y ∈ W y := fun _ ↦ mem_iInter₂.2 fun _ _ ↦ hyV _ _
    rcases precise_refinement W hWo (iUnion_eq_univ_iff.2 fun y ↦ ⟨y, hW y⟩)
      with ⟨E, hEo, hE, hEf, hEA⟩
    refine ⟨Σ y, T y, fun z ↦ U z.2.1 z.1 ×ˢ E z.1, fun _ ↦ (hUo _ _).prod (hEo _),
      iUnion_eq_univ_iff.2 fun (x, y) ↦ ?_, fun (x, y) ↦ ?_, fun ⟨y, x, hx⟩ ↦ ?_⟩
    · rcases iUnion_eq_univ_iff.1 hE y with ⟨b, hb⟩
      rcases iUnion₂_eq_univ_iff.1 (hT b) x with ⟨a, ha, hx⟩
      exact ⟨⟨b, a, ha⟩, hx, hb⟩
    · rcases hEf y with ⟨t, ht, htf⟩
      refine ⟨univ ×ˢ t, prod_mem_nhds univ_mem ht, ?_⟩
      refine (htf.biUnion fun y _ ↦ finite_range (Sigma.mk y)).subset ?_
      rintro ⟨b, a, ha⟩ ⟨⟨c, d⟩, ⟨-, hd : d ∈ E b⟩, -, hdt : d ∈ t⟩
      exact mem_iUnion₂.2 ⟨b, ⟨d, hd, hdt⟩, mem_range_self _⟩
    · refine ⟨a x y, (Set.prod_mono Subset.rfl ?_).trans (hUV x y)⟩
      exact (hEA _).trans (iInter₂_subset x hx)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 200) [ParacompactSpace X] [CompactSpace Y] : ParacompactSpace (X × Y) :=
  (Homeomorph.prodComm X Y).paracompactSpace_iff.2 inferInstance

-- See note [lower instance priority]
/-- A compact space is paracompact. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A compact space is paracompact.
-/
instance (priority := 100) paracompact_of_compact [CompactSpace X] : ParacompactSpace X := by
  -- the proof is trivial: we choose a finite subcover using compactness, and use it
  refine ⟨fun ι s ho hu ↦ ?_⟩
  rcases isCompact_univ.elim_finite_subcover _ ho hu.ge with ⟨T, hT⟩
  refine ⟨(T : Set ι), fun t ↦ s t, fun t ↦ ho _, ?_, locallyFinite_of_finite _,
    fun t ↦ ⟨t, Subset.rfl⟩⟩
  simpa only [iUnion_coe_set, ← univ_subset_iff]

/-- Let `X` be a locally compact sigma compact Hausdorff topological space, let `s` be a closed set
in `X`. Suppose that for each `x ∈ s` the sets `B x : ι x → Set X` with the predicate
`p x : ι x → Prop` form a basis of the filter `𝓝 x`. Then there exists a locally finite covering
`fun i ↦ B (c i) (r i)` of `s` such that all “centers” `c i` belong to `s` and each `r i` satisfies
`p (c i)`.

The notation is inspired by the case `B x r = Metric.ball x r` but the theorem applies to
`nhds_basis_opens` as well. If the covering must be subordinate to some open covering of `s`, then
the user should use a basis obtained by `Filter.HasBasis.restrict_subset` or a similar lemma, see
the proof of `paracompact_of_locallyCompact_sigmaCompact` for an example.

The formalization is based on two [ncatlab](https://ncatlab.org/) proofs:
* [locally compact and sigma compact spaces are paracompact](https://ncatlab.org/nlab/show/locally+compact+and+sigma-compact+spaces+are+paracompact);
* [open cover of smooth manifold admits locally finite refinement by closed balls](https://ncatlab.org/nlab/show/partition+of+unity#ExistenceOnSmoothManifolds).

See also `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis` for a version of this lemma
dealing with a covering of the whole space.

In most cases (namely, if `B c r ∪ B c r'` is again a set of the form `B c r''`) it is possible
to choose `α = X`. This fact is not yet formalized in `mathlib`. -/
/-
**refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set [WeaklyLocally
CompactSpace X] [SigmaCompactSpace X] [T2Space X] {ι : X -> Type u} {p : forall 
x, ι x -> Prop} {B : forall x, ι x -> Set X} {s : Set X} (hs : IsClosed s) (hB :
 forall x in s, (𝓝 x).HasBasis (p x) (B x)) : exists (α : Type v) (c : α -> X) (
r : forall a, ι (c a)), (forall a, c a in s ∧ p (c a) (r a)) ∧ (s subseteq ⋃ a, 
B (c a) (r a)) ∧ LocallyFinite fun a => B (c a) (r a)
参数：hs : IsClosed s；hB : forall x in s, (𝓝 x).HasBasis (p x) (B x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CompactExhaustion.find_shiftr`：find_shiftr (x : X) : K.shiftr.find x = K
.find x + 1
· 使用定理 `Set.sdiff_subset_sdiff_right`：sdiff_subset_sdiff_right {s t u : Set α} (
h : t subseteq u) : s \ u subseteq s \ t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `CompactExhaustion.mem_sdiff_shiftr_find`：mem_sdiff_shiftr_find (x : X) :
 x in K.shiftr (K.find x + 1) \ K.shiftr (K.find x)
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `IsCompact.diff`：IsCompact.diff (hs : IsCompact s) (ht : IsOpen t) : IsCo
mpact (s \ t)
· 使用定理 `CompactExhaustion.isCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X
] (K : CompactExhaustion X) (n : ℕ), IsCompact (K n)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `IsClosed.compl_mem_nhds`：IsClosed.compl_mem_nhds (hs : IsClosed s) (hx :
 x ∉ s) : sᶜ in 𝓝 x
· 使用定理 `CompactExhaustion.isClosed`：CompactExhaustion.isClosed [T2Space X] (K : 
CompactExhaustion X) (n : Nat) : IsClosed (K n)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CompactExhaustion.subset_interior_succ`：subset_interior_succ (n : Nat) :
 K n subseteq interior (K (n + 1))
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `Set.finite_le_nat`：finite_le_nat (n : Nat) : Set.Finite { i | i <= n }
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Let `X` be a locally compact sigma compact Hausdorff topological space, let `s` 
be a closed set
in `X`. Suppose that for each `x ∈ s` the sets `B x : ι x → Set X` with the pred
icate
`p x : ι x → Prop` form a basis of the filter `𝓝 x`. Then there exists a locally
 finite covering
`fun i ↦ B (c i) (r i)` of `s` such that all “centers” `c i` belong to `s` and e
ach `r i` satisfies
`p (c i)`.

The notation is inspired by the case `B x r = Metric.ball x r` but the theorem a
pplies to
`nhds_basis_opens` as well. If the covering must be subordinate to some open cov
ering of `s`, then
the user should use a basis obtained by `Filter.HasBasis.restrict_subset` or a s
imilar lemma, see
the proof of `paracompact_of_locallyCompact_sigmaCompact` for an example.

The formalization is based on two [ncatlab](https://ncatlab.org/) proofs:
* [locally compact and sigma compact spaces are paracompact](https://ncatlab.org
/nlab/show/locally+compact+and+sigma-compact+spaces+are+paracompact);
* [open cover of smooth manifold admits locally finite refinement by closed ball
s](https://ncatlab.org/nlab/show/partition+of+unity#ExistenceOnSmoothManifolds).

See also `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis` for a version
 of this lemma
dealing with a covering of the whole space.

In most cases (namely, if `B c r ∪ B c r'` is again a set of the form `B c r''`)
 it is possible
to choose `α = X`. This fact is not yet formalized in `mathlib`.
-/
theorem refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] [T2Space X] {ι : X → Type u} {p : ∀ x, ι x → Prop} {B : ∀ x, ι x → Set X}
    {s : Set X} (hs : IsClosed s) (hB : ∀ x ∈ s, (𝓝 x).HasBasis (p x) (B x)) :
    ∃ (α : Type v) (c : α → X) (r : ∀ a, ι (c a)),
      (∀ a, c a ∈ s ∧ p (c a) (r a)) ∧
        (s ⊆ ⋃ a, B (c a) (r a)) ∧ LocallyFinite fun a ↦ B (c a) (r a) := by
  -- For technical reasons we prepend two empty sets to the sequence `CompactExhaustion.choice X`
  set K' : CompactExhaustion X := CompactExhaustion.choice X
  set K : CompactExhaustion X := K'.shiftr.shiftr
  set Kdiff := fun n ↦ K (n + 1) \ interior (K n)
  -- Now we restate some properties of `CompactExhaustion` for `K`/`Kdiff`
  have hKcov : ∀ x, x ∈ Kdiff (K'.find x + 1) := fun x ↦ by
    simpa only [K'.find_shiftr] using
      sdiff_subset_sdiff_right interior_subset (K'.shiftr.mem_sdiff_shiftr_find x)
  have Kdiffc : ∀ n, IsCompact (Kdiff n ∩ s) :=
    fun n ↦ ((K.isCompact _).diff isOpen_interior).inter_right hs
  -- Next we choose a finite covering `B (c n i) (r n i)` of each
  -- `Kdiff (n + 1) ∩ s` such that `B (c n i) (r n i) ∩ s` is disjoint with `K n`
  have : ∀ (n) (x : ↑(Kdiff (n + 1) ∩ s)), (K n)ᶜ ∈ 𝓝 (x : X) :=
    fun n x ↦ (K.isClosed n).compl_mem_nhds fun hx' ↦ x.2.1.2 <| K.subset_interior_succ _ hx'
  choose! r hrp hr using fun n (x : ↑(Kdiff (n + 1) ∩ s)) ↦ (hB x x.2.2).mem_iff.1 (this n x)
  have hxr : ∀ (n x) (hx : x ∈ Kdiff (n + 1) ∩ s), B x (r n ⟨x, hx⟩) ∈ 𝓝 x := fun n x hx ↦
    (hB x hx.2).mem_of_mem (hrp _ ⟨x, hx⟩)
  choose T hT using fun n ↦ (Kdiffc (n + 1)).elim_nhds_subcover' _ (hxr n)
  set T' : ∀ n, Set ↑(Kdiff (n + 1) ∩ s) := fun n ↦ T n
  -- Finally, we take the union of all these coverings
  refine ⟨Σ n, T' n, fun a ↦ a.2, fun a ↦ r a.1 a.2, ?_, ?_, ?_⟩
  · rintro ⟨n, x, hx⟩
    exact ⟨x.2.2, hrp _ _⟩
  · refine fun x hx ↦ mem_iUnion.2 ?_
    rcases mem_iUnion₂.1 (hT _ ⟨hKcov x, hx⟩) with ⟨⟨c, hc⟩, hcT, hcx⟩
    exact ⟨⟨_, ⟨c, hc⟩, hcT⟩, hcx⟩
  · intro x
    refine
      ⟨interior (K (K'.find x + 3)),
        IsOpen.mem_nhds isOpen_interior (K.subset_interior_succ _ (hKcov x).1), ?_⟩
    have : (⋃ k ≤ K'.find x + 2, range (Sigma.mk k) : Set (Σ n, T' n)).Finite :=
      (finite_le_nat _).biUnion fun k _ ↦ finite_range _
    apply this.subset
    rintro ⟨k, c, hc⟩
    simp only [mem_iUnion, mem_ofPred_eq, Subtype.coe_mk]
    rintro ⟨x, hxB : x ∈ B c (r k c), hxK⟩
    refine ⟨k, ?_, ⟨c, hc⟩, rfl⟩
    have := (mem_compl_iff _ _).1 (hr k c hxB)
    contrapose! this with hnk
    exact K.subset hnk (interior_subset hxK)

/-- Let `X` be a locally compact sigma compact Hausdorff topological space. Suppose that for each
`x` the sets `B x : ι x → Set X` with the predicate `p x : ι x → Prop` form a basis of the filter
`𝓝 x`. Then there exists a locally finite covering `fun i ↦ B (c i) (r i)` of `X` such that each
`r i` satisfies `p (c i)`.

The notation is inspired by the case `B x r = Metric.ball x r` but the theorem applies to
`nhds_basis_opens` as well. If the covering must be subordinate to some open covering of `s`, then
the user should use a basis obtained by `Filter.HasBasis.restrict_subset` or a similar lemma, see
the proof of `paracompact_of_locallyCompact_sigmaCompact` for an example.

The formalization is based on two [ncatlab](https://ncatlab.org/) proofs:
* [locally compact and sigma compact spaces are paracompact](https://ncatlab.org/nlab/show/locally+compact+and+sigma-compact+spaces+are+paracompact);
* [open cover of smooth manifold admits locally finite refinement by closed balls](https://ncatlab.org/nlab/show/partition+of+unity#ExistenceOnSmoothManifolds).

See also `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set` for a version of this lemma
dealing with a covering of a closed set.

In most cases (namely, if `B c r ∪ B c r'` is again a set of the form `B c r''`) it is possible
to choose `α = X`. This fact is not yet formalized in `mathlib`. -/
/-
**refinement_of_locallyCompact_sigmaCompact_of_nhds_basis** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：refinement_of_locallyCompact_sigmaCompact_of_nhds_basis [WeaklyLocallyComp
actSpace X] [SigmaCompactSpace X] [T2Space X] {ι : X -> Type u} {p : forall x, ι
 x -> Prop} {B : forall x, ι x -> Set X} (hB : forall x, (𝓝 x).HasBasis (p x) (B
 x)) : exists (α : Type v) (c : α -> X) (r : forall a, ι (c a)), (forall a, p (c
 a) (r a)) ∧ ⋃ a, B (c a) (r a) = univ ∧ LocallyFinite fun a => B (c a) (r a)
参数：hB : forall x, (𝓝 x).HasBasis (p x) (B x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set`：refinement_
of_locallyCompact_sigmaCompact_of_nhds_basis_set [WeaklyLocallyCompactSpace X] [
SigmaCompactSpace X] [T2Space X] {ι : X -> Type u…
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ

--- 原说明 ---
Let `X` be a locally compact sigma compact Hausdorff topological space. Suppose 
that for each
`x` the sets `B x : ι x → Set X` with the predicate `p x : ι x → Prop` form a ba
sis of the filter
`𝓝 x`. Then there exists a locally finite covering `fun i ↦ B (c i) (r i)` of `X
` such that each
`r i` satisfies `p (c i)`.

The notation is inspired by the case `B x r = Metric.ball x r` but the theorem a
pplies to
`nhds_basis_opens` as well. If the covering must be subordinate to some open cov
ering of `s`, then
the user should use a basis obtained by `Filter.HasBasis.restrict_subset` or a s
imilar lemma, see
the proof of `paracompact_of_locallyCompact_sigmaCompact` for an example.

The formalization is based on two [ncatlab](https://ncatlab.org/) proofs:
* [locally compact and sigma compact spaces are paracompact](https://ncatlab.org
/nlab/show/locally+compact+and+sigma-compact+spaces+are+paracompact);
* [open cover of smooth manifold admits locally finite refinement by closed ball
s](https://ncatlab.org/nlab/show/partition+of+unity#ExistenceOnSmoothManifolds).

See also `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set` for a ver
sion of this lemma
dealing with a covering of a closed set.

In most cases (namely, if `B c r ∪ B c r'` is again a set of the form `B c r''`)
 it is possible
to choose `α = X`. This fact is not yet formalized in `mathlib`.
-/
theorem refinement_of_locallyCompact_sigmaCompact_of_nhds_basis [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] [T2Space X] {ι : X → Type u} {p : ∀ x, ι x → Prop} {B : ∀ x, ι x → Set X}
    (hB : ∀ x, (𝓝 x).HasBasis (p x) (B x)) :
    ∃ (α : Type v) (c : α → X) (r : ∀ a, ι (c a)),
      (∀ a, p (c a) (r a)) ∧ ⋃ a, B (c a) (r a) = univ ∧ LocallyFinite fun a ↦ B (c a) (r a) :=
  let ⟨α, c, r, hp, hU, hfin⟩ :=
    refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set isClosed_univ fun x _ ↦ hB x
  ⟨α, c, r, fun a ↦ (hp a).2, univ_subset_iff.1 hU, hfin⟩

-- See note [lower instance priority]
/-- A locally compact sigma compact Hausdorff space is paracompact. See also
`refinement_of_locallyCompact_sigmaCompact_of_nhds_basis` for a more precise statement. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A locally compact sigma compact Hausdorff space is paracompact. See also
`refinement_of_locallyCompact_sigmaCompact_of_nhds_basis` for a more precise sta
tement.
-/
instance (priority := 100) paracompact_of_locallyCompact_sigmaCompact [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] [T2Space X] : ParacompactSpace X := by
  refine ⟨fun α s ho hc ↦ ?_⟩
  choose i hi using iUnion_eq_univ_iff.1 hc
  have : ∀ x : X, (𝓝 x).HasBasis (fun t : Set X ↦ (x ∈ t ∧ IsOpen t) ∧ t ⊆ s (i x)) id :=
    fun x : X ↦ (nhds_basis_opens x).restrict_subset (IsOpen.mem_nhds (ho (i x)) (hi x))
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis this with
    ⟨β, c, t, hto, htc, htf⟩
  exact ⟨β, t, fun x ↦ (hto x).1.2, htc, htf, fun b ↦ ⟨i <| c b, (hto b).2⟩⟩

/-- **Dieudonné's theorem**: a paracompact R₁ space is normal.
Formalization is based on the proof
at [ncatlab](https://ncatlab.org/nlab/show/paracompact+Hausdorff+spaces+are+normal). -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Dieudonné's theorem**: a paracompact R₁ space is normal.
Formalization is based on the proof
at [ncatlab](https://ncatlab.org/nlab/show/paracompact+Hausdorff+spaces+are+norm
al).
-/
instance (priority := 100) NormalSpace.of_paracompactSpace_r1Space
    [R1Space X] [ParacompactSpace X] : NormalSpace X := by
  -- First we show how to go from points to a set on one side.
  have : ∀ s t : Set X, IsClosed s →
      (∀ x ∈ s, ∃ u v, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ t ⊆ v ∧ Disjoint u v) →
      ∃ u v, IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ Disjoint u v := fun s t hs H ↦ by
    /- For each `x ∈ s` we choose open disjoint `u x ∋ x` and `v x ⊇ t`. The sets `u x` form an
        open covering of `s`. We choose a locally finite refinement `u' : s → Set X`, then
        `⋃ i, u' i` and `(closure (⋃ i, u' i))ᶜ` are disjoint open neighborhoods of `s` and `t`. -/
    choose u v hu hv hxu htv huv using SetCoe.forall'.1 H
    rcases precise_refinement_set hs u hu fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hxu _⟩ with
      ⟨u', hu'o, hcov', hu'fin, hsub⟩
    refine ⟨⋃ i, u' i, (closure (⋃ i, u' i))ᶜ, isOpen_iUnion hu'o, isClosed_closure.isOpen_compl,
      hcov', ?_, disjoint_compl_right.mono le_rfl (compl_le_compl subset_closure)⟩
    rw [hu'fin.closure_iUnion, compl_iUnion, subset_iInter_iff]
    refine fun i x hxt hxu ↦
      absurd (htv i hxt) (closure_minimal ?_ (isClosed_compl_iff.2 <| hv _) hxu)
    exact fun y hyu hyv ↦ (huv i).le_bot ⟨hsub _ hyu, hyv⟩
  -- Now we apply the lemma twice: first to `s` and `t`, then to `t` and each point of `s`.
  refine { normal := fun s t hs ht hst ↦ this s t hs fun x hx ↦ ?_ }
  rcases this t {x} ht fun y hy ↦ (by
    simp_rw [singleton_subset_iff]
    exact r1_separation <| ht.not_inseparable hy <| hst.notMem_of_mem_left hx)
    with ⟨v, u, hv, hu, htv, hxu, huv⟩
  exact ⟨u, v, hu, hv, singleton_subset_iff.1 hxu, htv, huv.symm⟩
