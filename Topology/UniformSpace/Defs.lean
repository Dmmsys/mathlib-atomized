/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Data.Rel.Cover
public import Mathlib.Topology.Order

/-!
# Uniform spaces

Uniform spaces are a generalization of metric spaces and topological groups. Many concepts directly
generalize to uniform spaces, e.g.

* uniform continuity (in this file)
* completeness (in `Cauchy.lean`)
* extension of uniform continuous functions to complete spaces (in `IsUniformEmbedding.lean`)
* totally bounded sets (in `Cauchy.lean`)
* totally bounded complete sets are compact (in `Cauchy.lean`)

A uniform structure on a type `X` is a filter `𝓤 X` on `X × X` satisfying some conditions
which makes it reasonable to say that `∀ᶠ (p : X × X) in 𝓤 X, ...` means
"for all p.1 and p.2 in X close enough, ...". Elements of this filter are called entourages
of `X`. The two main examples are:

* If `X` is a metric space, `V ∈ 𝓤 X ↔ ∃ ε > 0, { p | dist p.1 p.2 < ε } ⊆ V`
* If `G` is an additive topological group, `V ∈ 𝓤 G ↔ ∃ U ∈ 𝓝 (0 : G), {p | p.2 - p.1 ∈ U} ⊆ V`

Those examples are generalizations in two different directions of the elementary example where
`X = ℝ` and `V ∈ 𝓤 ℝ ↔ ∃ ε > 0, { p | |p.2 - p.1| < ε } ⊆ V` which features both the topological
group structure on `ℝ` and its metric space structure.

Each uniform structure on `X` induces a topology on `X` characterized by

> `nhds_eq_comap_uniformity : ∀ {x : X}, 𝓝 x = comap (Prod.mk x) (𝓤 X)`

where `Prod.mk x : X → X × X := (fun y ↦ (x, y))` is the partial evaluation of the product
constructor.

The dictionary with metric spaces includes:
* an upper bound for `dist x y` translates into `(x, y) ∈ V` for some `V ∈ 𝓤 X`
* a ball `ball x r` roughly corresponds to `UniformSpace.ball x V := {y | (x, y) ∈ V}`
  for some `V ∈ 𝓤 X`, but the later is more general (it includes in
  particular both open and closed balls for suitable `V`).
  In particular we have:
  `isOpen_iff_ball_subset {s : Set X} : IsOpen s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 X, ball x V ⊆ s`

The triangle inequality is abstracted to a statement involving the composition of relations in `X`.
First note that the triangle inequality in a metric space is equivalent to
`∀ (x y z : X) (r r' : ℝ), dist x y ≤ r → dist y z ≤ r' → dist x z ≤ r + r'`.
Then, for any `V` and `W` with type `Set (X × X)`, the composition `V ○ W : Set (X × X)` is
defined as `{ p : X × X | ∃ z, (p.1, z) ∈ V ∧ (z, p.2) ∈ W }`.
In the metric space case, if `V = { p | dist p.1 p.2 ≤ r }` and `W = { p | dist p.1 p.2 ≤ r' }`
then the triangle inequality, as reformulated above, says `V ○ W` is contained in
`{p | dist p.1 p.2 ≤ r + r'}` which is the entourage associated to the radius `r + r'`.
In general we have `mem_ball_comp (h : y ∈ ball x V) (h' : z ∈ ball y W) : z ∈ ball x (V ○ W)`.
Note that this discussion does not depend on any axiom imposed on the uniformity filter,
it is simply captured by the definition of composition.

The uniform space axioms ask the filter `𝓤 X` to satisfy the following:
* every `V ∈ 𝓤 X` contains the diagonal `idRel = { p | p.1 = p.2 }`. This abstracts the fact
  that `dist x x ≤ r` for every non-negative radius `r` in the metric space case and also that
  `x - x` belongs to every neighborhood of zero in the topological group case.
* `V ∈ 𝓤 X → Prod.swap '' V ∈ 𝓤 X`. This is tightly related the fact that `dist x y = dist y x`
  in a metric space, and to continuity of negation in the topological group case.
* `∀ V ∈ 𝓤 X, ∃ W ∈ 𝓤 X, W ○ W ⊆ V`. In the metric space case, it corresponds
  to cutting the radius of a ball in half and applying the triangle inequality.
  In the topological group case, it comes from continuity of addition at `(0, 0)`.

These three axioms are stated more abstractly in the definition below, in terms of
operations on filters, without directly manipulating entourages.

## Main definitions

* `UniformSpace X` is a uniform space structure on a type `X`
* `UniformContinuous f` is a predicate saying a function `f : α → β` between uniform spaces
  is uniformly continuous : `∀ r ∈ 𝓤 β, ∀ᶠ (x : α × α) in 𝓤 α, (f x.1, f x.2) ∈ r`

## Notation

Localized in `Uniformity`, we have the notation `𝓤 X` for the uniformity on a uniform space `X`.
This file also uses a lot the notation `○` for composition of relations, seen as terms with
type `SetRel X X`. This notation (defined in the file `Mathlib/Data/Rel.lean`) is
localized in `SetRel`.

## Implementation notes

We use the theory of relations as sets developed in `Mathlib/Data/Rel.lean`.
The relevant definition is `SetRel X X := Set (X × X)`, which is the type of elements of
the uniformity filter `𝓤 X : Filter (X × X)`.

The structure `UniformSpace X` bundles a uniform structure on `X`, a topology on `X` and
an assumption saying those are compatible. This may not seem mathematically reasonable at first,
but is in fact an instance of the forgetful inheritance pattern. See Note [forgetful inheritance]
below.

## References

The formalization uses the books:

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

But it makes a more systematic use of the filter library.
-/

@[expose] public section

open Set Filter Topology

universe u v ua ub uc ud

/-!
### Relations, seen as `SetRel α α`
-/

variable {α : Type ua} {β : Type ub} {γ : Type uc} {δ : Type ud} {ι : Sort*}

open scoped SetRel

/-
**SetRel.mem_filter_prod_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SetRel.mem_filter_prod_comm (R : SetRel α α) {f g : Filter α} [R.IsSymm] :
 R in f ×ˢ g ↔ R in g ×ˢ f
参数：R : SetRel α α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetRel.inv_eq_self`：∀ {α : Type u_1} (R : SetRel α α) [R.IsSymm], R.inv 
= R
· 使用定理 `SetRel.inv.eq_1`：∀ {α : Type u_1} {β : Type u_2} (R : SetRel α β), R.inv
 = Prod.swap ⁻¹' R
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.prod_comm`：prod_comm : f ×ˢ g = map Prod.swap (g ×ˢ f)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma SetRel.mem_filter_prod_comm (R : SetRel α α) {f g : Filter α} [R.IsSymm] :
    R ∈ f ×ˢ g ↔ R ∈ g ×ˢ f := by
  rw [← R.inv_eq_self, SetRel.inv, ← mem_map, ← prod_comm, ← SetRel.inv, R.inv_eq_self]

/-- This core description of a uniform space is outside of the type class hierarchy. It is useful
  for constructions of uniform spaces, when the topology is derived from the uniform space. -/
/-
**UniformSpace.Core** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：UniformSpace.Core (α : Type u) where /-- The uniformity filter. Once `Unif
ormSpace` is defined, `𝓤 α` (`_root_.uniformity`) becomes the normal form. -/ un
iformity : Filter (α × α) /-- Every set in the uniformity filter includes the di
agonal. -/ refl : 𝓟 SetRel.id <= uniformity /-- If `s ∈ uniformity`, then `Prod.
swap ⁻¹' s ∈ uniformity`. -/ symm : Tendsto Prod.swap uniformity uniformity /-- 
For every set `u ∈ uniformity`, there exists `v ∈ uniformity` such that `v ○ v ⊆
 u`. -/ comp : (uniformity
参数：α : Type u；`_root_.uniformity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This core description of a uniform space is outside of the type class hierarchy.
 It is useful
  for constructions of uniform spaces, when the topology is derived from the uni
form space.
-/
structure UniformSpace.Core (α : Type u) where
  /-- The uniformity filter. Once `UniformSpace` is defined, `𝓤 α` (`_root_.uniformity`) becomes the
  normal form. -/
  uniformity : Filter (α × α)
  /-- Every set in the uniformity filter includes the diagonal. -/
  refl : 𝓟 SetRel.id ≤ uniformity
  /-- If `s ∈ uniformity`, then `Prod.swap ⁻¹' s ∈ uniformity`. -/
  symm : Tendsto Prod.swap uniformity uniformity
  /-- For every set `u ∈ uniformity`, there exists `v ∈ uniformity` such that `v ○ v ⊆ u`. -/
  comp : (uniformity.lift' fun s => s ○ s) ≤ uniformity
/-
**UniformSpace.Core.comp_mem_uniformity_sets** 是 Mathlib 中的一个定理，位于命名空间 `UniformS
pace.Core`。
形式化陈述：∀ {α : Type ua} {c : UniformSpace.Core α} {s : SetRel α α}, s ∈ c.uniformi
ty → ∃ t ∈ c.uniformity, SetRel.comp t t ⊆ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.mem_lift'_sets`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h
 : Set α → Set β},   Monotone h → ∀ {s : Set β}, s ∈ f.lift' h ↔ ∃ t ∈ f, h t ⊆ 
s
· 使用定理 `Monotone.relComp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {ι : Ty
pe u_6} [inst : Preorder ι] {f : ι → SetRel α β}   {g : ι → SetRel β γ}, Monoton
e f → …
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
· 使用定理 `UniformSpace.Core.comp`：∀ {α : Type u} (self : UniformSpace.Core α), (se
lf.uniformity.lift' fun s => SetRel.comp s s) ≤ self.uniformity
-/
protected theorem UniformSpace.Core.comp_mem_uniformity_sets {c : Core α} {s : SetRel α α}
    (hs : s ∈ c.uniformity) : ∃ t ∈ c.uniformity, t ○ t ⊆ s :=
  (mem_lift'_sets <| monotone_id.relComp monotone_id).mp <| c.comp hs

/-- An alternative constructor for `UniformSpace.Core`. This version unfolds various
`Filter`-related definitions. -/
/-
**UniformSpace.Core.mk'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformSpace.Core.mk' {α : Type u} (U : Filter (α × α)) (refl : forall r i
n U, forall (x), (x, x) in r) (symm : forall r in U, Prod.swap ⁻¹' r in U) (comp
 : forall r in U, exists t in U, t ○ t subseteq r) : UniformSpace.Core α where u
niformity
参数：U : Filter (α × α)；refl : forall r in U, forall (x), (x, x) in r；symm : foral
l r in U, Prod.swap ⁻¹' r in U；comp : forall r in U, exists t in U, t ○ t subset
eq r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternative constructor for `UniformSpace.Core`. This version unfolds various
`Filter`-related definitions.
-/
def UniformSpace.Core.mk' {α : Type u} (U : Filter (α × α)) (refl : ∀ r ∈ U, ∀ (x), (x, x) ∈ r)
    (symm : ∀ r ∈ U, Prod.swap ⁻¹' r ∈ U) (comp : ∀ r ∈ U, ∃ t ∈ U, t ○ t ⊆ r) :
    UniformSpace.Core α where
  uniformity := U
  refl _r ru := SetRel.id_subset_iff.2 ⟨refl _ ru⟩
  symm
  comp _r ru := let ⟨_s, hs, hsr⟩ := comp _ ru; mem_of_superset (mem_lift' hs) hsr

/-- Defining a `UniformSpace.Core` from a filter basis satisfying some uniformity-like axioms. -/
/-
**UniformSpace.Core.mkOfBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformSpace.Core.mkOfBasis {α : Type u} (B : FilterBasis (α × α)) (refl :
 forall r in B, forall (x), (x, x) in r) (symm : forall r in B, exists t in B, t
 subseteq Prod.swap ⁻¹' r) (comp : forall r in B, exists t in B, t ○ t subseteq 
r) : UniformSpace.Core α where uniformity
参数：B : FilterBasis (α × α)；refl : forall r in B, forall (x), (x, x) in r；symm : 
forall r in B, exists t in B, t subseteq Prod.swap ⁻¹' r；comp : forall r in B, e
xists t in B, t ○ t subseteq r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Defining a `UniformSpace.Core` from a filter basis satisfying some uniformity-li
ke axioms.
-/
def UniformSpace.Core.mkOfBasis {α : Type u} (B : FilterBasis (α × α))
    (refl : ∀ r ∈ B, ∀ (x), (x, x) ∈ r) (symm : ∀ r ∈ B, ∃ t ∈ B, t ⊆ Prod.swap ⁻¹' r)
    (comp : ∀ r ∈ B, ∃ t ∈ B, t ○ t ⊆ r) : UniformSpace.Core α where
  uniformity := B.filter
  refl := B.hasBasis.ge_iff.mpr fun _r ru => SetRel.id_subset_iff.2 ⟨refl _ ru⟩
  symm := (B.hasBasis.tendsto_iff B.hasBasis).mpr symm
  comp := ((B.hasBasis.lift' (monotone_id.relComp monotone_id)).le_basis_iff B.hasBasis).2 comp

/-- A uniform space generates a topological space -/
@[instance_reducible]
/-
**UniformSpace.Core.toTopologicalSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformSpace.Core.toTopologicalSpace {α : Type u} (u : UniformSpace.Core α
) : TopologicalSpace α
参数：u : UniformSpace.Core α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A uniform space generates a topological space
-/
def UniformSpace.Core.toTopologicalSpace {α : Type u} (u : UniformSpace.Core α) :
    TopologicalSpace α :=
  .mkOfNhds fun x ↦ .comap (Prod.mk x) u.uniformity
/-
**UniformSpace.Core.ext** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Core`。
形式化陈述：∀ {α : Type ua} {u₁ u₂ : UniformSpace.Core α}, u₁.uniformity = u₂.uniformi
ty → u₁ = u₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
-/
theorem UniformSpace.Core.ext :
    ∀ {u₁ u₂ : UniformSpace.Core α}, u₁.uniformity = u₂.uniformity → u₁ = u₂
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl
/-
**UniformSpace.Core.nhds_toTopologicalSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.Core.nhds_toTopologicalSpace {α : Type u} (u : Core α) (x : α
) : @nhds α u.toTopologicalSpace x = comap (Prod.mk x) u.uniformity
参数：u : Core α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.nhds_mkOfNhds_of_hasBasis`：nhds_mkOfNhds_of_hasBasis {n
 : α -> Filter α} {ι : α -> Sort*} {p : forall a, ι a -> Prop} {s : forall a, ι 
a -> Set α} (hb : forall a, (n a…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `UniformSpace.Core.refl`：∀ {α : Type u} (self : UniformSpace.Core α), Fil
ter.principal SetRel.id ≤ self.uniformity
· 使用定理 `UniformSpace.Core.comp_mem_uniformity_sets`：∀ {α : Type ua} {c : Uniform
Space.Core α} {s : SetRel α α}, s ∈ c.uniformity → ∃ t ∈ c.uniformity, SetRel.co
mp t t ⊆ s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem UniformSpace.Core.nhds_toTopologicalSpace {α : Type u} (u : Core α) (x : α) :
    @nhds α u.toTopologicalSpace x = comap (Prod.mk x) u.uniformity := by
  apply TopologicalSpace.nhds_mkOfNhds_of_hasBasis (fun _ ↦ (basis_sets _).comap _)
  · exact fun a U hU ↦ u.refl hU rfl
  · intro a U hU
    rcases u.comp_mem_uniformity_sets hU with ⟨V, hV, hVU⟩
    filter_upwards [preimage_mem_comap hV] with b hb
    filter_upwards [preimage_mem_comap hV] with c hc
    exact hVU ⟨b, hb, hc⟩

-- the topological structure is embedded in the uniform structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
/-- A uniform space is a generalization of the "uniform" topological aspects of a
  metric space. It consists of a filter on `α × α` called the "uniformity", which
  satisfies properties analogous to the reflexivity, symmetry, and triangle properties
  of a metric.

  A metric space has a natural uniformity, and a uniform space has a natural topology.
  A topological group also has a natural uniformity, even when it is not metrizable. -/
@[wikidata Q652446]
/-
**UniformSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A uniform space is a generalization of the "uniform" topological aspects of a
  metric space. It consists of a filter on `α × α` called the "uniformity", whic
h
  satisfies properties analogous to the reflexivity, symmetry, and triangle prop
erties
  of a metric.

  A metric space has a natural uniformity, and a uniform space has a natural top
ology.
  A topological group also has a natural uniformity, even when it is not metriza
ble.
-/
class UniformSpace (α : Type u) extends TopologicalSpace α where
  /-- The uniformity filter. -/
  protected uniformity : Filter (α × α)
  /-- If `s ∈ uniformity`, then `Prod.swap ⁻¹' s ∈ uniformity`. -/
  protected symm : Tendsto Prod.swap uniformity uniformity
  /-- For every set `u ∈ uniformity`, there exists `v ∈ uniformity` such that `v ○ v ⊆ u`. -/
  protected comp : (uniformity.lift' fun s => s ○ s) ≤ uniformity
  /-- The uniformity agrees with the topology: the neighborhoods filter of each point `x`
  is equal to `Filter.comap (Prod.mk x) (𝓤 α)`. -/
  protected nhds_eq_comap_uniformity (x : α) : 𝓝 x = comap (Prod.mk x) uniformity

/-- The uniformity is a filter on α × α (inferred from an ambient uniform space
/-
**on** 是 Mathlib 中的一个结构，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
  structure on α). -/
/-
**uniformity** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：uniformity (α : Type u) [UniformSpace α] : Filter (α × α)
参数：α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uniformity is a filter on α × α (inferred from an ambient uniform space
  structure on α).
-/
def uniformity (α : Type u) [UniformSpace α] : Filter (α × α) :=
  @UniformSpace.uniformity α _

/-- Notation for the uniformity filter with respect to a non-standard `UniformSpace` instance. -/
scoped[Uniformity] notation "𝓤[" u "]" => @uniformity _ u

@[inherit_doc]
scoped[Uniformity] notation "𝓤" => uniformity

open scoped Uniformity

/-- Construct a `UniformSpace` from a `u : UniformSpace.Core` and a `TopologicalSpace` structure
that is equal to `u.toTopologicalSpace`. -/
/-
**UniformSpace.ofCoreEq** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UniformSpace.ofCoreEq {α : Type u} (u : UniformSpace.Core α) (t : Topologi
calSpace α) (h : t = u.toTopologicalSpace) : UniformSpace α where __
参数：u : UniformSpace.Core α；t : TopologicalSpace α；h : t = u.toTopologicalSpace。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Core.symm`：∀ {α : Type u} (self : UniformSpace.Core α), Fil
ter.Tendsto Prod.swap self.uniformity self.uniformity
· 使用定理 `UniformSpace.Core.comp`：∀ {α : Type u} (self : UniformSpace.Core α), (se
lf.uniformity.lift' fun s => SetRel.comp s s) ≤ self.uniformity

--- 原说明 ---
Construct a `UniformSpace` from a `u : UniformSpace.Core` and a `TopologicalSpac
e` structure
that is equal to `u.toTopologicalSpace`.
-/
abbrev UniformSpace.ofCoreEq {α : Type u} (u : UniformSpace.Core α) (t : TopologicalSpace α)
    (h : t = u.toTopologicalSpace) : UniformSpace α where
  __ := u
  toTopologicalSpace := t
  nhds_eq_comap_uniformity x := by rw [h, u.nhds_toTopologicalSpace]

/-- Construct a `UniformSpace` from a `UniformSpace.Core`. -/
/-
**UniformSpace.ofCore** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UniformSpace.ofCore {α : Type u} (u : UniformSpace.Core α) : UniformSpace 
α
参数：u : UniformSpace.Core α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a `UniformSpace` from a `UniformSpace.Core`.
-/
abbrev UniformSpace.ofCore {α : Type u} (u : UniformSpace.Core α) : UniformSpace α :=
  .ofCoreEq u _ rfl

/-- Construct a `UniformSpace.Core` from a `UniformSpace`. -/
/-
**UniformSpace.toCore** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UniformSpace.toCore (u : UniformSpace α) : UniformSpace.Core α where __
参数：u : UniformSpace α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.symm`：∀ {α : Type u} [self : UniformSpace α], Filter.Tendst
o Prod.swap UniformSpace.uniformity UniformSpace.uniformity
· 使用定理 `UniformSpace.comp`：∀ {α : Type u} [self : UniformSpace α],   (UniformSpa
ce.uniformity.lift' fun s => SetRel.comp s s) ≤ UniformSpace.uniformity

--- 原说明 ---
Construct a `UniformSpace.Core` from a `UniformSpace`.
-/
abbrev UniformSpace.toCore (u : UniformSpace α) : UniformSpace.Core α where
  __ := u
  refl := by
    rintro U hU ⟨x, y⟩ (rfl : x = y)
    have : Prod.mk x ⁻¹' U ∈ 𝓝 x := by
      rw [UniformSpace.nhds_eq_comap_uniformity]
      exact preimage_mem_comap hU
    convert! mem_of_mem_nhds this
/-
**UniformSpace.toCore_toTopologicalSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.toCore_toTopologicalSpace (u : UniformSpace α) : u.toCore.toT
opologicalSpace = u.toTopologicalSpace
参数：u : UniformSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext_nhds`：∀ {X : Type u_2} {t t' : TopologicalSpace X},
 (∀ (x : X), nhds x = nhds x) → t = t'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.nhds_eq_comap_uniformity`：∀ {α : Type u} [self : UniformSpa
ce α] (x : α), nhds x = Filter.comap (Prod.mk x) UniformSpace.uniformity
· 使用定理 `UniformSpace.Core.nhds_toTopologicalSpace`：UniformSpace.Core.nhds_toTopo
logicalSpace {α : Type u} (u : Core α) (x : α) : @nhds α u.toTopologicalSpace x 
= comap (Prod.mk x) u.uniformit…
-/
theorem UniformSpace.toCore_toTopologicalSpace (u : UniformSpace α) :
    u.toCore.toTopologicalSpace = u.toTopologicalSpace :=
  TopologicalSpace.ext_nhds fun a ↦ by
    rw [u.nhds_eq_comap_uniformity, u.toCore.nhds_toTopologicalSpace]
/-
**UniformSpace.mem_uniformity_ofCore_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformSpace.mem_uniformity_ofCore_iff {u : UniformSpace.Core α} {s : SetR
el α α} : s in 𝓤[.ofCore u] ↔ s in u.uniformity
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma UniformSpace.mem_uniformity_ofCore_iff {u : UniformSpace.Core α} {s : SetRel α α} :
    s ∈ 𝓤[.ofCore u] ↔ s ∈ u.uniformity :=
  Iff.rfl

@[ext (iff := false)]
/-
**UniformSpace.ext** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α = uniformity α → u₁
 = u₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext_nhds`：∀ {X : Type u_2} {t t' : TopologicalSpace X},
 (∀ (x : X), nhds x = nhds x) → t = t'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.nhds_eq_comap_uniformity`：∀ {α : Type u} [self : UniformSpa
ce α] (x : α), nhds x = Filter.comap (Prod.mk x) UniformSpace.uniformity
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem UniformSpace.ext {u₁ u₂ : UniformSpace α} (h : 𝓤[u₁] = 𝓤[u₂]) : u₁ = u₂ := by
  have : u₁.toTopologicalSpace = u₂.toTopologicalSpace := TopologicalSpace.ext_nhds fun x ↦ by
    rw [u₁.nhds_eq_comap_uniformity, u₂.nhds_eq_comap_uniformity]
    exact congr_arg (comap _) h
  cases u₁; cases u₂; congr
/-
**UniformSpace.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, u₁ = u₂ ↔ ∀ (s : Set (α × α)), s
 ∈ uniformity α ↔ s ∈ uniformity α
参数：s : Set (α × α)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
-/
protected theorem UniformSpace.ext_iff {u₁ u₂ : UniformSpace α} :
    u₁ = u₂ ↔ ∀ s, s ∈ 𝓤[u₁] ↔ s ∈ 𝓤[u₂] :=
  ⟨fun h _ => h ▸ Iff.rfl, fun h => by ext; exact h _⟩
/-
**UniformSpace.ofCoreEq_toCore** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.ofCoreEq_toCore (u : UniformSpace α) (t : TopologicalSpace α)
 (h : t = u.toCore.toTopologicalSpace) : .ofCoreEq u.toCore t h = u
参数：u : UniformSpace α；t : TopologicalSpace α；h : t = u.toCore.toTopologicalSpace
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
-/
theorem UniformSpace.ofCoreEq_toCore (u : UniformSpace α) (t : TopologicalSpace α)
    (h : t = u.toCore.toTopologicalSpace) : .ofCoreEq u.toCore t h = u :=
  UniformSpace.ext rfl

/-- Replace topology in a `UniformSpace` instance with a propositionally (but possibly not
definitionally) equal one. -/
/-
**UniformSpace.replaceTopology** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UniformSpace.replaceTopology {α : Type*} [i : TopologicalSpace α] (u : Uni
formSpace α) (h : i = u.toTopologicalSpace) : UniformSpace α where __
参数：u : UniformSpace α；h : i = u.toTopologicalSpace。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.symm`：∀ {α : Type u} [self : UniformSpace α], Filter.Tendst
o Prod.swap UniformSpace.uniformity UniformSpace.uniformity
· 使用定理 `UniformSpace.comp`：∀ {α : Type u} [self : UniformSpace α],   (UniformSpa
ce.uniformity.lift' fun s => SetRel.comp s s) ≤ UniformSpace.uniformity

--- 原说明 ---
Replace topology in a `UniformSpace` instance with a propositionally (but possib
ly not
definitionally) equal one.
-/
abbrev UniformSpace.replaceTopology {α : Type*} [i : TopologicalSpace α] (u : UniformSpace α)
    (h : i = u.toTopologicalSpace) : UniformSpace α where
  __ := u
  toTopologicalSpace := i
  nhds_eq_comap_uniformity x := by rw [h, u.nhds_eq_comap_uniformity]
/-
**UniformSpace.replaceTopology_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.replaceTopology_eq {α : Type*} [i : TopologicalSpace α] (u : 
UniformSpace α) (h : i = u.toTopologicalSpace) : u.replaceTopology h = u
参数：u : UniformSpace α；h : i = u.toTopologicalSpace。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
-/
theorem UniformSpace.replaceTopology_eq {α : Type*} [i : TopologicalSpace α] (u : UniformSpace α)
    (h : i = u.toTopologicalSpace) : u.replaceTopology h = u :=
  UniformSpace.ext rfl

section UniformSpace

variable [UniformSpace α]

/-
**nhds_eq_comap_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α).comap (Prod.mk x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.nhds_eq_comap_uniformity`：∀ {α : Type u} [self : UniformSpa
ce α] (x : α), nhds x = Filter.comap (Prod.mk x) UniformSpace.uniformity
-/
theorem nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α).comap (Prod.mk x) :=
  UniformSpace.nhds_eq_comap_uniformity x
/-
**isOpen_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_uniformity {s : Set α} : IsOpen s ↔ forall x in s, { p : α × α | p.
1 = x -> p.2 in s } in 𝓤 α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_uniformity {s : Set α} :
    IsOpen s ↔ ∀ x ∈ s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ 𝓤 α := by
  simp only [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity, mem_comap_prodMk]
/-
**refl_le_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：refl_le_uniformity : 𝓟 SetRel.id <= 𝓤 α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Core.refl`：∀ {α : Type u} (self : UniformSpace.Core α), Fil
ter.principal SetRel.id ≤ self.uniformity
-/
theorem refl_le_uniformity : 𝓟 SetRel.id ≤ 𝓤 α :=
  (@UniformSpace.toCore α _).refl
/-
**uniformity.neBot** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：uniformity.neBot [Nonempty α] : NeBot (𝓤 α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `Set.Nonempty.principal_neBot`：∀ {α : Type u} {s : Set α}, s.Nonempty → (
Filter.principal s).NeBot
· 使用引理 `Set.diagonal_nonempty`：diagonal_nonempty [Nonempty α] : (diagonal α).Non
empty
· 使用定理 `refl_le_uniformity`：refl_le_uniformity : 𝓟 SetRel.id <= 𝓤 α
-/
instance uniformity.neBot [Nonempty α] : NeBot (𝓤 α) :=
  diagonal_nonempty.principal_neBot.mono refl_le_uniformity
/-
**refl_mem_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：refl_mem_uniformity {x : α} {s : SetRel α α} (h : s in 𝓤 α) : (x, x) in s
参数：h : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `refl_le_uniformity`：refl_le_uniformity : 𝓟 SetRel.id <= 𝓤 α
-/
theorem refl_mem_uniformity {x : α} {s : SetRel α α} (h : s ∈ 𝓤 α) : (x, x) ∈ s :=
  refl_le_uniformity h rfl
/-
**isRefl_of_mem_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRefl_of_mem_uniformity {s : SetRel α α} (h : s in 𝓤 α) : s.IsRefl
参数：h : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `refl_mem_uniformity`：refl_mem_uniformity {x : α} {s : SetRel α α} (h : s
 in 𝓤 α) : (x, x) in s
-/
theorem isRefl_of_mem_uniformity {s : SetRel α α} (h : s ∈ 𝓤 α) : s.IsRefl :=
  ⟨fun _ => refl_mem_uniformity h⟩
/-
**mem_uniformity_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_uniformity_of_eq {x y : α} {s : SetRel α α} (h : s in 𝓤 α) (hx : x = y
) : (x, y) in s
参数：h : s in 𝓤 α；hx : x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `refl_le_uniformity`：refl_le_uniformity : 𝓟 SetRel.id <= 𝓤 α
-/
theorem mem_uniformity_of_eq {x y : α} {s : SetRel α α} (h : s ∈ 𝓤 α) (hx : x = y) : (x, y) ∈ s :=
  refl_le_uniformity h hx
/-
**symm_le_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) <= 𝓤 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.symm`：∀ {α : Type u} [self : UniformSpace α], Filter.Tendst
o Prod.swap UniformSpace.uniformity UniformSpace.uniformity
-/
theorem symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) ≤ 𝓤 _ :=
  UniformSpace.symm
/-
**comp_le_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comp_le_uniformity : ((𝓤 α).lift' fun s : SetRel α α => s ○ s) <= 𝓤 α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.comp`：∀ {α : Type u} [self : UniformSpace α],   (UniformSpa
ce.uniformity.lift' fun s => SetRel.comp s s) ≤ UniformSpace.uniformity
-/
theorem comp_le_uniformity : ((𝓤 α).lift' fun s : SetRel α α => s ○ s) ≤ 𝓤 α :=
  UniformSpace.comp
/-
**lift'_comp_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type ua} [inst : UniformSpace α], ((uniformity α).lift' fun s => s.
comp s) = uniformity α
参数：(uniformity α).lift' fun s => s.comp s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `comp_le_uniformity`：comp_le_uniformity : ((𝓤 α).lift' fun s : SetRel α α
 => s ○ s) <= 𝓤 α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_lift'`：le_lift' {f : Filter α} {h : Set α -> Set β} {g : Filte
r β} : g <= f.lift' h ↔ forall s in f, h s in g
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `isRefl_of_mem_uniformity`：isRefl_of_mem_uniformity {s : SetRel α α} (h :
 s in 𝓤 α) : s.IsRefl
· 使用引理 `SetRel.left_subset_comp`：left_subset_comp {R : SetRel α β} [S.IsRefl] : 
R subseteq R ○ S
-/
theorem lift'_comp_uniformity : ((𝓤 α).lift' fun s : SetRel α α => s ○ s) = 𝓤 α :=
  comp_le_uniformity.antisymm <| le_lift'.2 fun _s hs ↦ mem_of_superset hs <|
    have := isRefl_of_mem_uniformity hs; SetRel.left_subset_comp
/-
**tendsto_swap_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_swap_uniformity : Tendsto (@Prod.swap α α) (𝓤 α) (𝓤 α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symm_le_uniformity`：symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) <= 𝓤
 _
-/
theorem tendsto_swap_uniformity : Tendsto (@Prod.swap α α) (𝓤 α) (𝓤 α) :=
  symm_le_uniformity
/-
**comp_mem_uniformity_sets** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comp_mem_uniformity_sets {s : SetRel α α} (hs : s in 𝓤 α) : exists t in 𝓤 
α, t ○ t subseteq s
参数：hs : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.mem_lift'_sets`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h
 : Set α → Set β},   Monotone h → ∀ {s : Set β}, s ∈ f.lift' h ↔ ∃ t ∈ f, h t ⊆ 
s
· 使用定理 `Monotone.relComp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {ι : Ty
pe u_6} [inst : Preorder ι] {f : ι → SetRel α β}   {g : ι → SetRel β γ}, Monoton
e f → …
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
· 使用定理 `comp_le_uniformity`：comp_le_uniformity : ((𝓤 α).lift' fun s : SetRel α α
 => s ○ s) <= 𝓤 α
-/
theorem comp_mem_uniformity_sets {s : SetRel α α} (hs : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, t ○ t ⊆ s :=
  (mem_lift'_sets <| monotone_id.relComp monotone_id).mp <| comp_le_uniformity hs

/-- Relation `fun f g ↦ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α)` is transitive. -/
/-
**Filter.Tendsto.uniformity_trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.uniformity_trans {l : Filter β} {f₁ f₂ f₃ : β -> α} (h₁₂ : 
Tendsto (fun x => (f₁ x, f₂ x)) l (𝓤 α)) (h₂₃ : Tendsto (fun x => (f₂ x, f₃ x)) 
l (𝓤 α)) : Tendsto (fun x => (f₁ x, f₃ x)) l (𝓤 α)
参数：h₁₂ : Tendsto (fun x => (f₁ x, f₂ x)) l (𝓤 α)；h₂₃ : Tendsto (fun x => (f₂ x, 
f₃ x)) l (𝓤 α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_lift'`：le_lift' {f : Filter α} {h : Set α -> Set β} {g : Filte
r β} : g <= f.lift' h ↔ forall s in f, h s in g
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `comp_le_uniformity`：comp_le_uniformity : ((𝓤 α).lift' fun s : SetRel α α
 => s ○ s) <= 𝓤 α

--- 原说明 ---
Relation `fun f g ↦ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α)` is transitive.
-/
theorem Filter.Tendsto.uniformity_trans {l : Filter β} {f₁ f₂ f₃ : β → α}
    (h₁₂ : Tendsto (fun x => (f₁ x, f₂ x)) l (𝓤 α))
    (h₂₃ : Tendsto (fun x => (f₂ x, f₃ x)) l (𝓤 α)) : Tendsto (fun x => (f₁ x, f₃ x)) l (𝓤 α) := by
  refine le_trans (le_lift'.2 fun s hs => mem_map.2 ?_) comp_le_uniformity
  filter_upwards [mem_map.1 (h₁₂ hs), mem_map.1 (h₂₃ hs)] with x hx₁₂ hx₂₃ using ⟨_, hx₁₂, hx₂₃⟩

/-- Relation `fun f g ↦ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α)` is symmetric. -/
/-
**Filter.Tendsto.uniformity_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.uniformity_symm {l : Filter β} {f : β -> α × α} (h : Tendst
o f l (𝓤 α)) : Tendsto (fun x => ((f x).2, (f x).1)) l (𝓤 α)
参数：h : Tendsto f l (𝓤 α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_swap_uniformity`：tendsto_swap_uniformity : Tendsto (@Prod.swap α
 α) (𝓤 α) (𝓤 α)

--- 原说明 ---
Relation `fun f g ↦ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α)` is symmetric.
-/
theorem Filter.Tendsto.uniformity_symm {l : Filter β} {f : β → α × α} (h : Tendsto f l (𝓤 α)) :
    Tendsto (fun x => ((f x).2, (f x).1)) l (𝓤 α) :=
  tendsto_swap_uniformity.comp h

/-- Relation `fun f g ↦ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α)` is reflexive. -/
/-
**tendsto_diag_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_diag_uniformity (f : β -> α) (l : Filter β) : Tendsto (fun x => (f
 x, f x)) l (𝓤 α)
参数：f : β -> α；l : Filter β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `refl_mem_uniformity`：refl_mem_uniformity {x : α} {s : SetRel α α} (h : s
 in 𝓤 α) : (x, x) in s

--- 原说明 ---
Relation `fun f g ↦ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α)` is reflexive.
-/
theorem tendsto_diag_uniformity (f : β → α) (l : Filter β) :
    Tendsto (fun x => (f x, f x)) l (𝓤 α) := fun _s hs =>
  mem_map.2 <| univ_mem' fun _ => refl_mem_uniformity hs
/-
**tendsto_const_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_const_uniformity {a : α} {f : Filter β} : Tendsto (fun _ => (a, a)
) f (𝓤 α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_diag_uniformity`：tendsto_diag_uniformity (f : β -> α) (l : Filte
r β) : Tendsto (fun x => (f x, f x)) l (𝓤 α)
-/
theorem tendsto_const_uniformity {a : α} {f : Filter β} : Tendsto (fun _ => (a, a)) f (𝓤 α) :=
  tendsto_diag_uniformity (fun _ => a) f
/-
**symm_of_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symm_of_uniformity {s : SetRel α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, Set
Rel.IsSymm t ∧ t subseteq s
参数：hs : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symm_le_uniformity`：symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) <= 𝓤
 _
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem symm_of_uniformity {s : SetRel α α} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, SetRel.IsSymm t ∧ t ⊆ s :=
  have : preimage Prod.swap s ∈ 𝓤 α := symm_le_uniformity hs
  ⟨s ∩ preimage Prod.swap s, inter_mem hs this, ⟨fun _ _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩, inter_subset_left⟩
/-
**comp_symm_of_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comp_symm_of_uniformity {s : SetRel α α} (hs : s in 𝓤 α) : exists t in 𝓤 α
, (forall {a b}, (a, b) in t -> (b, a) in t) ∧ t ○ t subseteq s
参数：hs : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `symm_of_uniformity`：symm_of_uniformity {s : SetRel α α} (hs : s in 𝓤 α) 
: exists t in 𝓤 α, SetRel.IsSymm t ∧ t subseteq s
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Monotone.relComp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {ι : Ty
pe u_6} [inst : Preorder ι] {f : ι → SetRel α β}   {g : ι → SetRel β γ}, Monoton
e f → …
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
-/
theorem comp_symm_of_uniformity {s : SetRel α α} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, (∀ {a b}, (a, b) ∈ t → (b, a) ∈ t) ∧ t ○ t ⊆ s :=
  let ⟨_t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  let ⟨t', ht', _, ht'₂⟩ := symm_of_uniformity ht₁
  ⟨t', ht', SetRel.symm _, Subset.trans (monotone_id.relComp monotone_id ht'₂) ht₂⟩
/-
**uniformity_le_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_le_symm : 𝓤 α <= map Prod.swap (𝓤 α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_swap_eq_comap_swap`：map_swap_eq_comap_swap {f : Filter (α × β
)} : map Prod.swap f = comap Prod.swap f
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `tendsto_swap_uniformity`：tendsto_swap_uniformity : Tendsto (@Prod.swap α
 α) (𝓤 α) (𝓤 α)
-/
theorem uniformity_le_symm : 𝓤 α ≤ map Prod.swap (𝓤 α) := by
  rw [map_swap_eq_comap_swap]; exact tendsto_swap_uniformity.le_comap
/-
**uniformity_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_eq_symm : 𝓤 α = map Prod.swap (𝓤 α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `uniformity_le_symm`：uniformity_le_symm : 𝓤 α <= map Prod.swap (𝓤 α)
· 使用定理 `symm_le_uniformity`：symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) <= 𝓤
 _
-/
theorem uniformity_eq_symm : 𝓤 α = map Prod.swap (𝓤 α) :=
  le_antisymm uniformity_le_symm symm_le_uniformity

@[simp]
/-
**comap_swap_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_swap_uniformity : comap (@Prod.swap α α) (𝓤 α) = 𝓤 α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `uniformity_eq_symm`：uniformity_eq_symm : 𝓤 α = map Prod.swap (𝓤 α)
· 使用定理 `Filter.comap_map`：comap_map {f : Filter α} {m : α -> β} (h : Injective m
) : comap m (map m f) = f
· 使用定理 `Prod.swap_injective`：swap_injective : Function.Injective (@swap α β)
-/
theorem comap_swap_uniformity : comap (@Prod.swap α α) (𝓤 α) = 𝓤 α :=
  (congr_arg _ uniformity_eq_symm).trans <| comap_map Prod.swap_injective
/-
**symmetrize_mem_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symmetrize_mem_uniformity {V : SetRel α α} (h : V in 𝓤 α) : SetRel.symmetr
ize V in 𝓤 α
参数：h : V in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_sets`：∀ {α : Type u_1} (self : Filter α) {x y : Set α}, x ∈
 self.sets → y ∈ self.sets → x ∩ y ∈ self.sets
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_swap_uniformity`：comap_swap_uniformity : comap (@Prod.swap α α) (𝓤
 α) = 𝓤 α
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
-/
theorem symmetrize_mem_uniformity {V : SetRel α α} (h : V ∈ 𝓤 α) : SetRel.symmetrize V ∈ 𝓤 α := by
  apply (𝓤 α).inter_sets h
  rw [← comap_swap_uniformity]
  exact preimage_mem_comap h

/-- Symmetric entourages form a basis of `𝓤 α` -/
/-
**UniformSpace.hasBasis_symmetric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.hasBasis_symmetric : (𝓤 α).HasBasis (fun s : SetRel α α => s 
in 𝓤 α ∧ SetRel.IsSymm s) id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.hasBasis_self`：hasBasis_self {l : Filter α} {P : Set α -> Prop} :
 HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r s
ubseteq t
· 使用定理 `symmetrize_mem_uniformity`：symmetrize_mem_uniformity {V : SetRel α α} (h
 : V in 𝓤 α) : SetRel.symmetrize V in 𝓤 α
· 使用引理 `SetRel.symmetrize_subset_self`：symmetrize_subset_self : R.symmetrize sub
seteq R

--- 原说明 ---
Symmetric entourages form a basis of `𝓤 α`
-/
theorem UniformSpace.hasBasis_symmetric :
    (𝓤 α).HasBasis (fun s : SetRel α α => s ∈ 𝓤 α ∧ SetRel.IsSymm s) id :=
  hasBasis_self.2 fun t t_in =>
    ⟨SetRel.symmetrize t, symmetrize_mem_uniformity t_in, inferInstance,
      SetRel.symmetrize_subset_self⟩
/-
**uniformity_lift_le_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_lift_le_swap {g : SetRel α α -> Filter β} {f : Filter β} (hg : 
Monotone g) (h : ((𝓤 α).lift fun s => g (preimage Prod.swap s)) <= f) : (𝓤 α).li
ft g <= f
参数：hg : Monotone g；h : ((𝓤 α).lift fun s => g (preimage Prod.swap s)) <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift_mono`：lift_mono (hf : f₁ <= f₂) (hg : g₁ <= g₂) : f₁.lift g₁
 <= f₂.lift g₂
· 使用定理 `uniformity_le_symm`：uniformity_le_symm : 𝓤 α <= map Prod.swap (𝓤 α)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_lift_eq2`：map_lift_eq2 {g : Set β -> Filter γ} {m : α -> β} (
hg : Monotone g) : (map m f).lift g = f.lift (g ∘ image m)
· 使用定理 `Set.image_swap_eq_preimage_swap`：image_swap_eq_preimage_swap : image (@P
rod.swap α β) = preimage Prod.swap
-/
theorem uniformity_lift_le_swap {g : SetRel α α → Filter β} {f : Filter β} (hg : Monotone g)
    (h : ((𝓤 α).lift fun s => g (preimage Prod.swap s)) ≤ f) : (𝓤 α).lift g ≤ f :=
  calc
    (𝓤 α).lift g ≤ (Filter.map (@Prod.swap α α) <| 𝓤 α).lift g :=
      lift_mono uniformity_le_symm le_rfl
    _ ≤ _ := by rw [map_lift_eq2 hg, image_swap_eq_preimage_swap]; exact h
/-
**uniformity_lift_le_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_lift_le_comp {f : SetRel α α -> Filter β} (h : Monotone f) : ((
𝓤 α).lift fun s => f (s ○ s)) <= (𝓤 α).lift f
参数：h : Monotone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.lift_lift'_assoc`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : Filter α} {g : Set α → Set β} {h : Set β → Filter γ},   Monotone g → Monoto
ne h → (f.lif…
· 使用定理 `Monotone.relComp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {ι : Ty
pe u_6} [inst : Preorder ι] {f : ι → SetRel α β}   {g : ι → SetRel β γ}, Monoton
e f → …
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
· 使用定理 `Filter.lift_mono`：lift_mono (hf : f₁ <= f₂) (hg : g₁ <= g₂) : f₁.lift g₁
 <= f₂.lift g₂
· 使用定理 `comp_le_uniformity`：comp_le_uniformity : ((𝓤 α).lift' fun s : SetRel α α
 => s ○ s) <= 𝓤 α
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem uniformity_lift_le_comp {f : SetRel α α → Filter β} (h : Monotone f) :
    ((𝓤 α).lift fun s => f (s ○ s)) ≤ (𝓤 α).lift f :=
  calc
    ((𝓤 α).lift fun s => f (s ○ s)) = ((𝓤 α).lift' fun s : SetRel α α => s ○ s).lift f := by
      rw [lift_lift'_assoc]
      · exact monotone_id.relComp monotone_id
      · exact h
    _ ≤ (𝓤 α).lift f := lift_mono comp_le_uniformity le_rfl
/-
**comp3_mem_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comp3_mem_uniformity {s : SetRel α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, t
 ○ (t ○ t) subseteq s
参数：hs : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `isRefl_of_mem_uniformity`：isRefl_of_mem_uniformity {s : SetRel α α} (h :
 s in 𝓤 α) : s.IsRefl
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `SetRel.comp_subset_comp`：comp_subset_comp {S₁ S₂ : SetRel β γ} (hR : R₁ 
subseteq R₂) (hS : S₁ subseteq S₂) : R₁ ○ S₁ subseteq R₂ ○ S₂
· 使用引理 `SetRel.left_subset_comp`：left_subset_comp {R : SetRel α β} [S.IsRefl] : 
R subseteq R ○ S
-/
theorem comp3_mem_uniformity {s : SetRel α α} (hs : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, t ○ (t ○ t) ⊆ s :=
  let ⟨_t', ht', ht's⟩ := comp_mem_uniformity_sets hs
  let ⟨t, ht, htt'⟩ := comp_mem_uniformity_sets ht'
  have := isRefl_of_mem_uniformity ht
  ⟨t, ht, (SetRel.comp_subset_comp (SetRel.left_subset_comp.trans htt') htt').trans ht's⟩

/-- See also `comp3_mem_uniformity`. -/
/-
**comp_le_uniformity3** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comp_le_uniformity3 : ((𝓤 α).lift' fun s : SetRel α α => s ○ (s ○ s)) <= 𝓤
 α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `comp3_mem_uniformity`：comp3_mem_uniformity {s : SetRel α α} (hs : s in 𝓤
 α) : exists t in 𝓤 α, t ○ (t ○ t) subseteq s
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.mem_lift'`：mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h

--- 原说明 ---
See also `comp3_mem_uniformity`.
-/
theorem comp_le_uniformity3 : ((𝓤 α).lift' fun s : SetRel α α => s ○ (s ○ s)) ≤ 𝓤 α := fun _ h =>
  let ⟨_t, htU, ht⟩ := comp3_mem_uniformity h
  mem_of_superset (mem_lift' htU) ht

/-- See also `comp_open_symm_mem_uniformity_sets`. -/
/-
**comp_symm_mem_uniformity_sets** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comp_symm_mem_uniformity_sets {s : SetRel α α} (hs : s in 𝓤 α) : exists t 
in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
参数：hs : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `symmetrize_mem_uniformity`：symmetrize_mem_uniformity {V : SetRel α α} (h
 : V in 𝓤 α) : SetRel.symmetrize V in 𝓤 α
· 使用引理 `SetRel.symmetrize_subset_self`：symmetrize_subset_self : R.symmetrize sub
seteq R
· 使用引理 `SetRel.comp_subset_comp`：comp_subset_comp {S₁ S₂ : SetRel β γ} (hR : R₁ 
subseteq R₂) (hS : S₁ subseteq S₂) : R₁ ○ S₁ subseteq R₂ ○ S₂

--- 原说明 ---
See also `comp_open_symm_mem_uniformity_sets`.
-/
theorem comp_symm_mem_uniformity_sets {s : SetRel α α} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, SetRel.IsSymm t ∧ t ○ t ⊆ s := by
  obtain ⟨w, w_in, w_sub⟩ : ∃ w ∈ 𝓤 α, w ○ w ⊆ s := comp_mem_uniformity_sets hs
  use SetRel.symmetrize w, symmetrize_mem_uniformity w_in, inferInstance
  have : SetRel.symmetrize w ⊆ w := SetRel.symmetrize_subset_self
  calc SetRel.symmetrize w ○ SetRel.symmetrize w
    _ ⊆ w ○ w := by gcongr
    _ ⊆ s := w_sub
/-
**subset_comp_self_of_mem_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_comp_self_of_mem_uniformity {s : SetRel α α} (h : s in 𝓤 α) : s sub
seteq s ○ s
参数：h : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isRefl_of_mem_uniformity`：isRefl_of_mem_uniformity {s : SetRel α α} (h :
 s in 𝓤 α) : s.IsRefl
· 使用引理 `SetRel.left_subset_comp`：left_subset_comp {R : SetRel α β} [S.IsRefl] : 
R subseteq R ○ S
-/
theorem subset_comp_self_of_mem_uniformity {s : SetRel α α} (h : s ∈ 𝓤 α) : s ⊆ s ○ s :=
  have := isRefl_of_mem_uniformity h; SetRel.left_subset_comp
/-
**comp_comp_symm_mem_uniformity_sets** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comp_comp_symm_mem_uniformity_sets {s : SetRel α α} (hs : s in 𝓤 α) : exis
ts t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t ○ t subseteq s
参数：hs : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用定理 `subset_comp_self_of_mem_uniformity`：subset_comp_self_of_mem_uniformity {
s : SetRel α α} (h : s in 𝓤 α) : s subseteq s ○ s
· 使用引理 `SetRel.comp_subset_comp`：comp_subset_comp {S₁ S₂ : SetRel β γ} (hR : R₁ 
subseteq R₂) (hS : S₁ subseteq S₂) : R₁ ○ S₁ subseteq R₂ ○ S₂
· 使用引理 `SetRel.comp_subset_comp_right`：comp_subset_comp_right {S₁ S₂ : SetRel β 
γ} (hS : S₁ subseteq S₂) : R ○ S₁ subseteq R ○ S₂
-/
theorem comp_comp_symm_mem_uniformity_sets {s : SetRel α α} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, SetRel.IsSymm t ∧ t ○ t ○ t ⊆ s := by
  rcases comp_symm_mem_uniformity_sets hs with ⟨w, w_in, _, w_sub⟩
  rcases comp_symm_mem_uniformity_sets w_in with ⟨t, t_in, t_symm, t_sub⟩
  use t, t_in, t_symm
  have : t ⊆ t ○ t := subset_comp_self_of_mem_uniformity t_in
  calc
    t ○ t ○ t ⊆ w ○ (t ○ t) := by gcongr
    _ ⊆ w ○ w := by gcongr
    _ ⊆ s := w_sub

/-!
### Balls in uniform spaces
-/

namespace UniformSpace

/-- The ball around `(x : β)` with respect to `(V : Set (β × β))`. Intended to be
used for `V ∈ 𝓤 β`, but this is not needed for the definition. Recovers the
notions of metric space ball when `V = {p | dist p.1 p.2 < r }`. -/
/-
**UniformSpace.ball** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpace`。
形式化陈述：ball (x : β) (V : Set (β × β)) : Set β
参数：x : β；V : Set (β × β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ball around `(x : β)` with respect to `(V : Set (β × β))`. Intended to be
used for `V ∈ 𝓤 β`, but this is not needed for the definition. Recovers the
notions of metric space ball when `V = {p | dist p.1 p.2 < r }`.
-/
def ball (x : β) (V : Set (β × β)) : Set β := Prod.mk x ⁻¹' V

open UniformSpace (ball)
/-
**UniformSpace.mem_ball_self** 是 Mathlib 中的一个引理，位于命名空间 `UniformSpace`。
形式化陈述：mem_ball_self (x : α) {V : SetRel α α} : V in 𝓤 α -> x in ball x V
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `refl_mem_uniformity`：refl_mem_uniformity {x : α} {s : SetRel α α} (h : s
 in 𝓤 α) : (x, x) in s
-/
lemma mem_ball_self (x : α) {V : SetRel α α} : V ∈ 𝓤 α → x ∈ ball x V := refl_mem_uniformity

/-- The triangle inequality for `UniformSpace.ball` -/
/-
**UniformSpace.mem_ball_comp** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：mem_ball_comp {V W : Set (β × β)} {x y z} (h : y in ball x V) (h' : z in b
all y W) : z in ball x (V ○ W)
参数：β × β；h : y in ball x V；h' : z in ball y W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.prodMk_mem_comp`：prodMk_mem_comp (hab : a ~[R] b) (hbc : b ~[S] c
) : a ~[R ○ S] c

--- 原说明 ---
The triangle inequality for `UniformSpace.ball`
-/
theorem mem_ball_comp {V W : Set (β × β)} {x y z} (h : y ∈ ball x V) (h' : z ∈ ball y W) :
    z ∈ ball x (V ○ W) :=
  SetRel.prodMk_mem_comp h h'
/-
**UniformSpace.ball_subset_of_comp_subset** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpac
e`。
形式化陈述：ball_subset_of_comp_subset {V W : Set (β × β)} {x y} (h : x in ball y W) (
h' : W ○ W subseteq V) : ball x W subseteq ball y V
参数：β × β；h : x in ball y W；h' : W ○ W subseteq V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.mem_ball_comp`：mem_ball_comp {V W : Set (β × β)} {x y z} (h
 : y in ball x V) (h' : z in ball y W) : z in ball x (V ○ W)
-/
theorem ball_subset_of_comp_subset {V W : Set (β × β)} {x y} (h : x ∈ ball y W) (h' : W ○ W ⊆ V) :
    ball x W ⊆ ball y V := fun _z z_in => h' (mem_ball_comp h z_in)
/-
**UniformSpace.ball_mono** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：ball_mono {V W : Set (β × β)} (h : V subseteq W) (x : β) : ball x V subset
eq ball x W
参数：β × β；h : V subseteq W；x : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem ball_mono {V W : Set (β × β)} (h : V ⊆ W) (x : β) : ball x V ⊆ ball x W :=
  preimage_mono h
/-
**UniformSpace.ball_inter** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：ball_inter (x : β) (V W : Set (β × β)) : ball x (V inter W) = ball x V int
er ball x W
参数：x : β；V W : Set (β × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_inter`：preimage_inter {s t : Set β} : f ⁻¹' (s inter t) = f
 ⁻¹' s inter f ⁻¹' t
-/
theorem ball_inter (x : β) (V W : Set (β × β)) : ball x (V ∩ W) = ball x V ∩ ball x W :=
  preimage_inter
/-
**UniformSpace.ball_inter_left** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：ball_inter_left (x : β) (V W : Set (β × β)) : ball x (V inter W) subseteq 
ball x V
参数：x : β；V W : Set (β × β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem ball_inter_left (x : β) (V W : Set (β × β)) : ball x (V ∩ W) ⊆ ball x V :=
  ball_mono inter_subset_left x
/-
**UniformSpace.ball_inter_right** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：ball_inter_right (x : β) (V W : Set (β × β)) : ball x (V inter W) subseteq
 ball x W
参数：x : β；V W : Set (β × β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem ball_inter_right (x : β) (V W : Set (β × β)) : ball x (V ∩ W) ⊆ ball x W :=
  ball_mono inter_subset_right x
/-
**UniformSpace.ball_iInter** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：ball_iInter {x : β} {V : ι -> Set (β × β)} : ball x (⋂ i, V i) = ⋂ i, ball
 x (V i)
参数：β × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_iInter`：preimage_iInter {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i
-/
theorem ball_iInter {x : β} {V : ι → Set (β × β)} : ball x (⋂ i, V i) = ⋂ i, ball x (V i) :=
  preimage_iInter
/-
**UniformSpace.mem_ball_symmetry** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：mem_ball_symmetry {V : SetRel β β} [V.IsSymm] {x y} : x in ball y V ↔ y in
 ball x V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.comm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R ↔ (b, a) ∈ R
-/
theorem mem_ball_symmetry {V : SetRel β β} [V.IsSymm] {x y} : x ∈ ball y V ↔ y ∈ ball x V := V.comm
/-
**UniformSpace.ball_eq_of_symmetry** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：ball_eq_of_symmetry {V : SetRel β β} [V.IsSymm] {x} : ball x V = { y | (y,
 x) in V }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.mem_ball_symmetry`：mem_ball_symmetry {V : SetRel β β} [V.Is
Symm] {x y} : x in ball y V ↔ y in ball x V
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ball_eq_of_symmetry {V : SetRel β β} [V.IsSymm] {x} : ball x V = { y | (y, x) ∈ V } := by
  ext y
  rw [mem_ball_symmetry]
  exact Iff.rfl
/-
**UniformSpace.mem_comp_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：mem_comp_of_mem_ball {V W : SetRel β β} {x y z : β} [V.IsSymm] (hx : x in 
ball z V) (hy : y in ball z W) : (x, y) in V ○ W
参数：hx : x in ball z V；hy : y in ball z W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.mem_ball_symmetry`：mem_ball_symmetry {V : SetRel β β} [V.Is
Symm] {x y} : x in ball y V ↔ y in ball x V
-/
theorem mem_comp_of_mem_ball {V W : SetRel β β} {x y z : β} [V.IsSymm] (hx : x ∈ ball z V)
    (hy : y ∈ ball z W) : (x, y) ∈ V ○ W := by
  rw [mem_ball_symmetry] at hx
  exact ⟨z, hx, hy⟩
/-
**UniformSpace.mem_comp_comp** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：mem_comp_comp {V W M : SetRel β β} [W.IsSymm] {p : β × β} : p in V ○ M ○ W
 ↔ (ball p.1 V ×ˢ ball p.2 W inter M).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.mem_ball_symmetry`：mem_ball_symmetry {V : SetRel β β} [V.Is
Symm] {x y} : x in ball y V ↔ y in ball x V
-/
theorem mem_comp_comp {V W M : SetRel β β} [W.IsSymm] {p : β × β} :
    p ∈ V ○ M ○ W ↔ (ball p.1 V ×ˢ ball p.2 W ∩ M).Nonempty := by
  obtain ⟨x, y⟩ := p
  constructor
  · rintro ⟨z, ⟨w, hpw, hwz⟩, hzy⟩
    exact ⟨(w, z), ⟨hpw, by rwa [mem_ball_symmetry]⟩, hwz⟩
  · rintro ⟨⟨w, z⟩, ⟨w_in, z_in⟩, hwz⟩
    rw [mem_ball_symmetry] at z_in
    exact ⟨z, ⟨w, w_in, hwz⟩, z_in⟩
/-
**UniformSpace.isCover_iff_subset_iUnion_ball** 是 Mathlib 中的一个引理，位于命名空间 `Uniform
Space`。
形式化陈述：isCover_iff_subset_iUnion_ball {U : SetRel β β} [U.IsSymm] {s N : Set β} :
 U.IsCover s N ↔ s subseteq ⋃ y in N, ball y U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `SetRel.comm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R ↔ (b, a) ∈ R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isCover_iff_subset_iUnion_ball {U : SetRel β β} [U.IsSymm] {s N : Set β} :
    U.IsCover s N ↔ s ⊆ ⋃ y ∈ N, ball y U := by
  simp [SetRel.IsCover, subset_def, ball, U.comm]

alias ⟨_root_.SetRel.IsCover.subset_iUnion_ball, _root_.SetRel.IsCover.of_subset_iUnion_ball⟩ :=
  isCover_iff_subset_iUnion_ball

end UniformSpace

/-!
### Neighborhoods in uniform spaces
-/

open UniformSpace

/-
**mem_nhds_uniformity_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhds_uniformity_iff_right {x : α} {s : Set α} : s in 𝓝 x ↔ { p : α × α
 | p.1 = x -> p.2 in s } in 𝓤 α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_nhds_uniformity_iff_right {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ { p : α × α | p.1 = x → p.2 ∈ s } ∈ 𝓤 α := by
  simp only [nhds_eq_comap_uniformity, mem_comap_prodMk]
/-
**mem_nhds_uniformity_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhds_uniformity_iff_left {x : α} {s : Set α} : s in 𝓝 x ↔ { p : α × α 
| p.2 = x -> p.1 in s } in 𝓤 α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_eq_symm`：uniformity_eq_symm : 𝓤 α = map Prod.swap (𝓤 α)
· 使用定理 `mem_nhds_uniformity_iff_right`：mem_nhds_uniformity_iff_right {x : α} {s 
: Set α} : s in 𝓝 x ↔ { p : α × α | p.1 = x -> p.2 in s } in 𝓤 α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_nhds_uniformity_iff_left {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ { p : α × α | p.2 = x → p.1 ∈ s } ∈ 𝓤 α := by
  rw [uniformity_eq_symm, mem_nhds_uniformity_iff_right]
  simp only [mem_map, preimage_ofPred_eq, Prod.snd_swap, Prod.fst_swap]
/-
**nhdsWithin_eq_comap_uniformity_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_eq_comap_uniformity_of_mem {x : α} {T : Set α} (hx : x in T) (S
 : Set α) : 𝓝[S] x = (𝓤 α ⊓ 𝓟 (T ×ˢ S)).comap (Prod.mk x)
参数：hx : x in T；S : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Set.mk_preimage_prod_right`：mk_preimage_prod_right (ha : a in s) : Prod.
mk a ⁻¹' s ×ˢ t = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhdsWithin_eq_comap_uniformity_of_mem {x : α} {T : Set α} (hx : x ∈ T) (S : Set α) :
    𝓝[S] x = (𝓤 α ⊓ 𝓟 (T ×ˢ S)).comap (Prod.mk x) := by
  simp [nhdsWithin, nhds_eq_comap_uniformity, hx]
/-
**nhdsWithin_eq_comap_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_eq_comap_uniformity {x : α} (S : Set α) : 𝓝[S] x = (𝓤 α ⊓ 𝓟 (un
iv ×ˢ S)).comap (Prod.mk x)
参数：S : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_eq_comap_uniformity_of_mem`：nhdsWithin_eq_comap_uniformity_of
_mem {x : α} {T : Set α} (hx : x in T) (S : Set α) : 𝓝[S] x = (𝓤 α ⊓ 𝓟 (T ×ˢ S))
.comap (Prod.mk x)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem nhdsWithin_eq_comap_uniformity {x : α} (S : Set α) :
    𝓝[S] x = (𝓤 α ⊓ 𝓟 (univ ×ˢ S)).comap (Prod.mk x) :=
  nhdsWithin_eq_comap_uniformity_of_mem (mem_univ _) S

/-- See also `isOpen_iff_isOpen_ball_subset`. -/
/-
**isOpen_iff_ball_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_iff_ball_subset {s : Set α} : IsOpen s ↔ forall x in s, exists V in
 𝓤 α, ball x V subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See also `isOpen_iff_isOpen_ball_subset`.
-/
theorem isOpen_iff_ball_subset {s : Set α} : IsOpen s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 α, ball x V ⊆ s := by
  simp_rw [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity, mem_comap, ball]
/-
**nhds_basis_uniformity'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_basis_uniformity' {p : ι -> Prop} {s : ι -> SetRel α α} (h : (𝓤 α).Ha
sBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => ball x (s i)
参数：h : (𝓤 α).HasBasis p s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
-/
theorem nhds_basis_uniformity' {p : ι → Prop} {s : ι → SetRel α α} (h : (𝓤 α).HasBasis p s)
    {x : α} : (𝓝 x).HasBasis p fun i => ball x (s i) := by
  rw [nhds_eq_comap_uniformity]
  exact h.comap (Prod.mk x)
/-
**nhds_basis_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> SetRel α α} (h : (𝓤 α).Has
Basis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y, x) in s i }
参数：h : (𝓤 α).HasBasis p s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `nhds_basis_uniformity'`：nhds_basis_uniformity' {p : ι -> Prop} {s : ι ->
 SetRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => ball x
 (s i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `comap_swap_uniformity`：comap_swap_uniformity : comap (@Prod.swap α α) (𝓤
 α) = 𝓤 α
-/
theorem nhds_basis_uniformity {p : ι → Prop} {s : ι → SetRel α α} (h : (𝓤 α).HasBasis p s)
    {x : α} : (𝓝 x).HasBasis p fun i => { y | (y, x) ∈ s i } := by
  replace h := h.comap Prod.swap
  rw [comap_swap_uniformity] at h
  exact nhds_basis_uniformity' h
/-
**nhds_eq_comap_uniformity'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_eq_comap_uniformity' {x : α} : 𝓝 x = (𝓤 α).comap fun y => (y, x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_of_same_basis`：∀ {α : Type u_1} {ι : Sort u_4} {l l' 
: Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l'.HasBasis p s →
 l = l'
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
-/
theorem nhds_eq_comap_uniformity' {x : α} : 𝓝 x = (𝓤 α).comap fun y => (y, x) :=
  (nhds_basis_uniformity (𝓤 α).basis_sets).eq_of_same_basis <| (𝓤 α).basis_sets.comap _
/-
**UniformSpace.mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.mem_nhds_iff {x : α} {s : Set α} : s in 𝓝 x ↔ exists V in 𝓤 α
, ball x V subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `Filter.mem_comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} {m : α 
→ β} {s : Set α}, s ∈ Filter.comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem UniformSpace.mem_nhds_iff {x : α} {s : Set α} : s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 α, ball x V ⊆ s := by
  rw [nhds_eq_comap_uniformity, mem_comap]
  simp_rw [ball]
/-
**UniformSpace.ball_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.ball_mem_nhds (x : α) ⦃V : SetRel α α⦄ (V_in : V in 𝓤 α) : ba
ll x V in 𝓝 x
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.mem_nhds_iff`：UniformSpace.mem_nhds_iff {x : α} {s : Set α}
 : s in 𝓝 x ↔ exists V in 𝓤 α, ball x V subseteq s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem UniformSpace.ball_mem_nhds (x : α) ⦃V : SetRel α α⦄ (V_in : V ∈ 𝓤 α) : ball x V ∈ 𝓝 x := by
  rw [UniformSpace.mem_nhds_iff]
  exact ⟨V, V_in, Subset.rfl⟩
/-
**UniformSpace.ball_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.ball_mem_nhdsWithin {x : α} {S : Set α} ⦃V : SetRel α α⦄ (x_i
n : x in S) (V_in : V in 𝓤 α ⊓ 𝓟 (S ×ˢ S)) : ball x V in 𝓝[S] x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_eq_comap_uniformity_of_mem`：nhdsWithin_eq_comap_uniformity_of
_mem {x : α} {T : Set α} (hx : x in T) (S : Set α) : 𝓝[S] x = (𝓤 α ⊓ 𝓟 (T ×ˢ S))
.comap (Prod.mk x)
· 使用定理 `Filter.mem_comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} {m : α 
→ β} {s : Set α}, s ∈ Filter.comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem UniformSpace.ball_mem_nhdsWithin {x : α} {S : Set α} ⦃V : SetRel α α⦄ (x_in : x ∈ S)
    (V_in : V ∈ 𝓤 α ⊓ 𝓟 (S ×ˢ S)) : ball x V ∈ 𝓝[S] x := by
  rw [nhdsWithin_eq_comap_uniformity_of_mem x_in, mem_comap]
  exact ⟨V, V_in, Subset.rfl⟩
/-
**UniformSpace.mem_nhds_iff_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.mem_nhds_iff_symm {x : α} {s : Set α} : s in 𝓝 x ↔ exists V i
n 𝓤 α, SetRel.IsSymm V ∧ ball x V subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.mem_nhds_iff`：UniformSpace.mem_nhds_iff {x : α} {s : Set α}
 : s in 𝓝 x ↔ exists V in 𝓤 α, ball x V subseteq s
· 使用定理 `symmetrize_mem_uniformity`：symmetrize_mem_uniformity {V : SetRel α α} (h
 : V in 𝓤 α) : SetRel.symmetrize V in 𝓤 α
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用引理 `SetRel.symmetrize_subset_self`：symmetrize_subset_self : R.symmetrize sub
seteq R
-/
theorem UniformSpace.mem_nhds_iff_symm {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 α, SetRel.IsSymm V ∧ ball x V ⊆ s := by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  · rintro ⟨V, V_in, V_sub⟩
    use SetRel.symmetrize V, symmetrize_mem_uniformity V_in, inferInstance
    exact Subset.trans (ball_mono SetRel.symmetrize_subset_self x) V_sub
  · rintro ⟨V, V_in, _, V_sub⟩
    exact ⟨V, V_in, V_sub⟩
/-
**UniformSpace.hasBasis_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.hasBasis_nhds (x : α) : HasBasis (𝓝 x) (fun s : SetRel α α =>
 s in 𝓤 α ∧ SetRel.IsSymm s) fun s => ball x s
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem UniformSpace.hasBasis_nhds (x : α) :
    HasBasis (𝓝 x) (fun s : SetRel α α => s ∈ 𝓤 α ∧ SetRel.IsSymm s) fun s => ball x s :=
  ⟨fun t => by simp [UniformSpace.mem_nhds_iff_symm, and_assoc]⟩

open UniformSpace
/-
**UniformSpace.mem_closure_iff_symm_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.mem_closure_iff_symm_ball {s : Set α} {x} : x in closure s ↔ 
forall {V}, V in 𝓤 α -> SetRel.IsSymm V -> (s inter ball x V).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_nhds_basis`：mem_closure_iff_nhds_basis {p : ι -> Prop} {
s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : x in closure t ↔ forall i, p i -> exi
sts y in t, y in…
· 使用定理 `UniformSpace.hasBasis_nhds`：UniformSpace.hasBasis_nhds (x : α) : HasBasi
s (𝓝 x) (fun s : SetRel α α => s in 𝓤 α ∧ SetRel.IsSymm s) fun s => ball x s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem UniformSpace.mem_closure_iff_symm_ball {s : Set α} {x} :
    x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → SetRel.IsSymm V → (s ∩ ball x V).Nonempty := by
  simp [mem_closure_iff_nhds_basis (hasBasis_nhds x), Set.Nonempty]
/-
**UniformSpace.mem_closure_iff_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.mem_closure_iff_ball {s : Set α} {x} : x in closure s ↔ foral
l {V}, V in 𝓤 α -> (ball x V inter s).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_nhds_basis'`：mem_closure_iff_nhds_basis' {p : ι -> Prop}
 {s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : x in closure t ↔ forall i, p i -> (
s i inter t).None…
· 使用定理 `nhds_basis_uniformity'`：nhds_basis_uniformity' {p : ι -> Prop} {s : ι ->
 SetRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => ball x
 (s i)
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem UniformSpace.mem_closure_iff_ball {s : Set α} {x} :
    x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → (ball x V ∩ s).Nonempty := by
  simp [mem_closure_iff_nhds_basis' (nhds_basis_uniformity' (𝓤 α).basis_sets)]
/-
**UniformSpace.closure_subset_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.closure_subset_preimage {U : SetRel α α} (hU : U in 𝓤 α) (s :
 Set α) : closure s subseteq U.preimage s
参数：hU : U in 𝓤 α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UniformSpace.mem_closure_iff_ball`：UniformSpace.mem_closure_iff_ball {s 
: Set α} {x} : x in closure s ↔ forall {V}, V in 𝓤 α -> (ball x V inter s).Nonem
pty
-/
theorem UniformSpace.closure_subset_preimage
    {U : SetRel α α} (hU : U ∈ 𝓤 α) (s : Set α) : closure s ⊆ U.preimage s := by
  intro x hx
  obtain ⟨y, hxy, hy⟩ := mem_closure_iff_ball.mp hx hU
  exact ⟨y, hy, hxy⟩
/-
**UniformSpace.closure_subset_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.closure_subset_image {U : SetRel α α} (hU : U in 𝓤 α) (s : Se
t α) : closure s subseteq U.image s
参数：hU : U in 𝓤 α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.closure_subset_preimage`：UniformSpace.closure_subset_preima
ge {U : SetRel α α} (hU : U in 𝓤 α) (s : Set α) : closure s subseteq U.preimage 
s
· 使用定理 `symm_le_uniformity`：symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) <= 𝓤
 _
-/
theorem UniformSpace.closure_subset_image
    {U : SetRel α α} (hU : U ∈ 𝓤 α) (s : Set α) : closure s ⊆ U.image s :=
  closure_subset_preimage (symm_le_uniformity hU) s
/-
**nhds_eq_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_eq_uniformity {x : α} : 𝓝 x = (𝓤 α).lift' (ball x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_biInf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l = ⨅ i, ⨅ (_ : p i), Filter
.principal (s …
· 使用定理 `nhds_basis_uniformity'`：nhds_basis_uniformity' {p : ι -> Prop} {s : ι ->
 SetRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => ball x
 (s i)
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem nhds_eq_uniformity {x : α} : 𝓝 x = (𝓤 α).lift' (ball x) :=
  (nhds_basis_uniformity' (𝓤 α).basis_sets).eq_biInf
/-
**nhds_eq_uniformity'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_eq_uniformity' {x : α} : 𝓝 x = (𝓤 α).lift' fun s => { y | (y, x) in s
 }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_biInf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l = ⨅ i, ⨅ (_ : p i), Filter
.principal (s …
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem nhds_eq_uniformity' {x : α} : 𝓝 x = (𝓤 α).lift' fun s => { y | (y, x) ∈ s } :=
  (nhds_basis_uniformity (𝓤 α).basis_sets).eq_biInf
/-
**mem_nhds_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhds_left (x : α) {s : SetRel α α} (h : s in 𝓤 α) : { y : α | (x, y) i
n s } in 𝓝 x
参数：x : α；h : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ball_mem_nhds`：UniformSpace.ball_mem_nhds (x : α) ⦃V : SetR
el α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x
-/
theorem mem_nhds_left (x : α) {s : SetRel α α} (h : s ∈ 𝓤 α) : { y : α | (x, y) ∈ s } ∈ 𝓝 x :=
  ball_mem_nhds x h
/-
**mem_nhds_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhds_right (y : α) {s : SetRel α α} (h : s in 𝓤 α) : { x : α | (x, y) 
in s } in 𝓝 y
参数：y : α；h : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhds_left`：mem_nhds_left (x : α) {s : SetRel α α} (h : s in 𝓤 α) : {
 y : α | (x, y) in s } in 𝓝 x
· 使用定理 `symm_le_uniformity`：symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) <= 𝓤
 _
-/
theorem mem_nhds_right (y : α) {s : SetRel α α} (h : s ∈ 𝓤 α) : { x : α | (x, y) ∈ s } ∈ 𝓝 y :=
  mem_nhds_left _ (symm_le_uniformity h)
/-
**exists_mem_nhds_ball_subset_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_mem_nhds_ball_subset_of_mem_nhds {a : α} {U : Set α} (h : U in 𝓝 a)
 : exists V in 𝓝 a, exists t in 𝓤 α, forall a' in V, UniformSpace.ball a' t subs
eteq U
参数：h : U in 𝓝 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_uniformity_iff_right`：mem_nhds_uniformity_iff_right {x : α} {s 
: Set α} : s in 𝓝 x ↔ { p : α × α | p.1 = x -> p.2 in s } in 𝓤 α
· 使用定理 `mem_nhds_left`：mem_nhds_left (x : α) {s : SetRel α α} (h : s in 𝓤 α) : {
 y : α | (x, y) in s } in 𝓝 x
-/
theorem exists_mem_nhds_ball_subset_of_mem_nhds {a : α} {U : Set α} (h : U ∈ 𝓝 a) :
    ∃ V ∈ 𝓝 a, ∃ t ∈ 𝓤 α, ∀ a' ∈ V, UniformSpace.ball a' t ⊆ U :=
  let ⟨t, ht, htU⟩ := comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 h)
  ⟨_, mem_nhds_left a ht, t, ht, fun a₁ h₁ a₂ h₂ => @htU (a, a₂) ⟨a₁, h₁, h₂⟩ rfl⟩
/-
**tendsto_right_nhds_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_right_nhds_uniformity {a : α} : Tendsto (fun a' => (a', a)) (𝓝 a) 
(𝓤 α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhds_right`：mem_nhds_right (y : α) {s : SetRel α α} (h : s in 𝓤 α) :
 { x : α | (x, y) in s } in 𝓝 y
-/
theorem tendsto_right_nhds_uniformity {a : α} : Tendsto (fun a' => (a', a)) (𝓝 a) (𝓤 α) := fun _ =>
  mem_nhds_right a
/-
**tendsto_left_nhds_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_left_nhds_uniformity {a : α} : Tendsto (fun a' => (a, a')) (𝓝 a) (
𝓤 α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhds_left`：mem_nhds_left (x : α) {s : SetRel α α} (h : s in 𝓤 α) : {
 y : α | (x, y) in s } in 𝓝 x
-/
theorem tendsto_left_nhds_uniformity {a : α} : Tendsto (fun a' => (a, a')) (𝓝 a) (𝓤 α) := fun _ =>
  mem_nhds_left a
/-
**lift_nhds_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_nhds_left {x : α} {g : Set α -> Filter β} (hg : Monotone g) : (𝓝 x).l
ift g = (𝓤 α).lift fun s : SetRel α α => g (ball x s)
参数：hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `Filter.comap_lift_eq2`：comap_lift_eq2 {m : β -> α} {g : Set β -> Filter 
γ} (hg : Monotone g) : (comap m f).lift g = f.lift (g ∘ preimage m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_nhds_left {x : α} {g : Set α → Filter β} (hg : Monotone g) :
    (𝓝 x).lift g = (𝓤 α).lift fun s : SetRel α α => g (ball x s) := by
  rw [nhds_eq_comap_uniformity, comap_lift_eq2 hg]
  simp_rw [ball, Function.comp_def]
/-
**lift_nhds_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_nhds_right {x : α} {g : Set α -> Filter β} (hg : Monotone g) : (𝓝 x).
lift g = (𝓤 α).lift fun s : SetRel α α => g { y | (y, x) in s }
参数：hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_comap_uniformity'`：nhds_eq_comap_uniformity' {x : α} : 𝓝 x = (𝓤 
α).comap fun y => (y, x)
· 使用定理 `Filter.comap_lift_eq2`：comap_lift_eq2 {m : β -> α} {g : Set β -> Filter 
γ} (hg : Monotone g) : (comap m f).lift g = f.lift (g ∘ preimage m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_nhds_right {x : α} {g : Set α → Filter β} (hg : Monotone g) :
    (𝓝 x).lift g = (𝓤 α).lift fun s : SetRel α α => g { y | (y, x) ∈ s } := by
  rw [nhds_eq_comap_uniformity', comap_lift_eq2 hg]
  simp_rw [Function.comp_def, preimage]
/-
**nhds_nhds_eq_uniformity_uniformity_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_nhds_eq_uniformity_uniformity_prod {a b : α} : 𝓝 a ×ˢ 𝓝 b = (𝓤 α).lif
t fun s : SetRel α α => (𝓤 α).lift' fun t => { y : α | (y, a) in s } ×ˢ { y : α 
| (b, y) in t }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_uniformity'`：nhds_eq_uniformity' {x : α} : 𝓝 x = (𝓤 α).lift' fun
 s => { y | (y, x) in s }
· 使用定理 `nhds_eq_uniformity`：nhds_eq_uniformity {x : α} : 𝓝 x = (𝓤 α).lift' (ball
 x)
· 使用定理 `Filter.prod_lift'_lift'`：∀ {α₁ : Type u_5} {α₂ : Type u_6} {β₁ : Type u_
7} {β₂ : Type u_8} {f₁ : Filter α₁} {f₂ : Filter α₂}   {g₁ : Set α₁ → Set β₁} {g
₂ : Set α₂ → …
· 使用定理 `Set.monotone_preimage`：monotone_preimage {f : α -> β} : Monotone (preima
ge f)
-/
theorem nhds_nhds_eq_uniformity_uniformity_prod {a b : α} :
    𝓝 a ×ˢ 𝓝 b = (𝓤 α).lift fun s : SetRel α α =>
      (𝓤 α).lift' fun t => { y : α | (y, a) ∈ s } ×ˢ { y : α | (b, y) ∈ t } := by
  rw [nhds_eq_uniformity', nhds_eq_uniformity, prod_lift'_lift']
  exacts [rfl, monotone_preimage, monotone_preimage]
/-
**Filter.HasBasis.biInter_biUnion_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.biInter_biUnion_ball {p : ι -> Prop} {U : ι -> SetRel α α}
 (h : HasBasis (𝓤 α) p U) (s : Set α) : (⋂ (i) (_ : p i), ⋃ x in s, ball x (U i)
) = closure s
参数：h : HasBasis (𝓤 α) p U；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `mem_closure_iff_nhds_basis`：mem_closure_iff_nhds_basis {p : ι -> Prop} {
s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : x in closure t ↔ forall i, p i -> exi
sts y in t, y in…
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Filter.HasBasis.biInter_biUnion_ball {p : ι → Prop} {U : ι → SetRel α α}
    (h : HasBasis (𝓤 α) p U) (s : Set α) :
    (⋂ (i) (_ : p i), ⋃ x ∈ s, ball x (U i)) = closure s := by
  ext x
  simp [mem_closure_iff_nhds_basis (nhds_basis_uniformity h), ball]

/-! ### Uniform continuity -/

variable [UniformSpace β]

/-- A function `f : α → β` is *uniformly continuous* if `(f x, f y)` tends to the diagonal
as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close to `y`, then
`f x` is close to `f y` no matter where `x` and `y` are located in `α`. -/
@[fun_prop]
/-
**UniformContinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformContinuous (f : α -> β)
参数：f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → β` is *uniformly continuous* if `(f x, f y)` tends to the di
agonal
as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close 
to `y`, then
`f x` is close to `f y` no matter where `x` and `y` are located in `α`.
-/
def UniformContinuous (f : α → β) :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α) (𝓤 β)

/-- Notation for uniform continuity with respect to non-standard `UniformSpace` instances. -/
scoped[Uniformity] notation "UniformContinuous[" u₁ ", " u₂ "]" => @UniformContinuous _ _ u₁ u₂

/-- A function `f : α → β` is *uniformly continuous* on `s : Set α` if `(f x, f y)` tends to
the diagonal as `(x, y)` tends to the diagonal while remaining in `s ×ˢ s`.
In other words, if `x` is sufficiently close to `y`, then `f x` is close to
`f y` no matter where `x` and `y` are located in `s`. -/
@[fun_prop]
/-
**UniformContinuousOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformContinuousOn (f : α -> β) (s : Set α) : Prop
参数：f : α -> β；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → β` is *uniformly continuous* on `s : Set α` if `(f x, f y)` 
tends to
the diagonal as `(x, y)` tends to the diagonal while remaining in `s ×ˢ s`.
In other words, if `x` is sufficiently close to `y`, then `f x` is close to
`f y` no matter where `x` and `y` are located in `s`.
-/
def UniformContinuousOn (f : α → β) (s : Set α) : Prop :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α ⊓ 𝓟 (s ×ˢ s)) (𝓤 β)
/-
**uniformContinuous_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_def {f : α -> β} : UniformContinuous f ↔ forall r in 𝓤 β
, { x : α × α | (f x.1, f x.2) in r } in 𝓤 α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniformContinuous_def {f : α → β} :
    UniformContinuous f ↔ ∀ r ∈ 𝓤 β, { x : α × α | (f x.1, f x.2) ∈ r } ∈ 𝓤 α :=
  Iff.rfl
/-
**uniformContinuous_iff_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_iff_eventually {f : α -> β} : UniformContinuous f ↔ fora
ll r in 𝓤 β, forallᶠ x : α × α in 𝓤 α, (f x.1, f x.2) in r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniformContinuous_iff_eventually {f : α → β} :
    UniformContinuous f ↔ ∀ r ∈ 𝓤 β, ∀ᶠ x : α × α in 𝓤 α, (f x.1, f x.2) ∈ r :=
  Iff.rfl
/-
**uniformContinuousOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuousOn_univ {f : α -> β} : UniformContinuousOn f univ ↔ Unifo
rmContinuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformContinuousOn.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformS
pace α] [inst_1 : UniformSpace β] (f : α → β) (s : Set α),   UniformContinuousOn
 f s =     Fil…
· 使用定理 `UniformContinuous.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (f : α → β),   UniformContinuous f = Filter.Tend
sto (fun x =…
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniformContinuousOn_univ {f : α → β} :
    UniformContinuousOn f univ ↔ UniformContinuous f := by
  rw [UniformContinuousOn, UniformContinuous, univ_prod_univ, principal_univ, inf_top_eq]
/-
**uniformContinuous_of_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_of_const {c : α -> β} (h : forall a b, c a = c b) : Unif
ormContinuous c
参数：h : forall a b, c a = c b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `refl_le_uniformity`：refl_le_uniformity : 𝓟 SetRel.id <= 𝓤 α
-/
theorem uniformContinuous_of_const {c : α → β} (h : ∀ a b, c a = c b) :
    UniformContinuous c :=
  have : (fun x : α × α => (c x.fst, c x.snd)) ⁻¹' SetRel.id = univ :=
    eq_univ_iff_forall.2 fun ⟨a, b⟩ => h a b
  le_trans (map_le_iff_le_comap.2 <| by simp [comap_principal, this]) refl_le_uniformity

@[fun_prop]
/-
**uniformContinuous_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_id : UniformContinuous (@id α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
theorem uniformContinuous_id : UniformContinuous (@id α) := tendsto_id

@[fun_prop]
/-
**uniformContinuous_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_const {b : β} : UniformContinuous fun _ : α => b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_of_const`：uniformContinuous_of_const {c : α -> β} (h :
 forall a b, c a = c b) : UniformContinuous c
-/
theorem uniformContinuous_const {b : β} : UniformContinuous fun _ : α => b :=
  uniformContinuous_of_const fun _ _ => rfl

@[fun_prop]
nonrec theorem UniformContinuous.comp [UniformSpace γ] {g : β → γ} {f : α → β}
    (hg : UniformContinuous g) (hf : UniformContinuous f) : UniformContinuous (g ∘ f) :=
  hg.comp hf

/-- If a function `T` is uniformly continuous in a uniform space `β`,
then its `n`-th iterate `T^[n]` is also uniformly continuous. -/
@[fun_prop]
/-
**UniformContinuous.iterate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.iterate (T : β -> β) (n : Nat) (h : UniformContinuous T)
 : UniformContinuous T^[n]
参数：T : β -> β；n : Nat；h : UniformContinuous T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_succ`：iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f

--- 原说明 ---
If a function `T` is uniformly continuous in a uniform space `β`,
then its `n`-th iterate `T^[n]` is also uniformly continuous.
-/
theorem UniformContinuous.iterate (T : β → β) (n : ℕ) (h : UniformContinuous T) :
    UniformContinuous T^[n] := by
  induction n with
  | zero => exact uniformContinuous_id
  | succ n hn => exact Function.iterate_succ _ _ ▸ UniformContinuous.comp hn h
/-
**Filter.HasBasis.uniformContinuous_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.uniformContinuous_iff {ι'} {p : ι -> Prop} {s : ι -> SetRe
l α α} (ha : (𝓤 α).HasBasis p s) {q : ι' -> Prop} {t : ι' -> Set (β × β)} (hb : 
(𝓤 β).HasBasis q t) {f : α -> β} : UniformContinuous f ↔ forall i, q i -> exists
 j, p j ∧ forall x y, (x, y) in s j -> (f x, f y) in t i
参数：ha : (𝓤 α).HasBasis p s；β × β；hb : (𝓤 β).HasBasis q t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Filter.HasBasis.uniformContinuous_iff {ι'} {p : ι → Prop}
    {s : ι → SetRel α α} (ha : (𝓤 α).HasBasis p s) {q : ι' → Prop} {t : ι' → Set (β × β)}
    (hb : (𝓤 β).HasBasis q t) {f : α → β} :
    UniformContinuous f ↔ ∀ i, q i → ∃ j, p j ∧ ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ t i :=
  (ha.tendsto_iff hb).trans <| by simp only [Prod.forall]
/-
**Filter.HasBasis.uniformContinuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.uniformContinuousOn_iff {ι'} {p : ι -> Prop} {s : ι -> Set
Rel α α} (ha : (𝓤 α).HasBasis p s) {q : ι' -> Prop} {t : ι' -> Set (β × β)} (hb 
: (𝓤 β).HasBasis q t) {f : α -> β} {S : Set α} : UniformContinuousOn f S ↔ foral
l i, q i -> exists j, p j ∧ forall x, x in S -> forall y, y in S -> (x, y) in s 
j -> (f x, f y) in t i
参数：ha : (𝓤 α).HasBasis p s；β × β；hb : (𝓤 β).HasBasis q t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.HasBasis.inf_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Fi
lter.principal s').…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Filter.HasBasis.uniformContinuousOn_iff {ι'} {p : ι → Prop}
    {s : ι → SetRel α α} (ha : (𝓤 α).HasBasis p s) {q : ι' → Prop} {t : ι' → Set (β × β)}
    (hb : (𝓤 β).HasBasis q t) {f : α → β} {S : Set α} :
    UniformContinuousOn f S ↔
      ∀ i, q i → ∃ j, p j ∧ ∀ x, x ∈ S → ∀ y, y ∈ S → (x, y) ∈ s j → (f x, f y) ∈ t i :=
  ((ha.inf_principal (S ×ˢ S)).tendsto_iff hb).trans <| by
    simp_rw [Prod.forall, Set.inter_comm (s _), forall_mem_comm, mem_inter_iff, mem_prod, and_imp]

/-- A map `f : α → β` between uniform spaces is called *uniform inducing* if the uniformity filter
on `α` is the pullback of the uniformity filter on `β` under `Prod.map f f`. If `α` is a separated
space, then this implies that `f` is injective, hence it is a `IsUniformEmbedding`. -/
@[mk_iff, fun_prop]
/-
**IsUniformInducing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type ua} → {β : Type ub} → [UniformSpace α] → [UniformSpace β] → (α →
 β) → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f : α → β` between uniform spaces is called *uniform inducing* if the uni
formity filter
on `α` is the pullback of the uniformity filter on `β` under `Prod.map f f`. If 
`α` is a separated
space, then this implies that `f` is injective, hence it is a `IsUniformEmbeddin
g`.
-/
structure IsUniformInducing (f : α → β) : Prop where
  /-- The uniformity filter on the domain is the pullback of the uniformity filter on the codomain
  under `Prod.map f f`. -/
  comap_uniformity : comap (fun x : α × α ↦ (f x.1, f x.2)) (𝓤 β) = 𝓤 α

/-- A map `f : α → β` between uniform spaces is a *uniform embedding* if it is uniform inducing and
injective. If `α` is a separated space, then the latter assumption follows from the former. -/
@[mk_iff, fun_prop]
/-
**IsUniformEmbedding** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type ua} → {β : Type ub} → [UniformSpace α] → [UniformSpace β] → (α →
 β) → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f : α → β` between uniform spaces is a *uniform embedding* if it is unifo
rm inducing and
injective. If `α` is a separated space, then the latter assumption follows from 
the former.
-/
structure IsUniformEmbedding (f : α → β) : Prop extends IsUniformInducing f where
  /-- A uniform embedding is injective. -/
  injective : Function.Injective f
/-
**IsUniformEmbedding.isUniformInducing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUniformEmbedding.isUniformInducing {f : α -> β} (hf : IsUniformEmbedding
 f) : IsUniformInducing f
参数：hf : IsUniformEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
-/
lemma IsUniformEmbedding.isUniformInducing {f : α → β} (hf : IsUniformEmbedding f) :
    IsUniformInducing f :=
  hf.toIsUniformInducing

end UniformSpace

