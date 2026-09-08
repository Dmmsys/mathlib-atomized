/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.UniformSpace.Compact
public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Compact separated uniform spaces

## Main statement

* **Heine-Cantor** theorem: continuous functions on compact uniform spaces with values in uniform
  spaces are automatically uniformly continuous. There are several variations, the main one is
  `CompactSpace.uniformContinuous_of_continuous`.

## Tags

uniform space, uniform continuity, compact space
-/

public section

open Uniformity Topology Filter UniformSpace Set

variable {α β γ : Type*} [UniformSpace α] [UniformSpace β]

/-!
### Heine-Cantor theorem
-/

/-- Heine-Cantor: a continuous function on a compact uniform space is uniformly
continuous. -/
/-
**CompactSpace.uniformContinuous_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompactSpace.uniformContinuous_of_continuous [CompactSpace α] {f : α -> β}
 (h : Continuous f) : UniformContinuous f
参数：h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_diagonal_eq_uniformity`：nhdsSet_diagonal_eq_uniformity [CompactS
pace α] : 𝓝ˢ (diagonal α) = 𝓤 α
· 使用定理 `Continuous.tendsto_nhdsSet`：Continuous.tendsto_nhdsSet {f : α -> β} {t :
 Set β} (hf : Continuous f) (hst : MapsTo f s t) : Tendsto f (𝓝ˢ s) (𝓝ˢ t)
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `Set.mapsTo_prodMap_diagonal`：mapsTo_prodMap_diagonal : MapsTo (Prod.map 
f f) (diagonal α) (diagonal β)
· 使用定理 `nhdsSet_diagonal_le_uniformity`：nhdsSet_diagonal_le_uniformity : 𝓝ˢ (dia
gonal α) <= 𝓤 α

--- 原说明 ---
Heine-Cantor: a continuous function on a compact uniform space is uniformly
continuous.
-/
theorem CompactSpace.uniformContinuous_of_continuous [CompactSpace α] {f : α → β}
    (h : Continuous f) : UniformContinuous f :=
  calc map (Prod.map f f) (𝓤 α)
    = map (Prod.map f f) (𝓝ˢ (diagonal α)) := by rw [nhdsSet_diagonal_eq_uniformity]
  _ ≤ 𝓝ˢ (diagonal β) := (h.prodMap h).tendsto_nhdsSet mapsTo_prodMap_diagonal
  _ ≤ 𝓤 β := nhdsSet_diagonal_le_uniformity

/-- Heine-Cantor: a continuous function on a compact set of a uniform space is uniformly
continuous. -/
/-
**IsCompact.uniformContinuousOn_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.uniformContinuousOn_of_continuous {s : Set α} {f : α -> β} (hs :
 IsCompact s) (hf : ContinuousOn f s) : UniformContinuousOn f s
参数：hs : IsCompact s；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformContinuousOn_iff_restrict`：uniformContinuousOn_iff_restrict [Unif
ormSpace α] [UniformSpace β] {f : α -> β} {s : Set α} : UniformContinuousOn f s 
↔ UniformContinuous (s…
· 使用定理 `CompactSpace.uniformContinuous_of_continuous`：CompactSpace.uniformContin
uous_of_continuous [CompactSpace α] {f : α -> β} (h : Continuous f) : UniformCon
tinuous f
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)

--- 原说明 ---
Heine-Cantor: a continuous function on a compact set of a uniform space is unifo
rmly
continuous.
-/
theorem IsCompact.uniformContinuousOn_of_continuous {s : Set α} {f : α → β} (hs : IsCompact s)
    (hf : ContinuousOn f s) : UniformContinuousOn f s := by
  rw [uniformContinuousOn_iff_restrict]
  rw [isCompact_iff_compactSpace] at hs
  rw [continuousOn_iff_continuous_domRestrict] at hf
  exact CompactSpace.uniformContinuous_of_continuous hf

/-- If `s` is compact and `f` is continuous at all points of `s`, then `f` is
"uniformly continuous at the set `s`", i.e. `f x` is close to `f y` whenever `x ∈ s` and `y` is
close to `x` (even if `y` is not itself in `s`, so this is a stronger assertion than
`UniformContinuousOn s`). -/
/-
**IsCompact.uniformContinuousAt_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.uniformContinuousAt_of_continuousAt {r : Set (β × β)} {s : Set α
} (hs : IsCompact s) (f : α -> β) (hf : forall a in s, ContinuousAt f a) (hr : r
 in 𝓤 β) : { x : α × α | x.1 in s -> (f x.1, f x.2) in r } in 𝓤 α
参数：β × β；hs : IsCompact s；f : α -> β；hf : forall a in s, ContinuousAt f a；hr : r
 in 𝓤 β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsCompact.elim_nhds_subcover'`：IsCompact.elim_nhds_subcover' (hs : IsCom
pact s) (U : forall x in s, Set X) (hU : forall x (hx : x in s), U x ‹x in s› in
 𝓝 x) : exists t : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.biInter_finset_mem`：biInter_finset_mem {β : Type v} {s : β -> Set
 α} (is : Finset β) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `UniformSpace.mem_ball_self`：mem_ball_self (x : α) {V : SetRel α α} : V i
n 𝓤 α -> x in ball x V
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `exists_mem_nhds_ball_subset_of_mem_nhds`：exists_mem_nhds_ball_subset_of_
mem_nhds {a : α} {U : Set α} (h : U in 𝓝 a) : exists V in 𝓝 a, exists t in 𝓤 α, 
forall a' in V, UniformSpace.…
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `mem_nhds_left`：mem_nhds_left (x : α) {s : SetRel α α} (h : s in 𝓤 α) : {
 y : α | (x, y) in s } in 𝓝 x

--- 原说明 ---
If `s` is compact and `f` is continuous at all points of `s`, then `f` is
"uniformly continuous at the set `s`", i.e. `f x` is close to `f y` whenever `x 
∈ s` and `y` is
close to `x` (even if `y` is not itself in `s`, so this is a stronger assertion 
than
`UniformContinuousOn s`).
-/
theorem IsCompact.uniformContinuousAt_of_continuousAt {r : Set (β × β)} {s : Set α}
    (hs : IsCompact s) (f : α → β) (hf : ∀ a ∈ s, ContinuousAt f a) (hr : r ∈ 𝓤 β) :
    { x : α × α | x.1 ∈ s → (f x.1, f x.2) ∈ r } ∈ 𝓤 α := by
  obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
  choose U hU T hT hb using fun a ha =>
    exists_mem_nhds_ball_subset_of_mem_nhds ((hf a ha).preimage_mem_nhds <| mem_nhds_left _ ht)
  obtain ⟨fs, hsU⟩ := hs.elim_nhds_subcover' U hU
  apply mem_of_superset ((biInter_finset_mem fs).2 fun a _ => hT a a.2)
  rintro ⟨a₁, a₂⟩ h h₁
  obtain ⟨a, ha, haU⟩ := Set.mem_iUnion₂.1 (hsU h₁)
  apply htr
  refine ⟨f a, SetRel.symm t <| hb _ _ _ haU ?_, hb _ _ _ haU ?_⟩
  exacts [mem_ball_self _ (hT a a.2), mem_iInter₂.1 h a ha]
/-
**Continuous.uniformContinuous_of_tendsto_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Continuous.uniformContinuous_of_tendsto_cocompact {f : α -> β} {x : β} (h_
cont : Continuous f) (hx : Tendsto f (cocompact α) (𝓝 x)) : UniformContinuous f
参数：h_cont : Continuous f；hx : Tendsto f (cocompact α) (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `uniformContinuous_def`：uniformContinuous_def {f : α -> β} : UniformConti
nuous f ↔ forall r in 𝓤 β, { x : α × α | (f x.1, f x.2) in r } in 𝓤 α
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_cocompact`：mem_cocompact : s in cocompact X ↔ exists t, IsCom
pact t ∧ tᶜ subseteq s
· 使用定理 `mem_nhds_left`：mem_nhds_left (x : α) {s : SetRel α α} (h : s in 𝓤 α) : {
 y : α | (x, y) in s } in 𝓝 x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `symmetrize_mem_uniformity`：symmetrize_mem_uniformity {V : SetRel α α} (h
 : V in 𝓤 α) : SetRel.symmetrize V in 𝓤 α
· 使用定理 `IsCompact.uniformContinuousAt_of_continuousAt`：IsCompact.uniformContinuo
usAt_of_continuousAt {r : Set (β × β)} {s : Set α} (hs : IsCompact s) (f : α -> 
β) (hf : forall a in s, ContinuousA…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
-/
theorem Continuous.uniformContinuous_of_tendsto_cocompact {f : α → β} {x : β}
    (h_cont : Continuous f) (hx : Tendsto f (cocompact α) (𝓝 x)) : UniformContinuous f :=
  uniformContinuous_def.2 fun r hr => by
    obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
    obtain ⟨s, hs, hst⟩ := mem_cocompact.1 (hx <| mem_nhds_left _ ht)
    apply
      mem_of_superset
        (symmetrize_mem_uniformity <|
          (hs.uniformContinuousAt_of_continuousAt f fun _ _ => h_cont.continuousAt) <|
            symmetrize_mem_uniformity hr)
    rintro ⟨b₁, b₂⟩ h
    by_cases h₁ : b₁ ∈ s; · exact (h.1 h₁).1
    by_cases h₂ : b₂ ∈ s; · exact (h.2 h₂).2
    apply htr
    exact ⟨x, SetRel.symm t <| hst h₁, hst h₂⟩

@[to_additive]
/-
**HasCompactMulSupport.uniformContinuous_of_continuous** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：HasCompactMulSupport.uniformContinuous_of_continuous {f : α -> β} [One β] 
(h1 : HasCompactMulSupport f) (h2 : Continuous f) : UniformContinuous f
参数：h1 : HasCompactMulSupport f；h2 : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.uniformContinuous_of_tendsto_cocompact`：Continuous.uniformCon
tinuous_of_tendsto_cocompact {f : α -> β} {x : β} (h_cont : Continuous f) (hx : 
Tendsto f (cocompact α) (𝓝 x)) : Unifor…
· 使用定理 `HasCompactMulSupport.is_one_at_infty`：is_one_at_infty {f : α -> γ} [Topo
logicalSpace γ] (h : HasCompactMulSupport f) : Tendsto f (cocompact α) (𝓝 1)
-/
theorem HasCompactMulSupport.uniformContinuous_of_continuous {f : α → β} [One β]
    (h1 : HasCompactMulSupport f) (h2 : Continuous f) : UniformContinuous f :=
  h2.uniformContinuous_of_tendsto_cocompact h1.is_one_at_infty

/-- A family of functions `α → β → γ` tends uniformly to its value at `x` if `α` is locally compact,
`β` is compact and `f` is continuous on `U × (univ : Set β)` for some neighborhood `U` of `x`. -/
/-
**ContinuousOn.tendstoUniformly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.tendstoUniformly [LocallyCompactSpace α] [CompactSpace β] [Un
iformSpace γ] {f : α -> β -> γ} {x : α} {U : Set α} (hxU : U in 𝓝 x) (h : Contin
uousOn ↿f (U ×ˢ univ)) : TendstoUniformly f (f x) (𝓝 x)
参数：hxU : U in 𝓝 x；h : ContinuousOn ↿f (U ×ˢ univ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyCompactSpace.local_compact_nhds`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : LocallyCompactSpace X] (x : X),   ∀ n ∈ nhds x, ∃ s ∈ nhds 
x, s ⊆ n ∧ IsCompact s
· 使用定理 `IsCompact.uniformContinuousOn_of_continuous`：IsCompact.uniformContinuous
On_of_continuous {s : Set α} {f : α -> β} (hs : IsCompact s) (hf : ContinuousOn 
f s) : UniformContinuousOn f s
· 使用定理 `IsCompact.prod`：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCo
mpact t) : IsCompact (s ×ˢ t)
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `UniformContinuousOn.tendstoUniformly`：UniformContinuousOn.tendstoUniform
ly [UniformSpace α] [UniformSpace γ] {U : Set α} (hU : U in 𝓝 x) {F : α -> β -> 
γ} (hF : UniformContinuous…

--- 原说明 ---
A family of functions `α → β → γ` tends uniformly to its value at `x` if `α` is 
locally compact,
`β` is compact and `f` is continuous on `U × (univ : Set β)` for some neighborho
od `U` of `x`.
-/
theorem ContinuousOn.tendstoUniformly [LocallyCompactSpace α] [CompactSpace β] [UniformSpace γ]
    {f : α → β → γ} {x : α} {U : Set α} (hxU : U ∈ 𝓝 x) (h : ContinuousOn ↿f (U ×ˢ univ)) :
    TendstoUniformly f (f x) (𝓝 x) := by
  rcases LocallyCompactSpace.local_compact_nhds _ _ hxU with ⟨K, hxK, hKU, hK⟩
  have : UniformContinuousOn ↿f (K ×ˢ univ) :=
    IsCompact.uniformContinuousOn_of_continuous (hK.prod isCompact_univ)
      (h.mono <| prod_mono hKU Subset.rfl)
  exact this.tendstoUniformly hxK

/-- A continuous family of functions `α → β → γ` tends uniformly to its value at `x`
if `α` is weakly locally compact and `β` is compact. -/
/-
**Continuous.tendstoUniformly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.tendstoUniformly [WeaklyLocallyCompactSpace α] [CompactSpace β]
 [UniformSpace γ] (f : α -> β -> γ) (h : Continuous ↿f) (x : α) : TendstoUniform
ly f (f x) (𝓝 x)
参数：f : α -> β -> γ；h : Continuous ↿f；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `IsCompact.uniformContinuousOn_of_continuous`：IsCompact.uniformContinuous
On_of_continuous {s : Set α} {f : α -> β} (hs : IsCompact s) (hf : ContinuousOn 
f s) : UniformContinuousOn f s
· 使用定理 `IsCompact.prod`：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCo
mpact t) : IsCompact (s ×ˢ t)
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `UniformContinuousOn.tendstoUniformly`：UniformContinuousOn.tendstoUniform
ly [UniformSpace α] [UniformSpace γ] {U : Set α} (hU : U in 𝓝 x) {F : α -> β -> 
γ} (hF : UniformContinuous…

--- 原说明 ---
A continuous family of functions `α → β → γ` tends uniformly to its value at `x`
if `α` is weakly locally compact and `β` is compact.
-/
theorem Continuous.tendstoUniformly [WeaklyLocallyCompactSpace α] [CompactSpace β] [UniformSpace γ]
    (f : α → β → γ) (h : Continuous ↿f) (x : α) : TendstoUniformly f (f x) (𝓝 x) :=
  let ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  have : UniformContinuousOn ↿f (K ×ˢ univ) :=
    IsCompact.uniformContinuousOn_of_continuous (hK.prod isCompact_univ) h.continuousOn
  this.tendstoUniformly hxK

/-- In a product space `α × β`, assume that a function `f` is continuous on `s × k` where `k` is
compact. Then, along the fiber above any `q ∈ s`, `f` is transversely uniformly continuous, i.e.,
if `p ∈ s` is close enough to `q`, then `f p x` is uniformly close to `f q x` for all `x ∈ k`. -/
/-
**IsCompact.mem_uniformity_of_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.mem_uniformity_of_prod {α β E : Type*} [TopologicalSpace α] [Top
ologicalSpace β] [UniformSpace E] {f : α -> β -> E} {s : Set α} {k : Set β} {q :
 α} {u : Set (E × E)} (hk : IsCompact k) (hf : ContinuousOn f.uncurry (s ×ˢ k)) 
(hq : q in s) (hu : u in 𝓤 E) : exists v in 𝓝[s] q, forall p in v, forall x in k
, (f p x, f q x) in u
参数：E × E；hk : IsCompact k；hf : ContinuousOn f.uncurry (s ×ˢ k)；hq : q in s；hu : 
u in 𝓤 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.induction_on`：IsCompact.induction_on (hs : IsCompact s) {p : S
et X -> Prop} (he : p ∅) (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hun
ion : forall…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `comp_symm_of_uniformity`：comp_symm_of_uniformity {s : SetRel α α} (hs : 
s in 𝓤 α) : exists t in 𝓤 α, (forall {a b}, (a, b) in t -> (b, a) in t) ∧ t ○ t 
subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin_prod_iff`：mem_nhdsWithin_prod_iff {x : X} {y : Y} {s : Se
t (X × Y)} {tx : Set X} {ty : Set Y} : s in 𝓝[tx ×ˢ ty] (x, y) ↔ exists u in 𝓝[t
x] x, exists …
· 使用定理 `mem_nhds_left`：mem_nhds_left (x : α) {s : SetRel α α} (h : s in 𝓤 α) : {
 y : α | (x, y) in s } in 𝓝 x
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用引理 `SetRel.prodMk_mem_comp`：prodMk_mem_comp (hab : a ~[R] b) (hbc : b ~[S] c
) : a ~[R ○ S] c

--- 原说明 ---
In a product space `α × β`, assume that a function `f` is continuous on `s × k` 
where `k` is
compact. Then, along the fiber above any `q ∈ s`, `f` is transversely uniformly 
continuous, i.e.,
if `p ∈ s` is close enough to `q`, then `f p x` is uniformly close to `f q x` fo
r all `x ∈ k`.
-/
lemma IsCompact.mem_uniformity_of_prod
    {α β E : Type*} [TopologicalSpace α] [TopologicalSpace β] [UniformSpace E]
    {f : α → β → E} {s : Set α} {k : Set β} {q : α} {u : Set (E × E)}
    (hk : IsCompact k) (hf : ContinuousOn f.uncurry (s ×ˢ k)) (hq : q ∈ s) (hu : u ∈ 𝓤 E) :
    ∃ v ∈ 𝓝[s] q, ∀ p ∈ v, ∀ x ∈ k, (f p x, f q x) ∈ u := by
  apply hk.induction_on (p := fun t ↦ ∃ v ∈ 𝓝[s] q, ∀ p ∈ v, ∀ x ∈ t, (f p x, f q x) ∈ u)
  · exact ⟨univ, univ_mem, by simp⟩
  · intro t' t ht't ⟨v, v_mem, hv⟩
    exact ⟨v, v_mem, fun p hp x hx ↦ hv p hp x (ht't hx)⟩
  · intro t t' ⟨v, v_mem, hv⟩ ⟨v', v'_mem, hv'⟩
    refine ⟨v ∩ v', inter_mem v_mem v'_mem, fun p hp x hx ↦ ?_⟩
    rcases hx with h'x | h'x
    · exact hv p hp.1 x h'x
    · exact hv' p hp.2 x h'x
  · rcases comp_symm_of_uniformity hu with ⟨u', u'_mem, u'_symm, hu'⟩
    intro x hx
    obtain ⟨v, hv, w, hw, hvw⟩ :
      ∃ v ∈ 𝓝[s] q, ∃ w ∈ 𝓝[k] x, v ×ˢ w ⊆ f.uncurry ⁻¹' {z | (f q x, z) ∈ u'} :=
        mem_nhdsWithin_prod_iff.1 (hf (q, x) ⟨hq, hx⟩ (mem_nhds_left (f q x) u'_mem))
    refine ⟨w, hw, v, hv, fun p hp y hy ↦ ?_⟩
    have A : (f q x, f p y) ∈ u' := hvw (⟨hp, hy⟩ : (p, y) ∈ v ×ˢ w)
    have B : (f q x, f q y) ∈ u' := hvw (⟨mem_of_mem_nhdsWithin hq hv, hy⟩ : (q, y) ∈ v ×ˢ w)
    exact hu' <| SetRel.prodMk_mem_comp (u'_symm A) B

section UniformConvergence

/-- An equicontinuous family of functions defined on a compact uniform space is automatically
uniformly equicontinuous. -/
/-
**CompactSpace.uniformEquicontinuous_of_equicontinuous** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：CompactSpace.uniformEquicontinuous_of_equicontinuous {ι : Type*} {F : ι ->
 β -> α} [CompactSpace β] (h : Equicontinuous F) : UniformEquicontinuous F
参数：h : Equicontinuous F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformEquicontinuous_iff_uniformContinuous`：uniformEquicontinuous_iff_u
niformContinuous {F : ι -> β -> α} : UniformEquicontinuous F ↔ UniformContinuous
 (ofFun ∘ Function.swap F : β -> …
· 使用定理 `CompactSpace.uniformContinuous_of_continuous`：CompactSpace.uniformContin
uous_of_continuous [CompactSpace α] {f : α -> β} (h : Continuous f) : UniformCon
tinuous f
· 使用定理 `equicontinuous_iff_continuous`：equicontinuous_iff_continuous {F : ι -> X
 -> α} : Equicontinuous F ↔ Continuous (ofFun ∘ Function.swap F : X -> ι ->ᵤ α)

--- 原说明 ---
An equicontinuous family of functions defined on a compact uniform space is auto
matically
uniformly equicontinuous.
-/
theorem CompactSpace.uniformEquicontinuous_of_equicontinuous {ι : Type*} {F : ι → β → α}
    [CompactSpace β] (h : Equicontinuous F) : UniformEquicontinuous F := by
  rw [equicontinuous_iff_continuous] at h
  rw [uniformEquicontinuous_iff_uniformContinuous]
  exact CompactSpace.uniformContinuous_of_continuous h

end UniformConvergence

