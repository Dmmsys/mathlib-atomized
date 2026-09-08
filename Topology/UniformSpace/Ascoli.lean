/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.UniformSpace.Equicontinuity
public import Mathlib.Topology.UniformSpace.Equiv

/-!
# Ascoli Theorem

In this file, we prove the general **Arzela-Ascoli theorem**, and various related statements about
the topology of equicontinuous subsets of `X →ᵤ[𝔖] α`, where `X` is a topological space, `𝔖` is
a family of compact subsets of `X`, and `α` is a uniform space.

## Main statements

* If `X` is a compact space, then the uniform structures of uniform convergence and pointwise
  convergence coincide on equicontinuous subsets. This is the key fact that makes equicontinuity
  important in functional analysis. We state various versions of it:
  - as an equality of `UniformSpace`s: `Equicontinuous.comap_uniformFun_eq`
  - in terms of `IsUniformInducing`: `Equicontinuous.isUniformInducing_uniformFun_iff_pi`
  - in terms of `IsInducing`: `Equicontinuous.inducing_uniformFun_iff_pi`
  - in terms of convergence along a filter: `Equicontinuous.tendsto_uniformFun_iff_pi`
* As a consequence, if `𝔖` is a family of compact subsets of `X`, then the uniform structures of
  uniform convergence on `𝔖` and pointwise convergence on `⋃₀ 𝔖` coincide on equicontinuous
  subsets. Again, we prove multiple variations:
  - as an equality of `UniformSpace`s: `EquicontinuousOn.comap_uniformOnFun_eq`
  - in terms of `IsUniformInducing`: `EquicontinuousOn.isUniformInducing_uniformOnFun_iff_pi'`
  - in terms of `IsInducing`: `EquicontinuousOn.inducing_uniformOnFun_iff_pi'`
  - in terms of convergence along a filter: `EquicontinuousOn.tendsto_uniformOnFun_iff_pi'`
* The **Arzela-Ascoli theorem** follows from the previous fact and Tykhonov's theorem.
  All of its variations can be found under the `ArzelaAscoli` namespace.

## Implementation details

* The statements in this file may be a bit daunting because we prove everything for families and
  embeddings instead of subspaces with the subspace topology. This is done because, in practice,
  one would rarely work with `X →ᵤ[𝔖] α` directly, so we need to provide API for bringing back the
  statements to various other types, such as `C(X, Y)` or `E →L[𝕜] F`. To counteract this, all
  statements (as well as most proofs!) are documented quite thoroughly.

* A lot of statements assume `∀ K ∈ 𝔖, EquicontinuousOn F K` instead of the more natural
  `EquicontinuousOn F (⋃₀ 𝔖)`. This is in order to keep the most generality, as the first statement
  is strictly weaker.

* In Bourbaki, the usual Arzela-Ascoli compactness theorem follows from a similar total boundedness
  result. Here we go directly for the compactness result, which is the most useful in practice, but
  this will be an easy addition/refactor if we ever need it.

## TODO

* Prove that, on an equicontinuous family, pointwise convergence and pointwise convergence on a
  dense subset coincide, and deduce metrizability criteria for equicontinuous subsets.

* Prove the total boundedness version of the theorem

* Prove the converse statement: if a subset of `X →ᵤ[𝔖] α` is compact, then it is equicontinuous
  on each `K ∈ 𝔖`.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]

## Tags

equicontinuity, uniform convergence, ascoli
-/

public section

open Set Filter Uniformity Topology Function UniformConvergence

variable {ι X α : Type*} [TopologicalSpace X] [UniformSpace α] {F : ι → X → α}

/-- Let `X` be a compact topological space, `α` a uniform space, and `F : ι → (X → α)` an
equicontinuous family. Then, the uniform structures of uniform convergence and pointwise
convergence induce the same uniform structure on `ι`.

In other words, pointwise convergence and uniform convergence coincide on an equicontinuous
subset of `X → α`.

Consider using `Equicontinuous.isUniformInducing_uniformFun_iff_pi` and
`Equicontinuous.inducing_uniformFun_iff_pi` instead, to avoid rewriting instances. -/
/-
**Equicontinuous.comap_uniformFun_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equicontinuous.comap_uniformFun_eq [CompactSpace X] (F_eqcont : Equicontin
uous F) : (UniformFun.uniformSpace X α).comap F = (Pi.uniformSpace _).comap F
参数：F_eqcont : Equicontinuous F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `UniformSpace.comap_mono`：UniformSpace.comap_mono {α γ} {f : α -> γ} : Mo
notone fun u : UniformSpace γ => u.comap f
· 使用定理 `UniformFun.uniformContinuous_toFun`：∀ {α : Type u_1} {β : Type u_2} [ins
t : UniformSpace β], UniformContinuous ⇑UniformFun.toFun
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.uniformity`：Pi.uniformity : 𝓤 (forall i, α i) = ⨅ i : ι, (Filter.coma
p fun a => (a.1 i, a.2 i)) (𝓤 (α i))
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `UniformFun.hasBasis_uniformity`：∀ (α : Type u_1) (β : Type u_2) [inst : 
UniformSpace β],   (uniformity (UniformFun α β)).HasBasis (fun x => x ∈ uniformi
ty β) (UniformFun.ge…
· 使用定理 `comp_comp_symm_mem_uniformity_sets`：comp_comp_symm_mem_uniformity_sets {
s : SetRel α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t ○ t s
ubseteq s
· 使用定理 `CompactSpace.elim_nhds_subcover`：CompactSpace.elim_nhds_subcover [Compac
tSpace X] (U : X -> Set X) (hU : forall x, U x in 𝓝 x) : exists t : Finset X, ⋃ 
x in t, U x = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用引理 `SetRel.prodMk_mem_comp`：prodMk_mem_comp (hab : a ~[R] b) (hbc : b ~[S] c
) : a ~[R ○ S] c
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Finset.iInter_mem_sets`：∀ {α : Type u} {f : Filter α} {β : Type v} {s : 
β → Set α} (is : Finset β), ⋂ i ∈ is, s i ∈ f ↔ ∀ i ∈ is, s i ∈ f
· 使用定理 `Filter.mem_iInf_of_mem`：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} 
(hs : s in f i) : s in ⨅ i, f i
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g

--- 原说明 ---
Let `X` be a compact topological space, `α` a uniform space, and `F : ι → (X → α
)` an
equicontinuous family. Then, the uniform structures of uniform convergence and p
ointwise
convergence induce the same uniform structure on `ι`.

In other words, pointwise convergence and uniform convergence coincide on an equ
icontinuous
subset of `X → α`.

Consider using `Equicontinuous.isUniformInducing_uniformFun_iff_pi` and
`Equicontinuous.inducing_uniformFun_iff_pi` instead, to avoid rewriting instance
s.
-/
theorem Equicontinuous.comap_uniformFun_eq [CompactSpace X] (F_eqcont : Equicontinuous F) :
    (UniformFun.uniformSpace X α).comap F =
    (Pi.uniformSpace _).comap F := by
  -- The `≤` inequality is trivial
  refine le_antisymm (UniformSpace.comap_mono UniformFun.uniformContinuous_toFun) ?_
  -- A bit of rewriting to get a nice intermediate statement.
  simp_rw [UniformSpace.comap, UniformSpace.le_def, uniformity_comap, Pi.uniformity,
    Filter.comap_iInf, comap_comap, Function.comp_def]
  refine ((UniformFun.hasBasis_uniformity X α).comap (Prod.map F F)).ge_iff.mpr ?_
  -- Core of the proof: we need to show that, for any entourage `U` in `α`,
  -- the set `𝐓(U) := {(i,j) : ι × ι | ∀ x : X, (F i x, F j x) ∈ U}` belongs to the filter
  -- `⨅ x, comap ((i,j) ↦ (F i x, F j x)) (𝓤 α)`.
  -- In other words, we have to show that it contains a finite intersection of
  -- sets of the form `𝐒(V, x) := {(i,j) : ι × ι | (F i x, F j x) ∈ V}` for some
  -- `x : X` and `V ∈ 𝓤 α`.
  intro U hU
  -- We will do an `ε/3` argument, so we start by choosing a symmetric entourage `V ∈ 𝓤 α`
  -- such that `V ○ V ○ V ⊆ U`.
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, Vsymm, hVU⟩
  -- Set `Ω x := {y | ∀ i, (F i x, F i y) ∈ V}`. The equicontinuity of `F` guarantees that
  -- each `Ω x` is a neighborhood of `x`.
  let Ω x : Set X := {y | ∀ i, (F i x, F i y) ∈ V}
  -- Hence, by compactness of `X`, we can find some `A ⊆ X` finite such that the `Ω a`s for `a ∈ A`
  -- still cover `X`.
  rcases CompactSpace.elim_nhds_subcover Ω (fun x ↦ F_eqcont x V hV) with ⟨A, Acover⟩
  -- We now claim that `⋂ a ∈ A, 𝐒(V, a) ⊆ 𝐓(U)`.
  have : (⋂ a ∈ A, {ij : ι × ι | (F ij.1 a, F ij.2 a) ∈ V}) ⊆
      (Prod.map F F) ⁻¹' UniformFun.gen X α U := by
    -- Given `(i, j) ∈ ⋂ a ∈ A, 𝐒(V, a)` and `x : X`, we have to prove that `(F i x, F j x) ∈ U`.
    rintro ⟨i, j⟩ hij x
    rw [mem_iInter₂] at hij
    -- We know that `x ∈ Ω a` for some `a ∈ A`, so that both `(F i x, F i a)` and `(F j a, F j x)`
    -- are in `V`.
    rcases mem_iUnion₂.mp (Acover.symm.subset <| mem_univ x) with ⟨a, ha, hax⟩
    -- Since `(i, j) ∈ 𝐒(V, a)` we also have `(F i a, F j a) ∈ V`, and finally we get
    -- `(F i x, F j x) ∈ V ○ V ○ V ⊆ U`.
    exact hVU <| SetRel.prodMk_mem_comp (SetRel.prodMk_mem_comp (SetRel.symm V <| hax i) (hij a ha))
      (hax j)
  -- This completes the proof.
  exact mem_of_superset
    (A.iInter_mem_sets.mpr fun x _ ↦ mem_iInf_of_mem x <| preimage_mem_comap hV) this

/-- Let `X` be a compact topological space, `α` a uniform space, and `F : ι → (X → α)` an
equicontinuous family. Then, the uniform structures of uniform convergence and pointwise
convergence induce the same uniform structure on `ι`.

In other words, pointwise convergence and uniform convergence coincide on an equicontinuous
subset of `X → α`.

This is a version of `Equicontinuous.comap_uniformFun_eq` stated in terms of `IsUniformInducing`
for convenience. -/
/-
**Equicontinuous.isUniformInducing_uniformFun_iff_pi** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：Equicontinuous.isUniformInducing_uniformFun_iff_pi [UniformSpace ι] [Compa
ctSpace X] (F_eqcont : Equicontinuous F) : IsUniformInducing (UniformFun.ofFun ∘
 F) ↔ IsUniformInducing F
参数：F_eqcont : Equicontinuous F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isUniformInducing_iff_uniformSpace`：isUniformInducing_iff_uniformSpace {
f : α -> β} : IsUniformInducing f ↔ ‹UniformSpace β›.comap f = ‹UniformSpace α›
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equicontinuous.comap_uniformFun_eq`：Equicontinuous.comap_uniformFun_eq [
CompactSpace X] (F_eqcont : Equicontinuous F) : (UniformFun.uniformSpace X α).co
map F = (Pi.uniformSpace…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Let `X` be a compact topological space, `α` a uniform space, and `F : ι → (X → α
)` an
equicontinuous family. Then, the uniform structures of uniform convergence and p
ointwise
convergence induce the same uniform structure on `ι`.

In other words, pointwise convergence and uniform convergence coincide on an equ
icontinuous
subset of `X → α`.

This is a version of `Equicontinuous.comap_uniformFun_eq` stated in terms of `Is
UniformInducing`
for convenience.
-/
lemma Equicontinuous.isUniformInducing_uniformFun_iff_pi [UniformSpace ι] [CompactSpace X]
    (F_eqcont : Equicontinuous F) :
    IsUniformInducing (UniformFun.ofFun ∘ F) ↔ IsUniformInducing F := by
  rw [isUniformInducing_iff_uniformSpace, isUniformInducing_iff_uniformSpace,
      ← F_eqcont.comap_uniformFun_eq]
  rfl

/-- Let `X` be a compact topological space, `α` a uniform space, and `F : ι → (X → α)` an
equicontinuous family. Then, the topologies of uniform convergence and pointwise convergence induce
the same topology on `ι`.

In other words, pointwise convergence and uniform convergence coincide on an equicontinuous
subset of `X → α`.

This is a consequence of `Equicontinuous.comap_uniformFun_eq`, stated in terms of `IsInducing`
for convenience. -/
/-
**Equicontinuous.inducing_uniformFun_iff_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Equicontinuous.inducing_uniformFun_iff_pi [TopologicalSpace ι] [CompactSpa
ce X] (F_eqcont : Equicontinuous F) : IsInducing (UniformFun.ofFun ∘ F) ↔ IsIndu
cing F
参数：F_eqcont : Equicontinuous F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.isInducing_iff`：∀ {X : Type u_1} {Y : Type u_2} [tX : Topologic
alSpace X] [tY : TopologicalSpace Y] (f : X → Y),   Topology.IsInducing f ↔ tX =
 TopologicalS…
· 使用定理 `Equicontinuous.comap_uniformFun_eq`：Equicontinuous.comap_uniformFun_eq [
CompactSpace X] (F_eqcont : Equicontinuous F) : (UniformFun.uniformSpace X α).co
map F = (Pi.uniformSpace…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Let `X` be a compact topological space, `α` a uniform space, and `F : ι → (X → α
)` an
equicontinuous family. Then, the topologies of uniform convergence and pointwise
 convergence induce
the same topology on `ι`.

In other words, pointwise convergence and uniform convergence coincide on an equ
icontinuous
subset of `X → α`.

This is a consequence of `Equicontinuous.comap_uniformFun_eq`, stated in terms o
f `IsInducing`
for convenience.
-/
lemma Equicontinuous.inducing_uniformFun_iff_pi [TopologicalSpace ι] [CompactSpace X]
    (F_eqcont : Equicontinuous F) :
    IsInducing (UniformFun.ofFun ∘ F) ↔ IsInducing F := by
  rw [isInducing_iff, isInducing_iff]
  change (_ = (UniformFun.uniformSpace X α |>.comap F |>.toTopologicalSpace)) ↔
         (_ = (Pi.uniformSpace _ |>.comap F |>.toTopologicalSpace))
  rw [F_eqcont.comap_uniformFun_eq]

/-- Let `X` be a compact topological space, `α` a uniform space, `F : ι → (X → α)` an
equicontinuous family, and `ℱ` a filter on `ι`. Then, `F` tends *uniformly* to `f : X → α` along
`ℱ` iff it tends to `f` *pointwise* along `ℱ`. -/
/-
**Equicontinuous.tendsto_uniformFun_iff_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equicontinuous.tendsto_uniformFun_iff_pi [CompactSpace X] (F_eqcont : Equi
continuous F) (ℱ : Filter ι) (f : X -> α) : Tendsto (UniformFun.ofFun ∘ F) ℱ (𝓝 
<| UniformFun.ofFun f) ↔ Tendsto F ℱ (𝓝 f)
参数：F_eqcont : Equicontinuous F；ℱ : Filter ι；f : X -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `UniformFun.uniformContinuous_toFun`：∀ {α : Type u_1} {β : Type u_2} [ins
t : UniformSpace β], UniformContinuous ⇑UniformFun.toFun
· 使用定理 `Equicontinuous.closure'`：Equicontinuous.closure' {A : Set Y} {u : Y -> X
 -> α} (hA : Equicontinuous (u ∘ (↑) : A -> X -> α)) (hu : Continuous u) : Equic
ontinuous (u …
· 使用定理 `equicontinuous_iff_range`：equicontinuous_iff_range {F : ι -> X -> α} : E
quicontinuous F ↔ Equicontinuous ((↑) : range F -> X -> α)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Equicontinuous.inducing_uniformFun_iff_pi`：Equicontinuous.inducing_unifo
rmFun_iff_pi [TopologicalSpace ι] [CompactSpace X] (F_eqcont : Equicontinuous F)
 : IsInducing (UniformFun.ofFun…
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
· 使用定理 `Filter.range_mem_map`：range_mem_map : range m in map m f
· 使用定理 `Filter.map_comap_of_mem`：map_comap_of_mem {f : Filter β} {m : α -> β} (h
f : range m in f) : (f.comap m).map m = f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Filter.tendsto_id'`：tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x <=
 y
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
· 使用引理 `Topology.IsInducing.tendsto_nhds_iff`：tendsto_nhds_iff {f : ι -> Y} {l :
 Filter ι} {y : Y} (hg : IsInducing g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (
𝓝 (g y))

--- 原说明 ---
Let `X` be a compact topological space, `α` a uniform space, `F : ι → (X → α)` a
n
equicontinuous family, and `ℱ` a filter on `ι`. Then, `F` tends *uniformly* to `
f : X → α` along
`ℱ` iff it tends to `f` *pointwise* along `ℱ`.
-/
theorem Equicontinuous.tendsto_uniformFun_iff_pi [CompactSpace X]
    (F_eqcont : Equicontinuous F) (ℱ : Filter ι) (f : X → α) :
    Tendsto (UniformFun.ofFun ∘ F) ℱ (𝓝 <| UniformFun.ofFun f) ↔
    Tendsto F ℱ (𝓝 f) := by
  -- Assume `ℱ` is non-trivial.
  rcases ℱ.eq_or_neBot with rfl | ℱ_ne
  · simp
  constructor <;> intro H
  -- The forward direction is always true, the interesting part is the converse.
  · exact UniformFun.uniformContinuous_toFun.continuous.tendsto _ |>.comp H
  -- To prove it, assume that `F` tends to `f` *pointwise* along `ℱ`.
  · set S : Set (X → α) := closure (range F)
    set 𝒢 : Filter S := comap (↑) (map F ℱ)
    -- We would like to use `Equicontinuous.comap_uniformFun_eq`, but applying it to `F` is not
    -- enough since `f` has no reason to be in the range of `F`.
    -- Instead, we will apply it to the inclusion `(↑) : S → (X → α)` where `S` is the closure of
    -- the range of `F` *for the product topology*.
    -- We know that `S` is still equicontinuous...
    have hS : S.Equicontinuous := closure' (by rwa [equicontinuous_iff_range] at F_eqcont)
      continuous_id
    -- ... hence, as announced, the product topology and uniform convergence topology
    -- coincide on `S`.
    have ind : IsInducing (UniformFun.ofFun ∘ (↑) : S → X →ᵤ α) :=
      hS.inducing_uniformFun_iff_pi.mpr ⟨rfl⟩
    -- By construction, `f` is in `S`.
    have f_mem : f ∈ S := mem_closure_of_tendsto H range_mem_map
    -- To conclude, we just have to translate our hypothesis and goal as statements about
    -- `S`, on which we know the two topologies at play coincide.
    -- For this, we define a filter on `S` by `𝒢 := comap (↑) (map F ℱ)`, and note that
    -- it satisfies `map (↑) 𝒢 = map F ℱ`. Thus, both our hypothesis and our goal
    -- can be rewritten as `𝒢 ≤ 𝓝 f`, where the neighborhood filter in the RHS corresponds
    -- to one of the two topologies at play on `S`. Since they coincide, we are done.
    have h𝒢ℱ : map (↑) 𝒢 = map F ℱ := Filter.map_comap_of_mem
      (Subtype.range_coe ▸ mem_of_superset range_mem_map subset_closure)
    have H' : Tendsto id 𝒢 (𝓝 ⟨f, f_mem⟩) := by
      rwa [tendsto_id', nhds_induced, ← map_le_iff_le_comap, h𝒢ℱ]
    rwa [ind.tendsto_nhds_iff, comp_id, ← tendsto_map'_iff, h𝒢ℱ] at H'

set_option backward.isDefEq.respectTransparency false in
/-- Let `X` be a topological space, `𝔖` a family of compact subsets of `X`, `α` a uniform space,
and `F : ι → (X → α)` a family which is equicontinuous on each `K ∈ 𝔖`. Then, the uniform
structures of uniform convergence on `𝔖` and pointwise convergence on `⋃₀ 𝔖` induce the same
uniform structure on `ι`.

In particular, pointwise convergence and compact convergence coincide on an equicontinuous
subset of `X → α`.

Consider using `EquicontinuousOn.isUniformInducing_uniformOnFun_iff_pi'` and
`EquicontinuousOn.inducing_uniformOnFun_iff_pi'` instead to avoid rewriting instances,
as well as their unprimed versions in case `𝔖` covers `X`. -/
/-
**EquicontinuousOn.comap_uniformOnFun_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EquicontinuousOn.comap_uniformOnFun_eq {𝔖 : Set (Set X)} (𝔖_compact : fora
ll K in 𝔖, IsCompact K) (F_eqcont : forall K in 𝔖, EquicontinuousOn F K) : (Unif
ormOnFun.uniformSpace X α 𝔖).comap F = (Pi.uniformSpace _).comap ((⋃₀ 𝔖).domRest
rict ∘ F)
参数：Set X；𝔖_compact : forall K in 𝔖, IsCompact K；F_eqcont : forall K in 𝔖, Equico
ntinuousOn F K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UniformSpace.comap_iInf`：UniformSpace.comap_iInf {ι α γ} {u : ι -> Unifo
rmSpace γ} {f : α -> γ} : (⨅ i, u i).comap f = ⨅ i, (u i).comap f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `UniformSpace.comap_comap`：UniformSpace.comap_comap {α β γ} {uγ : Uniform
Space γ} {f : α -> β} {g : β -> γ} : UniformSpace.comap (g ∘ f) uγ = UniformSpac
e.comap f (Uni…
· 使用引理 `Pi.uniformSpace_comap_restrict_sUnion`：Pi.uniformSpace_comap_restrict_sU
nion (𝔖 : Set (Set ι)) : UniformSpace.comap (⋃₀ 𝔖).domRestrict (Pi.uniformSpace 
(fun i : (⋃₀ 𝔖) => α i)) = …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `Equicontinuous.comap_uniformFun_eq`：Equicontinuous.comap_uniformFun_eq [
CompactSpace X] (F_eqcont : Equicontinuous F) : (UniformFun.uniformSpace X α).co
map F = (Pi.uniformSpace…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `equicontinuous_restrict_iff`：equicontinuous_restrict_iff (F : ι -> X -> 
α) {S : Set X} : Equicontinuous (S.domRestrict ∘ F) ↔ EquicontinuousOn F S
· 使用定理 `iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f g : ι →
 α}, (∀ (i : ι), f i = g i) → ⨅ i, f i = ⨅ i, g i

--- 原说明 ---
Let `X` be a topological space, `𝔖` a family of compact subsets of `X`, `α` a un
iform space,
and `F : ι → (X → α)` a family which is equicontinuous on each `K ∈ 𝔖`. Then, th
e uniform
structures of uniform convergence on `𝔖` and pointwise convergence on `⋃₀ 𝔖` ind
uce the same
uniform structure on `ι`.

In particular, pointwise convergence and compact convergence coincide on an equi
continuous
subset of `X → α`.

Consider using `EquicontinuousOn.isUniformInducing_uniformOnFun_iff_pi'` and
`EquicontinuousOn.inducing_uniformOnFun_iff_pi'` instead to avoid rewriting inst
ances,
as well as their unprimed versions in case `𝔖` covers `X`.
-/
theorem EquicontinuousOn.comap_uniformOnFun_eq {𝔖 : Set (Set X)} (𝔖_compact : ∀ K ∈ 𝔖, IsCompact K)
    (F_eqcont : ∀ K ∈ 𝔖, EquicontinuousOn F K) :
    (UniformOnFun.uniformSpace X α 𝔖).comap F =
    (Pi.uniformSpace _).comap ((⋃₀ 𝔖).domRestrict ∘ F) := by
  -- Recall that the uniform structure on `X →ᵤ[𝔖] α` is the one induced by all the maps
  -- `K.domRestrict : (X →ᵤ[𝔖] α) → (K →ᵤ α)` for `K ∈ 𝔖`. Its pullback along `F`, which is
  -- the LHS of our goal, is thus the uniform structure induced by the maps
  -- `K.domRestrict ∘ F : ι → (K →ᵤ α)` for `K ∈ 𝔖`.
  have H1 : (UniformOnFun.uniformSpace X α 𝔖).comap F =
      ⨅ (K ∈ 𝔖), (UniformFun.uniformSpace _ _).comap (K.domRestrict ∘ F) := by
    simp_rw [UniformOnFun.uniformSpace, UniformSpace.comap_iInf, ← UniformSpace.comap_comap,
      UniformFun.ofFun, Equiv.coe_fn_mk, UniformOnFun.toFun, UniformOnFun.ofFun, Function.comp_def,
      UniformFun, Equiv.coe_fn_symm_mk]
  -- Now, note that a similar fact is true for the uniform structure on `X → α` induced by
  -- the map `(⋃₀ 𝔖).domRestrict : (X → α) → ((⋃₀ 𝔖) → α)`: it is equal to the one induced by
  -- all maps `K.domRestrict : (X → α) → (K → α)` for `K ∈ 𝔖`, which means that the RHS of our
  -- goal is the uniform structure induced by the maps `K.domRestrict ∘ F : ι → (K → α)`
  -- for `K ∈ 𝔖`.
  have H2 : (Pi.uniformSpace _).comap ((⋃₀ 𝔖).domRestrict ∘ F) =
      ⨅ (K ∈ 𝔖), (Pi.uniformSpace _).comap (K.domRestrict ∘ F) := by
    simp_rw [UniformSpace.comap_comap, Pi.uniformSpace_comap_restrict_sUnion (fun _ ↦ α) 𝔖,
      UniformSpace.comap_iInf]
  -- But, for `K ∈ 𝔖` fixed, we know that the uniform structures of `K →ᵤ α` and `K → α`
  -- induce, via the equicontinuous family `K.domRestrict ∘ F`, the same uniform structure on `ι`.
  have H3 : ∀ K ∈ 𝔖, (UniformFun.uniformSpace K α).comap (K.domRestrict ∘ F) =
      (Pi.uniformSpace _).comap (K.domRestrict ∘ F) := fun K hK ↦ by
    have : CompactSpace K := isCompact_iff_compactSpace.mp (𝔖_compact K hK)
    exact (equicontinuous_restrict_iff _ |>.mpr <| F_eqcont K hK).comap_uniformFun_eq
  -- Combining these three facts completes the proof.
  simp_rw [H1, H2, iInf_congr fun K ↦ iInf_congr fun hK ↦ H3 K hK]

/-- Let `X` be a topological space, `𝔖` a family of compact subsets of `X`, `α` a uniform space,
and `F : ι → (X → α)` a family which is equicontinuous on each `K ∈ 𝔖`. Then, the uniform
structures of uniform convergence on `𝔖` and pointwise convergence on `⋃₀ 𝔖` induce the same
uniform structure on `ι`.

In particular, pointwise convergence and compact convergence coincide on an equicontinuous
subset of `X → α`.

This is a version of `EquicontinuousOn.comap_uniformOnFun_eq` stated in terms of `IsUniformInducing`
for convenience. -/
/-
**EquicontinuousOn.isUniformInducing_uniformOnFun_iff_pi'** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：EquicontinuousOn.isUniformInducing_uniformOnFun_iff_pi' [UniformSpace ι] {
𝔖 : Set (Set X)} (𝔖_compact : forall K in 𝔖, IsCompact K) (F_eqcont : forall K i
n 𝔖, EquicontinuousOn F K) : IsUniformInducing (UniformOnFun.ofFun 𝔖 ∘ F) ↔ IsUn
iformInducing ((⋃₀ 𝔖).domRestrict ∘ F)
参数：Set X；𝔖_compact : forall K in 𝔖, IsCompact K；F_eqcont : forall K in 𝔖, Equico
ntinuousOn F K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isUniformInducing_iff_uniformSpace`：isUniformInducing_iff_uniformSpace {
f : α -> β} : IsUniformInducing f ↔ ‹UniformSpace β›.comap f = ‹UniformSpace α›
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EquicontinuousOn.comap_uniformOnFun_eq`：EquicontinuousOn.comap_uniformOn
Fun_eq {𝔖 : Set (Set X)} (𝔖_compact : forall K in 𝔖, IsCompact K) (F_eqcont : fo
rall K in 𝔖, EquicontinuousO…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Let `X` be a topological space, `𝔖` a family of compact subsets of `X`, `α` a un
iform space,
and `F : ι → (X → α)` a family which is equicontinuous on each `K ∈ 𝔖`. Then, th
e uniform
structures of uniform convergence on `𝔖` and pointwise convergence on `⋃₀ 𝔖` ind
uce the same
uniform structure on `ι`.

In particular, pointwise convergence and compact convergence coincide on an equi
continuous
subset of `X → α`.

This is a version of `EquicontinuousOn.comap_uniformOnFun_eq` stated in terms of
 `IsUniformInducing`
for convenience.
-/
lemma EquicontinuousOn.isUniformInducing_uniformOnFun_iff_pi' [UniformSpace ι]
    {𝔖 : Set (Set X)} (𝔖_compact : ∀ K ∈ 𝔖, IsCompact K)
    (F_eqcont : ∀ K ∈ 𝔖, EquicontinuousOn F K) :
    IsUniformInducing (UniformOnFun.ofFun 𝔖 ∘ F) ↔
    IsUniformInducing ((⋃₀ 𝔖).domRestrict ∘ F) := by
  rw [isUniformInducing_iff_uniformSpace, isUniformInducing_iff_uniformSpace,
      ← EquicontinuousOn.comap_uniformOnFun_eq 𝔖_compact F_eqcont]
  rfl

/-- Let `X` be a topological space, `𝔖` a covering of `X` by compact subsets, `α` a uniform space,
and `F : ι → (X → α)` a family which is equicontinuous on each `K ∈ 𝔖`. Then, the uniform
structures of uniform convergence on `𝔖` and pointwise convergence induce the same
uniform structure on `ι`.

This is a specialization of `EquicontinuousOn.isUniformInducing_uniformOnFun_iff_pi'` to
the case where `𝔖` covers `X`. -/
/-
**EquicontinuousOn.isUniformInducing_uniformOnFun_iff_pi** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：EquicontinuousOn.isUniformInducing_uniformOnFun_iff_pi [UniformSpace ι] {𝔖
 : Set (Set X)} (𝔖_covers : ⋃₀ 𝔖 = univ) (𝔖_compact : forall K in 𝔖, IsCompact K
) (F_eqcont : forall K in 𝔖, EquicontinuousOn F K) : IsUniformInducing (UniformO
nFun.ofFun 𝔖 ∘ F) ↔ IsUniformInducing F
参数：Set X；𝔖_covers : ⋃₀ 𝔖 = univ；𝔖_compact : forall K in 𝔖, IsCompact K；F_eqcont 
: forall K in 𝔖, EquicontinuousOn F K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用引理 `EquicontinuousOn.isUniformInducing_uniformOnFun_iff_pi'`：EquicontinuousO
n.isUniformInducing_uniformOnFun_iff_pi' [UniformSpace ι] {𝔖 : Set (Set X)} (𝔖_c
ompact : forall K in 𝔖, IsCompact K) (F_eqcon…
· 使用定理 `IsUniformInducing.comp`：IsUniformInducing.comp {g : β -> γ} (hg : IsUnif
ormInducing g) {f : α -> β} (hf : IsUniformInducing f) : IsUniformInducing (g ∘ 
f)
· 使用定理 `UniformEquiv.isUniformInducing`：isUniformInducing (h : α ≃ᵤ β) : IsUnifo
rmInducing h

--- 原说明 ---
Let `X` be a topological space, `𝔖` a covering of `X` by compact subsets, `α` a 
uniform space,
and `F : ι → (X → α)` a family which is equicontinuous on each `K ∈ 𝔖`. Then, th
e uniform
structures of uniform convergence on `𝔖` and pointwise convergence induce the sa
me
uniform structure on `ι`.

This is a specialization of `EquicontinuousOn.isUniformInducing_uniformOnFun_iff
_pi'` to
the case where `𝔖` covers `X`.
-/
lemma EquicontinuousOn.isUniformInducing_uniformOnFun_iff_pi [UniformSpace ι]
    {𝔖 : Set (Set X)} (𝔖_covers : ⋃₀ 𝔖 = univ) (𝔖_compact : ∀ K ∈ 𝔖, IsCompact K)
    (F_eqcont : ∀ K ∈ 𝔖, EquicontinuousOn F K) :
    IsUniformInducing (UniformOnFun.ofFun 𝔖 ∘ F) ↔
    IsUniformInducing F := by
  rw [eq_univ_iff_forall] at 𝔖_covers
  -- This obviously follows from the previous lemma, we formalize it by going through the
  -- isomorphism of uniform spaces between `(⋃₀ 𝔖) → α` and `X → α`.
  let φ : ((⋃₀ 𝔖) → α) ≃ᵤ (X → α) := UniformEquiv.piCongrLeft (β := fun _ ↦ α)
    (Equiv.subtypeUnivEquiv 𝔖_covers)
  rw [EquicontinuousOn.isUniformInducing_uniformOnFun_iff_pi' 𝔖_compact F_eqcont,
      show domRestrict (⋃₀ 𝔖) ∘ F = φ.symm ∘ F by rfl]
  exact ⟨fun H ↦ φ.isUniformInducing.comp H, fun H ↦ φ.symm.isUniformInducing.comp H⟩

/-- Let `X` be a topological space, `𝔖` a family of compact subsets of `X`, `α` a uniform space,
and `F : ι → (X → α)` a family which is equicontinuous on each `K ∈ 𝔖`. Then, the topologies
of uniform convergence on `𝔖` and pointwise convergence on `⋃₀ 𝔖` induce the same topology on  `ι`.

In particular, pointwise convergence and compact convergence coincide on an equicontinuous
subset of `X → α`.

This is a consequence of `EquicontinuousOn.comap_uniformOnFun_eq` stated in terms of `IsInducing`
for convenience. -/
/-
**EquicontinuousOn.inducing_uniformOnFun_iff_pi'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：EquicontinuousOn.inducing_uniformOnFun_iff_pi' [TopologicalSpace ι] {𝔖 : S
et (Set X)} (𝔖_compact : forall K in 𝔖, IsCompact K) (F_eqcont : forall K in 𝔖, 
EquicontinuousOn F K) : IsInducing (UniformOnFun.ofFun 𝔖 ∘ F) ↔ IsInducing ((⋃₀ 
𝔖).domRestrict ∘ F)
参数：Set X；𝔖_compact : forall K in 𝔖, IsCompact K；F_eqcont : forall K in 𝔖, Equico
ntinuousOn F K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.isInducing_iff`：∀ {X : Type u_1} {Y : Type u_2} [tX : Topologic
alSpace X] [tY : TopologicalSpace Y] (f : X → Y),   Topology.IsInducing f ↔ tX =
 TopologicalS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EquicontinuousOn.comap_uniformOnFun_eq`：EquicontinuousOn.comap_uniformOn
Fun_eq {𝔖 : Set (Set X)} (𝔖_compact : forall K in 𝔖, IsCompact K) (F_eqcont : fo
rall K in 𝔖, EquicontinuousO…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Let `X` be a topological space, `𝔖` a family of compact subsets of `X`, `α` a un
iform space,
and `F : ι → (X → α)` a family which is equicontinuous on each `K ∈ 𝔖`. Then, th
e topologies
of uniform convergence on `𝔖` and pointwise convergence on `⋃₀ 𝔖` induce the sam
e topology on  `ι`.

In particular, pointwise convergence and compact convergence coincide on an equi
continuous
subset of `X → α`.

This is a consequence of `EquicontinuousOn.comap_uniformOnFun_eq` stated in term
s of `IsInducing`
for convenience.
-/
lemma EquicontinuousOn.inducing_uniformOnFun_iff_pi' [TopologicalSpace ι]
    {𝔖 : Set (Set X)} (𝔖_compact : ∀ K ∈ 𝔖, IsCompact K)
    (F_eqcont : ∀ K ∈ 𝔖, EquicontinuousOn F K) :
    IsInducing (UniformOnFun.ofFun 𝔖 ∘ F) ↔
    IsInducing ((⋃₀ 𝔖).domRestrict ∘ F) := by
  rw [isInducing_iff, isInducing_iff]
  change (_ = ((UniformOnFun.uniformSpace X α 𝔖).comap F).toTopologicalSpace) ↔
    (_ = ((Pi.uniformSpace _).comap ((⋃₀ 𝔖).domRestrict ∘ F)).toTopologicalSpace)
  rw [← EquicontinuousOn.comap_uniformOnFun_eq 𝔖_compact F_eqcont]

/-- Let `X` be a topological space, `𝔖` a covering of `X` by compact subsets, `α` a uniform space,
and `F : ι → (X → α)` a family which is equicontinuous on each `K ∈ 𝔖`. Then, the topologies
of uniform convergence on `𝔖` and pointwise convergence induce the same topology on `ι`.

This is a specialization of `EquicontinuousOn.inducing_uniformOnFun_iff_pi'` to
the case where `𝔖` covers `X`. -/
/-
**EquicontinuousOn.isInducing_uniformOnFun_iff_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：EquicontinuousOn.isInducing_uniformOnFun_iff_pi [TopologicalSpace ι] {𝔖 : 
Set (Set X)} (𝔖_covers : ⋃₀ 𝔖 = univ) (𝔖_compact : forall K in 𝔖, IsCompact K) (
F_eqcont : forall K in 𝔖, EquicontinuousOn F K) : IsInducing (UniformOnFun.ofFun
 𝔖 ∘ F) ↔ IsInducing F
参数：Set X；𝔖_covers : ⋃₀ 𝔖 = univ；𝔖_compact : forall K in 𝔖, IsCompact K；F_eqcont 
: forall K in 𝔖, EquicontinuousOn F K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用引理 `EquicontinuousOn.inducing_uniformOnFun_iff_pi'`：EquicontinuousOn.inducin
g_uniformOnFun_iff_pi' [TopologicalSpace ι] {𝔖 : Set (Set X)} (𝔖_compact : foral
l K in 𝔖, IsCompact K) (F_eqcont : f…
· 使用定理 `Topology.IsInducing.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3}
 {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalSpac
e X] [inst_2 :…
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h

--- 原说明 ---
Let `X` be a topological space, `𝔖` a covering of `X` by compact subsets, `α` a 
uniform space,
and `F : ι → (X → α)` a family which is equicontinuous on each `K ∈ 𝔖`. Then, th
e topologies
of uniform convergence on `𝔖` and pointwise convergence induce the same topology
 on `ι`.

This is a specialization of `EquicontinuousOn.inducing_uniformOnFun_iff_pi'` to
the case where `𝔖` covers `X`.
-/
lemma EquicontinuousOn.isInducing_uniformOnFun_iff_pi [TopologicalSpace ι]
    {𝔖 : Set (Set X)} (𝔖_covers : ⋃₀ 𝔖 = univ) (𝔖_compact : ∀ K ∈ 𝔖, IsCompact K)
    (F_eqcont : ∀ K ∈ 𝔖, EquicontinuousOn F K) :
    IsInducing (UniformOnFun.ofFun 𝔖 ∘ F) ↔
    IsInducing F := by
  rw [eq_univ_iff_forall] at 𝔖_covers
  -- This obviously follows from the previous lemma, we formalize it by going through the
  -- homeomorphism between `(⋃₀ 𝔖) → α` and `X → α`.
  let φ : ((⋃₀ 𝔖) → α) ≃ₜ (X → α) := Homeomorph.piCongrLeft (Y := fun _ ↦ α)
    (Equiv.subtypeUnivEquiv 𝔖_covers)
  rw [EquicontinuousOn.inducing_uniformOnFun_iff_pi' 𝔖_compact F_eqcont,
      show domRestrict (⋃₀ 𝔖) ∘ F = φ.symm ∘ F by rfl]
  exact ⟨fun H ↦ φ.isInducing.comp H, fun H ↦ φ.symm.isInducing.comp H⟩

-- TODO: find a way to factor common elements of this proof and the proof of
-- `EquicontinuousOn.comap_uniformOnFun_eq`
/-- Let `X` be a topological space, `𝔖` a family of compact subsets of `X`,
`α` a uniform space, `F : ι → (X → α)` a family equicontinuous on each `K ∈ 𝔖`, and `ℱ` a filter
on `ι`. Then, `F` tends to `f : X → α` along `ℱ` *uniformly on each `K ∈ 𝔖`* iff it tends to `f`
*pointwise on `⋃₀ 𝔖`* along `ℱ`. -/
/-
**EquicontinuousOn.tendsto_uniformOnFun_iff_pi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EquicontinuousOn.tendsto_uniformOnFun_iff_pi' {𝔖 : Set (Set X)} (𝔖_compact
 : forall K in 𝔖, IsCompact K) (F_eqcont : forall K in 𝔖, EquicontinuousOn F K) 
(ℱ : Filter ι) (f : X -> α) : Tendsto (UniformOnFun.ofFun 𝔖 ∘ F) ℱ (𝓝 <| Uniform
OnFun.ofFun 𝔖 f) ↔ Tendsto ((⋃₀ 𝔖).domRestrict ∘ F) ℱ (𝓝 <| (⋃₀ 𝔖).domRestrict f
)
参数：Set X；𝔖_compact : forall K in 𝔖, IsCompact K；F_eqcont : forall K in 𝔖, Equico
ntinuousOn F K；ℱ : Filter ι；f : X -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UniformOnFun.topologicalSpace_eq`：∀ (α : Type u_1) (β : Type u_2) [inst 
: UniformSpace β] (𝔖 : Set (Set α)),   UniformOnFun.topologicalSpace α β 𝔖 =    
 ⨅ s ∈ 𝔖,       Topolo…
· 使用引理 `Pi.induced_domRestrict_sUnion`：Pi.induced_domRestrict_sUnion (𝔖 : Set (S
et ι)) : induced (⋃₀ 𝔖).domRestrict (Pi.topologicalSpace (Y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nhds_iInf`：nhds_iInf {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α} :
 @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `Equicontinuous.tendsto_uniformFun_iff_pi`：Equicontinuous.tendsto_uniform
Fun_iff_pi [CompactSpace X] (F_eqcont : Equicontinuous F) (ℱ : Filter ι) (f : X 
-> α) : Tendsto (UniformFun.of…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `equicontinuous_restrict_iff`：equicontinuous_restrict_iff (F : ι -> X -> 
α) {S : Set X} : Equicontinuous (S.domRestrict ∘ F) ↔ EquicontinuousOn F S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Let `X` be a topological space, `𝔖` a family of compact subsets of `X`,
`α` a uniform space, `F : ι → (X → α)` a family equicontinuous on each `K ∈ 𝔖`, 
and `ℱ` a filter
on `ι`. Then, `F` tends to `f : X → α` along `ℱ` *uniformly on each `K ∈ 𝔖`* iff
 it tends to `f`
*pointwise on `⋃₀ 𝔖`* along `ℱ`.
-/
theorem EquicontinuousOn.tendsto_uniformOnFun_iff_pi'
    {𝔖 : Set (Set X)} (𝔖_compact : ∀ K ∈ 𝔖, IsCompact K)
    (F_eqcont : ∀ K ∈ 𝔖, EquicontinuousOn F K) (ℱ : Filter ι) (f : X → α) :
    Tendsto (UniformOnFun.ofFun 𝔖 ∘ F) ℱ (𝓝 <| UniformOnFun.ofFun 𝔖 f) ↔
    Tendsto ((⋃₀ 𝔖).domRestrict ∘ F) ℱ (𝓝 <| (⋃₀ 𝔖).domRestrict f) := by
  -- Recall that the uniform structure on `X →ᵤ[𝔖] α` is the one induced by all the maps
  -- `K.domRestrict : (X →ᵤ[𝔖] α) → (K →ᵤ α)` for `K ∈ 𝔖`.
  -- Similarly, the uniform structure on `X → α` induced by the map
  -- `(⋃₀ 𝔖).domRestrict : (X → α) → ((⋃₀ 𝔖) → α)` is equal to the one induced by
  -- all maps `K.domRestrict : (X → α) → (K → α)` for `K ∈ 𝔖`
  -- Thus, we just have to compare the two sides of our goal when restricted to some
  -- `K ∈ 𝔖`, where we can apply `Equicontinuous.tendsto_uniformFun_iff_pi`.
  rw [← Filter.tendsto_comap_iff (g := (⋃₀ 𝔖).domRestrict), ← nhds_induced]
  simp_rw +instances [UniformOnFun.topologicalSpace_eq,
    Pi.induced_domRestrict_sUnion 𝔖 (A := fun _ ↦ α), _root_.nhds_iInf, nhds_induced, tendsto_iInf,
    tendsto_comap_iff]
  congrm ∀ K (hK : K ∈ 𝔖), ?_
  have : CompactSpace K := isCompact_iff_compactSpace.mp (𝔖_compact K hK)
  rw [← (equicontinuous_restrict_iff _ |>.mpr <| F_eqcont K hK).tendsto_uniformFun_iff_pi]
  rfl

/-- Let `X` be a topological space, `𝔖` a covering of `X` by compact subsets,
`α` a uniform space, `F : ι → (X → α)` a family equicontinuous on each `K ∈ 𝔖`, and `ℱ` a filter
on `ι`. Then, `F` tends to `f : X → α` along `ℱ` *uniformly on each `K ∈ 𝔖`* iff it tends to `f`
*pointwise* along `ℱ`.

This is a specialization of `EquicontinuousOn.tendsto_uniformOnFun_iff_pi'` to the case
where `𝔖` covers `X`. -/
/-
**EquicontinuousOn.tendsto_uniformOnFun_iff_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EquicontinuousOn.tendsto_uniformOnFun_iff_pi {𝔖 : Set (Set X)} (𝔖_compact 
: forall K in 𝔖, IsCompact K) (𝔖_covers : ⋃₀ 𝔖 = univ) (F_eqcont : forall K in 𝔖
, EquicontinuousOn F K) (ℱ : Filter ι) (f : X -> α) : Tendsto (UniformOnFun.ofFu
n 𝔖 ∘ F) ℱ (𝓝 <| UniformOnFun.ofFun 𝔖 f) ↔ Tendsto F ℱ (𝓝 f)
参数：Set X；𝔖_compact : forall K in 𝔖, IsCompact K；𝔖_covers : ⋃₀ 𝔖 = univ；F_eqcont 
: forall K in 𝔖, EquicontinuousOn F K；ℱ : Filter ι；f : X -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `EquicontinuousOn.tendsto_uniformOnFun_iff_pi'`：EquicontinuousOn.tendsto_
uniformOnFun_iff_pi' {𝔖 : Set (Set X)} (𝔖_compact : forall K in 𝔖, IsCompact K) 
(F_eqcont : forall K in 𝔖, Equicont…
· 使用引理 `Topology.IsInducing.tendsto_nhds_iff`：tendsto_nhds_iff {f : ι -> Y} {l :
 Filter ι} {y : Y} (hg : IsInducing g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (
𝓝 (g y))
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Let `X` be a topological space, `𝔖` a covering of `X` by compact subsets,
`α` a uniform space, `F : ι → (X → α)` a family equicontinuous on each `K ∈ 𝔖`, 
and `ℱ` a filter
on `ι`. Then, `F` tends to `f : X → α` along `ℱ` *uniformly on each `K ∈ 𝔖`* iff
 it tends to `f`
*pointwise* along `ℱ`.

This is a specialization of `EquicontinuousOn.tendsto_uniformOnFun_iff_pi'` to t
he case
where `𝔖` covers `X`.
-/
theorem EquicontinuousOn.tendsto_uniformOnFun_iff_pi
    {𝔖 : Set (Set X)} (𝔖_compact : ∀ K ∈ 𝔖, IsCompact K) (𝔖_covers : ⋃₀ 𝔖 = univ)
    (F_eqcont : ∀ K ∈ 𝔖, EquicontinuousOn F K) (ℱ : Filter ι) (f : X → α) :
    Tendsto (UniformOnFun.ofFun 𝔖 ∘ F) ℱ (𝓝 <| UniformOnFun.ofFun 𝔖 f) ↔
    Tendsto F ℱ (𝓝 f) := by
  rw [eq_univ_iff_forall] at 𝔖_covers
  let φ : ((⋃₀ 𝔖) → α) ≃ₜ (X → α) := Homeomorph.piCongrLeft (Y := fun _ ↦ α)
    (Equiv.subtypeUnivEquiv 𝔖_covers)
  rw [EquicontinuousOn.tendsto_uniformOnFun_iff_pi' 𝔖_compact F_eqcont,
      show domRestrict (⋃₀ 𝔖) ∘ F = φ.symm ∘ F by rfl,
      show domRestrict (⋃₀ 𝔖) f = φ.symm f by rfl,
      φ.symm.isInducing.tendsto_nhds_iff]

/-- Let `X` be a topological space, `𝔖` a family of compact subsets of `X` and
`α` a uniform space. An equicontinuous subset of `X → α` is closed in the topology of uniform
convergence on all `K ∈ 𝔖` iff it is closed in the topology of pointwise convergence on `⋃₀ 𝔖`. -/
/-
**EquicontinuousOn.isClosed_range_pi_of_uniformOnFun'** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：EquicontinuousOn.isClosed_range_pi_of_uniformOnFun' {𝔖 : Set (Set X)} (𝔖_c
ompact : forall K in 𝔖, IsCompact K) (F_eqcont : forall K in 𝔖, EquicontinuousOn
 F K) (H : IsClosed (range <| UniformOnFun.ofFun 𝔖 ∘ F)) : IsClosed (range <| (⋃
₀ 𝔖).domRestrict ∘ F)
参数：Set X；𝔖_compact : forall K in 𝔖, IsCompact K；F_eqcont : forall K in 𝔖, Equico
ntinuousOn F K；H : IsClosed (range <| UniformOnFun.ofFun 𝔖 ∘ F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `DiscreteUniformity.instOfFiniteOfDiscreteTopology`：∀ {Y : Type u_2} [Fin
ite Y] [inst : UniformSpace Y] [DiscreteTopology Y], DiscreteUniformity Y
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `instT1SpaceForall`：∀ {ι : Type u_3} {X : ι → Type u_4} [inst : (i : ι) →
 TopologicalSpace (X i)] [∀ (i : ι), T1Space (X i)],   T1Space ((i : ι) → X i)
· 使用定理 `T4Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T4
Space X], T1Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
· 使用定理 `NormalSpace.of_compactSpace_r1Space`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompactSpace X] [R1Space X], NormalSpace X
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyOfSubsingleton`：∀ {α : Type u} [inst : Topological
Space α] [Subsingleton α], IndiscreteTopology α
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Function.Injective.surjective_comp_right`：∀ {α : Sort u_1} {β : Sort u_2
} {γ : Sort u_3} {f : α → β} [Nonempty γ],   Function.Injective f → Function.Sur
jective fun g => g ∘ f
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EquicontinuousOn.tendsto_uniformOnFun_iff_pi'`：EquicontinuousOn.tendsto_
uniformOnFun_iff_pi' {𝔖 : Set (Set X)} (𝔖_compact : forall K in 𝔖, IsCompact K) 
(F_eqcont : forall K in 𝔖, Equicont…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Let `X` be a topological space, `𝔖` a family of compact subsets of `X` and
`α` a uniform space. An equicontinuous subset of `X → α` is closed in the topolo
gy of uniform
convergence on all `K ∈ 𝔖` iff it is closed in the topology of pointwise converg
ence on `⋃₀ 𝔖`.
-/
theorem EquicontinuousOn.isClosed_range_pi_of_uniformOnFun'
    {𝔖 : Set (Set X)} (𝔖_compact : ∀ K ∈ 𝔖, IsCompact K)
    (F_eqcont : ∀ K ∈ 𝔖, EquicontinuousOn F K)
    (H : IsClosed (range <| UniformOnFun.ofFun 𝔖 ∘ F)) :
    IsClosed (range <| (⋃₀ 𝔖).domRestrict ∘ F) := by
  -- Do we have no equivalent of `nontriviality`?
  rcases isEmpty_or_nonempty α with _ | _
  · simp [isClosed_discrete]
  -- This follows from the previous lemmas and the characterization of the closure using filters.
  simp_rw [isClosed_iff_clusterPt, ← Filter.map_top, ← mapClusterPt_def,
    mapClusterPt_iff_ultrafilter, range_comp, Subtype.coe_injective.surjective_comp_right.forall,
    ← domRestrict_eq, ← EquicontinuousOn.tendsto_uniformOnFun_iff_pi' 𝔖_compact F_eqcont]
  exact fun f ⟨u, _, hu⟩ ↦ mem_image_of_mem _ <| H.mem_of_tendsto hu <|
    Eventually.of_forall mem_range_self

/-- Let `X` be a topological space, `𝔖` a covering of `X` by compact subsets, and
`α` a uniform space. An equicontinuous subset of `X → α` is closed in the topology of uniform
convergence on all `K ∈ 𝔖` iff it is closed in the topology of pointwise convergence.

This is a specialization of `EquicontinuousOn.isClosed_range_pi_of_uniformOnFun'` to the case where
`𝔖` covers `X`. -/
/-
**EquicontinuousOn.isClosed_range_uniformOnFun_iff_pi** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：EquicontinuousOn.isClosed_range_uniformOnFun_iff_pi {𝔖 : Set (Set X)} (𝔖_c
ompact : forall K in 𝔖, IsCompact K) (𝔖_covers : ⋃₀ 𝔖 = univ) (F_eqcont : forall
 K in 𝔖, EquicontinuousOn F K) : IsClosed (range <| UniformOnFun.ofFun 𝔖 ∘ F) ↔ 
IsClosed (range F)
参数：Set X；𝔖_compact : forall K in 𝔖, IsCompact K；𝔖_covers : ⋃₀ 𝔖 = univ；F_eqcont 
: forall K in 𝔖, EquicontinuousOn F K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EquicontinuousOn.tendsto_uniformOnFun_iff_pi`：EquicontinuousOn.tendsto_u
niformOnFun_iff_pi {𝔖 : Set (Set X)} (𝔖_compact : forall K in 𝔖, IsCompact K) (𝔖
_covers : ⋃₀ 𝔖 = univ) (F_eqcont :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Let `X` be a topological space, `𝔖` a covering of `X` by compact subsets, and
`α` a uniform space. An equicontinuous subset of `X → α` is closed in the topolo
gy of uniform
convergence on all `K ∈ 𝔖` iff it is closed in the topology of pointwise converg
ence.

This is a specialization of `EquicontinuousOn.isClosed_range_pi_of_uniformOnFun'
` to the case where
`𝔖` covers `X`.
-/
theorem EquicontinuousOn.isClosed_range_uniformOnFun_iff_pi
    {𝔖 : Set (Set X)} (𝔖_compact : ∀ K ∈ 𝔖, IsCompact K) (𝔖_covers : ⋃₀ 𝔖 = univ)
    (F_eqcont : ∀ K ∈ 𝔖, EquicontinuousOn F K) :
    IsClosed (range <| UniformOnFun.ofFun 𝔖 ∘ F) ↔
    IsClosed (range F) := by
  -- This follows from the previous lemmas and the characterization of the closure using filters.
  simp_rw [isClosed_iff_clusterPt, ← Filter.map_top, ← mapClusterPt_def,
    mapClusterPt_iff_ultrafilter, range_comp, (UniformOnFun.ofFun 𝔖).surjective.forall,
    ← EquicontinuousOn.tendsto_uniformOnFun_iff_pi 𝔖_compact 𝔖_covers F_eqcont,
    (UniformOnFun.ofFun 𝔖).injective.mem_set_image]

alias ⟨EquicontinuousOn.isClosed_range_pi_of_uniformOnFun, _⟩ :=
  EquicontinuousOn.isClosed_range_uniformOnFun_iff_pi

/-- A version of the **Arzela-Ascoli theorem**.

Let `X` be a topological space, `𝔖` a family of compact subsets of `X`, `α` a uniform space,
and `F : ι → (X → α)`. Assume that:
* `F`, viewed as a function `ι → (X →ᵤ[𝔖] α)`, is closed and inducing
* `F` is equicontinuous on each `K ∈ 𝔖`
* For all `x ∈ ⋃₀ 𝔖`, the range of `i ↦ F i x` is contained in some fixed compact subset.

Then `ι` is compact. -/
/-
**ArzelaAscoli.compactSpace_of_closed_inducing'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ArzelaAscoli.compactSpace_of_closed_inducing' [TopologicalSpace ι] {𝔖 : Se
t (Set X)} (𝔖_compact : forall K in 𝔖, IsCompact K) (F_ind : IsInducing (Uniform
OnFun.ofFun 𝔖 ∘ F)) (F_cl : IsClosed <| range <| UniformOnFun.ofFun 𝔖 ∘ F) (F_eq
cont : forall K in 𝔖, EquicontinuousOn F K) (F_pointwiseCompact : forall K in 𝔖,
 forall x in K, exists Q, IsCompact Q ∧ forall i, F i x in Q) : CompactSpace ι
参数：Set X；𝔖_compact : forall K in 𝔖, IsCompact K；F_ind : IsInducing (UniformOnFun
.ofFun 𝔖 ∘ F)；F_cl : IsClosed <| range <| UniformOnFun.ofFun 𝔖 ∘ F；F_eqcont : fo
rall K in 𝔖, EquicontinuousOn F K；F_pointwiseCompact : forall K in 𝔖, forall x i
n K, exists Q, IsCompact Q ∧ forall i, F i x in Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EquicontinuousOn.inducing_uniformOnFun_iff_pi'`：EquicontinuousOn.inducin
g_uniformOnFun_iff_pi' [TopologicalSpace ι] {𝔖 : Set (Set X)} (𝔖_compact : foral
l K in 𝔖, IsCompact K) (F_eqcont : f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompact_univ_iff`：isCompact_univ_iff : IsCompact (univ : Set X) ↔ Comp
actSpace X
· 使用定理 `Topology.IsInducing.isCompact_iff`：Topology.IsInducing.isCompact_iff {f 
: X -> Y} (hf : IsInducing f) : IsCompact s ↔ IsCompact (f '' s)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isCompact_univ_pi`：isCompact_univ_pi {s : forall i, Set (X i)} (h : fora
ll i, IsCompact (s i)) : IsCompact (pi univ s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `EquicontinuousOn.isClosed_range_pi_of_uniformOnFun'`：EquicontinuousOn.is
Closed_range_pi_of_uniformOnFun' {𝔖 : Set (Set X)} (𝔖_compact : forall K in 𝔖, I
sCompact K) (F_eqcont : forall K in 𝔖, Eq…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `forall_sUnion`：forall_sUnion {S : Set (Set α)} {p : α -> Prop} : (forall
 x in ⋃₀ S, p x) ↔ forall s in S, forall x in s, p x
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A version of the **Arzela-Ascoli theorem**.

Let `X` be a topological space, `𝔖` a family of compact subsets of `X`, `α` a un
iform space,
and `F : ι → (X → α)`. Assume that:
* `F`, viewed as a function `ι → (X →ᵤ[𝔖] α)`, is closed and inducing
* `F` is equicontinuous on each `K ∈ 𝔖`
* For all `x ∈ ⋃₀ 𝔖`, the range of `i ↦ F i x` is contained in some fixed compac
t subset.

Then `ι` is compact.
-/
theorem ArzelaAscoli.compactSpace_of_closed_inducing' [TopologicalSpace ι] {𝔖 : Set (Set X)}
    (𝔖_compact : ∀ K ∈ 𝔖, IsCompact K) (F_ind : IsInducing (UniformOnFun.ofFun 𝔖 ∘ F))
    (F_cl : IsClosed <| range <| UniformOnFun.ofFun 𝔖 ∘ F)
    (F_eqcont : ∀ K ∈ 𝔖, EquicontinuousOn F K)
    (F_pointwiseCompact : ∀ K ∈ 𝔖, ∀ x ∈ K, ∃ Q, IsCompact Q ∧ ∀ i, F i x ∈ Q) :
    CompactSpace ι := by
  -- By equicontinuity, we know that the topology on `ι` is also the one induced by
  -- `domRestrict (⋃₀ 𝔖) ∘ F`.
  have : IsInducing (domRestrict (⋃₀ 𝔖) ∘ F) := by
    rwa [EquicontinuousOn.inducing_uniformOnFun_iff_pi' 𝔖_compact F_eqcont] at F_ind
  -- Thus, we just have to check that the range of this map is compact.
  rw [← isCompact_univ_iff, this.isCompact_iff, image_univ]
  -- But then we are working in a product space, where compactness can easily be proven using
  -- Tykhonov's theorem! More precisely, for each `x ∈ ⋃₀ 𝔖`, choose a compact set `Q x`
  -- containing all `F i x`s.
  rw [← forall_sUnion] at F_pointwiseCompact
  choose! Q Q_compact F_in_Q using F_pointwiseCompact
  -- Notice that, since the range of `F` is closed in `X →ᵤ[𝔖] α`, equicontinuity ensures that
  -- the range of `(⋃₀ 𝔖).domRestrict ∘ F` is still closed in the product topology.
  -- But it's contained in the product of the `Q x`s, which is compact by Tykhonov, hence
  -- it is compact as well.
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun x ↦ Q_compact x x.2)
    (EquicontinuousOn.isClosed_range_pi_of_uniformOnFun' 𝔖_compact F_eqcont F_cl)
    (range_subset_iff.mpr fun i x _ ↦ F_in_Q x x.2 i)

/-- A version of the **Arzela-Ascoli theorem**.

Let `X, ι` be topological spaces, `𝔖` a covering of `X` by compact subsets, `α` a uniform space,
and `F : ι → (X → α)`. Assume that:
* `F`, viewed as a function `ι → (X →ᵤ[𝔖] α)`, is a closed embedding (in other words, `ι`
  identifies to a closed subset of `X →ᵤ[𝔖] α` through `F`)
* `F` is equicontinuous on each `K ∈ 𝔖`
* For all `x`, the range of `i ↦ F i x` is contained in some fixed compact subset.

Then `ι` is compact. -/
/-
**ArzelaAscoli.compactSpace_of_isClosedEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ArzelaAscoli.compactSpace_of_isClosedEmbedding [TopologicalSpace ι] {𝔖 : S
et (Set X)} (𝔖_compact : forall K in 𝔖, IsCompact K) (F_clemb : IsClosedEmbeddin
g (UniformOnFun.ofFun 𝔖 ∘ F)) (F_eqcont : forall K in 𝔖, EquicontinuousOn F K) (
F_pointwiseCompact : forall K in 𝔖, forall x in K, exists Q, IsCompact Q ∧ foral
l i, F i x in Q) : CompactSpace ι
参数：Set X；𝔖_compact : forall K in 𝔖, IsCompact K；F_clemb : IsClosedEmbedding (Uni
formOnFun.ofFun 𝔖 ∘ F)；F_eqcont : forall K in 𝔖, EquicontinuousOn F K；F_pointwis
eCompact : forall K in 𝔖, forall x in K, exists Q, IsCompact Q ∧ forall i, F i x
 in Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArzelaAscoli.compactSpace_of_closed_inducing'`：ArzelaAscoli.compactSpace
_of_closed_inducing' [TopologicalSpace ι] {𝔖 : Set (Set X)} (𝔖_compact : forall 
K in 𝔖, IsCompact K) (F_ind : IsInd…
· 使用定理 `Topology.IsClosedEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Topo…
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…

--- 原说明 ---
A version of the **Arzela-Ascoli theorem**.

Let `X, ι` be topological spaces, `𝔖` a covering of `X` by compact subsets, `α` 
a uniform space,
and `F : ι → (X → α)`. Assume that:
* `F`, viewed as a function `ι → (X →ᵤ[𝔖] α)`, is a closed embedding (in other w
ords, `ι`
  identifies to a closed subset of `X →ᵤ[𝔖] α` through `F`)
* `F` is equicontinuous on each `K ∈ 𝔖`
* For all `x`, the range of `i ↦ F i x` is contained in some fixed compact subse
t.

Then `ι` is compact.
-/
theorem ArzelaAscoli.compactSpace_of_isClosedEmbedding [TopologicalSpace ι] {𝔖 : Set (Set X)}
    (𝔖_compact : ∀ K ∈ 𝔖, IsCompact K) (F_clemb : IsClosedEmbedding (UniformOnFun.ofFun 𝔖 ∘ F))
    (F_eqcont : ∀ K ∈ 𝔖, EquicontinuousOn F K)
    (F_pointwiseCompact : ∀ K ∈ 𝔖, ∀ x ∈ K, ∃ Q, IsCompact Q ∧ ∀ i, F i x ∈ Q) :
    CompactSpace ι :=
  compactSpace_of_closed_inducing' 𝔖_compact F_clemb.isInducing F_clemb.isClosed_range
    F_eqcont F_pointwiseCompact

/-- A version of the **Arzela-Ascoli theorem**.

Let `X, ι` be topological spaces, `𝔖` a covering of `X` by compact subsets, `α` a T2 uniform space,
`F : ι → (X → α)`, and `s` a subset of `ι`. Assume that:
* `F`, viewed as a function `ι → (X →ᵤ[𝔖] α)`, is a closed embedding (in other words, `ι`
  identifies to a closed subset of `X →ᵤ[𝔖] α` through `F`)
* `F '' s` is equicontinuous on each `K ∈ 𝔖`
* For all `x ∈ ⋃₀ 𝔖`, the image of `s` under `i ↦ F i x` is contained in some fixed compact subset.

Then `s` has compact closure in `ι`. -/
/-
**ArzelaAscoli.isCompact_closure_of_isClosedEmbedding** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：ArzelaAscoli.isCompact_closure_of_isClosedEmbedding [TopologicalSpace ι] [
T2Space α] {𝔖 : Set (Set X)} (𝔖_compact : forall K in 𝔖, IsCompact K) (F_clemb :
 IsClosedEmbedding (UniformOnFun.ofFun 𝔖 ∘ F)) {s : Set ι} (s_eqcont : forall K 
in 𝔖, EquicontinuousOn (F ∘ ((↑) : s -> ι)) K) (s_pointwiseCompact : forall K in
 𝔖, forall x in K, exists Q, IsCompact Q ∧ forall i in s, F i x in Q) : IsCompac
t (closure s)
参数：Set X；𝔖_compact : forall K in 𝔖, IsCompact K；F_clemb : IsClosedEmbedding (Uni
formOnFun.ofFun 𝔖 ∘ F)；s_eqcont : forall K in 𝔖, EquicontinuousOn (F ∘ ((↑) : s 
-> ι)) K；s_pointwiseCompact : forall K in 𝔖, forall x in K, exists Q, IsCompact 
Q ∧ forall i in s, F i x in Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `UniformOnFun.uniformContinuous_eval_of_mem`：uniformContinuous_eval_of_me
m {x : α} (hxs : x in s) (hs : s in 𝔖) : UniformContinuous ((Function.eval x : (
α -> β) -> β) ∘ toFun 𝔖)
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
· 使用定理 `EquicontinuousOn.closure'`：EquicontinuousOn.closure' {A : Set Y} {u : Y 
-> X -> α} {S : Set X} (hA : EquicontinuousOn (u ∘ (↑) : A -> X -> α) S) (hu : C
ontinuous (S.do…
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `ArzelaAscoli.compactSpace_of_isClosedEmbedding`：ArzelaAscoli.compactSpac
e_of_isClosedEmbedding [TopologicalSpace ι] {𝔖 : Set (Set X)} (𝔖_compact : foral
l K in 𝔖, IsCompact K) (F_clemb : Is…
· 使用定理 `Topology.IsClosedEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Ty
pe u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologi
calSpace Y] [inst_2 :…
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)

--- 原说明 ---
A version of the **Arzela-Ascoli theorem**.

Let `X, ι` be topological spaces, `𝔖` a covering of `X` by compact subsets, `α` 
a T2 uniform space,
`F : ι → (X → α)`, and `s` a subset of `ι`. Assume that:
* `F`, viewed as a function `ι → (X →ᵤ[𝔖] α)`, is a closed embedding (in other w
ords, `ι`
  identifies to a closed subset of `X →ᵤ[𝔖] α` through `F`)
* `F '' s` is equicontinuous on each `K ∈ 𝔖`
* For all `x ∈ ⋃₀ 𝔖`, the image of `s` under `i ↦ F i x` is contained in some fi
xed compact subset.

Then `s` has compact closure in `ι`.
-/
theorem ArzelaAscoli.isCompact_closure_of_isClosedEmbedding [TopologicalSpace ι] [T2Space α]
    {𝔖 : Set (Set X)} (𝔖_compact : ∀ K ∈ 𝔖, IsCompact K)
    (F_clemb : IsClosedEmbedding (UniformOnFun.ofFun 𝔖 ∘ F))
    {s : Set ι} (s_eqcont : ∀ K ∈ 𝔖, EquicontinuousOn (F ∘ ((↑) : s → ι)) K)
    (s_pointwiseCompact : ∀ K ∈ 𝔖, ∀ x ∈ K, ∃ Q, IsCompact Q ∧ ∀ i ∈ s, F i x ∈ Q) :
    IsCompact (closure s) := by
  -- We apply `ArzelaAscoli.compactSpace_of_isClosedEmbedding` to the map
  -- `F ∘ (↑) : closure s → (X → α)`, for which all the hypotheses are easily verified.
  rw [isCompact_iff_compactSpace]
  have : ∀ K ∈ 𝔖, ∀ x ∈ K, Continuous (eval x ∘ F) := fun K hK x hx ↦
    UniformOnFun.uniformContinuous_eval_of_mem _ _ hx hK |>.continuous.comp F_clemb.continuous
  have cls_eqcont : ∀ K ∈ 𝔖, EquicontinuousOn (F ∘ ((↑) : closure s → ι)) K :=
    fun K hK ↦ (s_eqcont K hK).closure' <| show Continuous (K.domRestrict ∘ F) from
      continuous_pi fun ⟨x, hx⟩ ↦ this K hK x hx
  have cls_pointwiseCompact : ∀ K ∈ 𝔖, ∀ x ∈ K, ∃ Q, IsCompact Q ∧ closure s ⊆ {i | F i x ∈ Q} :=
    fun K hK x hx ↦ (s_pointwiseCompact K hK x hx).imp fun Q hQ ↦ ⟨hQ.1, closure_minimal hQ.2 <|
      hQ.1.isClosed.preimage (this K hK x hx)⟩
  exact ArzelaAscoli.compactSpace_of_isClosedEmbedding 𝔖_compact
    (F_clemb.comp isClosed_closure.isClosedEmbedding_subtypeVal) cls_eqcont
    fun K hK x hx ↦ (cls_pointwiseCompact K hK x hx).imp fun Q hQ ↦ ⟨hQ.1, by simpa using! hQ.2⟩

/-- A version of the **Arzela-Ascoli theorem**.

If an equicontinuous family of continuous functions is compact in the pointwise topology, then it
is compact in the compact open topology. -/
/-
**ArzelaAscoli.isCompact_of_equicontinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ArzelaAscoli.isCompact_of_equicontinuous (S : Set C(X, α)) (hS1 : IsCompac
t (ContinuousMap.toFun '' S)) (hS2 : Equicontinuous ((↑) : S -> X -> α)) : IsCom
pact S
参数：S : Set C(X, α)；hS1 : IsCompact (ContinuousMap.toFun '' S)；hS2 : Equicontinuo
us ((↑) : S -> X -> α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z : Ty
pe u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : Topologi
calSpace X] [inst_2 :…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用引理 `EquicontinuousOn.isInducing_uniformOnFun_iff_pi`：EquicontinuousOn.isIndu
cing_uniformOnFun_iff_pi [TopologicalSpace ι] {𝔖 : Set (Set X)} (𝔖_covers : ⋃₀ 𝔖
 = univ) (𝔖_compact : forall K in 𝔖, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Set.mem_sUnion_of_mem`：mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (S
et α)} (hx : x in t) (ht : t in S) : x in ⋃₀ S
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用引理 `Equicontinuous.equicontinuousOn`：Equicontinuous.equicontinuousOn {F : ι 
-> X -> α} (H : Equicontinuous F) (S : Set X) : EquicontinuousOn F S
· 使用定理 `Topology.IsInducing.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3}
 {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalSpac
e X] [inst_2 :…
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact`：isUniformEmbed
ding_toUniformOnFunIsCompact : IsUniformEmbedding (toUniformOnFunIsCompact : C(α
, β) -> α ->ᵤ[{K | IsCompact K}] β) where coma…
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `Homeomorph.compactSpace`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] [CompactSpace X] (h : X ≃ₜ Y),   Comp
actSpace Y

--- 原说明 ---
A version of the **Arzela-Ascoli theorem**.

If an equicontinuous family of continuous functions is compact in the pointwise 
topology, then it
is compact in the compact open topology.
-/
theorem ArzelaAscoli.isCompact_of_equicontinuous
    (S : Set C(X, α)) (hS1 : IsCompact (ContinuousMap.toFun '' S))
    (hS2 : Equicontinuous ((↑) : S → X → α)) : IsCompact S := by
  suffices h : IsInducing (Equiv.Set.image _ S DFunLike.coe_injective) by
    rw [isCompact_iff_compactSpace] at hS1 ⊢
    exact (Equiv.toHomeomorphOfIsInducing _ h).symm.compactSpace
  rw [← IsInducing.subtypeVal.of_comp_iff, ← EquicontinuousOn.isInducing_uniformOnFun_iff_pi]
  · exact ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isInducing.comp .subtypeVal
  · exact eq_univ_iff_forall.mpr (fun x ↦ mem_sUnion_of_mem (mem_singleton x) isCompact_singleton)
  · exact fun _ ↦ id
  · exact fun K _ ↦ hS2.equicontinuousOn K
