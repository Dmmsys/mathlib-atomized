/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A linear map which is locally an embedding is an embedding

Fix `𝕜` a `NontriviallyNormedField`, `E`, `F` two topological vector spaces over `𝕜`, and
`f : E → F` a `𝕜`-linear map. We show that, if there is a neighborhood `V` of `0 : E`
such that the restriction `V → F` is an embedding, then `f` itself is an embedding.

Note that this result is false for topological groups, as shown by the following counterexamples:
* first, in the group setting, there are local embeddings (even local homeomorphisms) which
  are not globally injective; an example is the quotient map `ℝ → 𝕋 := ℝ ⧸ ℤ`;
* even if assume that `f` is globally injective, the theorem still fails. Consider for example
  `f : ℝ → 𝕋 × 𝕋` given by `x ↦ ([x], [α * x])`, with `α` irrational. `f` is injective, and locally
  an embedding by the inverse function theorem, yet it is not globally an embedding: any
  neighborhood of `f(0) = (0, 0)` contains infinitely many points `f(n)`, `n ∈ ℤ`, since
  `α * n` gets arbitrarily close to being an integer infinitely many times.

## Main results

* `ContinuousSMul.topology_eq_of_induced_eq`: let `t₁`, `t₂` be two vector space
  topologies on `E`, and assume that there is a `t₁`-neighborhood of 0 `V` in restriction to
  which the two topologies coincide. Then `t₁ = t₂`.
* `LinearMap.isInducing_of_restrict_nhds_zero`: consider a linear map `f : E → F`, and assume
  there is a neighborhood of 0 `V` in `E` such that `V.domRestrict f : V → F` satisfies
  `Topology.IsInducing`. Then `f` satisfies `Topology.IsInducing`.
* `LinearMap.isEmbedding_of_restrict_nhds_zero`: consider a linear map `f : E → F`, and assume
  there is a neighborhood of 0 `V` in `E` such that `V.domRestrict f : V → F` is a topological
  embedding. Then `f` is a topological embedding.

## TODO

We will also need the fact that if the restriction `V → F` is a *closed* embedding, then
`f : E → F` is a *closed* embedding. This will follow from the fact that a subgroup which is
locally closed at `0` is in fact closed, which we don't have yet

## Implementation details

The content of this file is essentially (variations of)
[N. Bourbaki, *Théories Spectrales*, Chapitre III, § 5, n° 1, lemme 1][bourbaki2023], except
Bourbaki's proof is very specific to `𝕜 = ℝ` or `𝕜 = ℂ`, since it relies crucially on balanced
sets being connected.

Nevertheless, we are able to adapt their proof to arbitrary nontrivially normed fields.
The key argument, replacing the fact that a connected set cannot be covered nontrivially by
disjoint open sets, is that a balanced set `W` cannot intersect nontrivially both `c • V`
and `Vᶜ`, when `V` is a neighborhood of `0` and `0 < ‖c‖ < 1`. We refer to the (highly commented!)
proof for more details.

## References

* [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 5, n° 1, lemme 1][bourbaki2023]

-/

@[expose] public section

open Topology Filter Bornology Set
open scoped Pointwise Set.Notation

variable {𝕜₁ 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  [AddCommGroup E] [AddCommGroup F] [Module 𝕜₁ E] [Module 𝕜₂ F] {σ : 𝕜₁ →+* 𝕜₂} {f : E →ₛₗ[σ] F}

variable (𝕜₁) in
/-- Consider a vector space `E` over a `NontriviallyNormedField` `𝕜`, and `t₁`, `t₂` two
vector space topologies on `E`.

Assume that there is a `t₁`-neighborhood of zero `V` such that the two topogies induce the
same filter of neighborhoods of `0` *in the subspace `V`*. Then `t₁ = t₂`. -/
/-
**ContinuousSMul.topology_eq_of_nhds_inf_principal_eq** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：ContinuousSMul.topology_eq_of_nhds_inf_principal_eq (t₁ t₂ : TopologicalSp
ace E) [@IsTopologicalAddGroup E t₁ _] [@IsTopologicalAddGroup E t₂ _] [@Continu
ousSMul 𝕜₁ E _ _ t₁] [@ContinuousSMul 𝕜₁ E _ _ t₂] {V : Set E} (V_mem : V in @nh
ds E t₁ 0) (H : @nhds E t₁ 0 ⊓ 𝓟 V = @nhds E t₂ 0 ⊓ 𝓟 V) : t₁ = t₂
参数：t₁ t₂ : TopologicalSpace E；V_mem : V in @nhds E t₁ 0；H : @nhds E t₁ 0 ⊓ 𝓟 V =
 @nhds E t₂ 0 ⊓ 𝓟 V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedField.exists_norm_lt_one`：exists_norm_lt_one : exists x : α, 0 < ‖
x‖ ∧ ‖x‖ < 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `set_smul_mem_nhds_zero_iff`：set_smul_mem_nhds_zero_iff {s : Set α} {c : 
G₀} (hc : c != 0) : c • s in 𝓝 (0 : α) ↔ s in 𝓝 (0 : α)
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `nhds_basis_balanced`：nhds_basis_balanced : (𝓝 (0 : E)).HasBasis (fun s :
 Set E => s in 𝓝 (0 : E) ∧ Balanced 𝕜 s) id
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.inf_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Fi
lter.principal s').…
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually_mem`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β},   Filter.Tendsto f l₁ l₂ → s ∈ l
₂ → ∀ᶠ (x : α) in l…
· 使用定理 `Filter.Tendsto.zero_smul_const`：∀ {M : Type u_1} {X : Type u_2} {α : Typ
e u_4} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : Zer
o M] [inst_3 : Zero …
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`：tendsto_pow_atTop_nhds_zero_
of_norm_lt_one {R : Type*} [SeminormedRing R] {x : R} (h : ‖x‖ < 1) : Tendsto (f
un n : Nat => x ^ n) atTop (𝓝 0)
· 使用定理 `Balanced.smul_mem`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRin
g 𝕜] [inst_1 : SMul 𝕜 E] {s : Set E},   Balanced 𝕜 s → ∀ ⦃a : 𝕜⦄, ‖a‖ ≤ 1 → ∀ ⦃x
 : E⦄, …
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Consider a vector space `E` over a `NontriviallyNormedField` `𝕜`, and `t₁`, `t₂`
 two
vector space topologies on `E`.

Assume that there is a `t₁`-neighborhood of zero `V` such that the two topogies 
induce the
same filter of neighborhoods of `0` *in the subspace `V`*. Then `t₁ = t₂`.
-/
lemma ContinuousSMul.topology_eq_of_nhds_inf_principal_eq (t₁ t₂ : TopologicalSpace E)
    [@IsTopologicalAddGroup E t₁ _] [@IsTopologicalAddGroup E t₂ _]
    [@ContinuousSMul 𝕜₁ E _ _ t₁] [@ContinuousSMul 𝕜₁ E _ _ t₂]
    {V : Set E} (V_mem : V ∈ @nhds E t₁ 0) (H : @nhds E t₁ 0 ⊓ 𝓟 V = @nhds E t₂ 0 ⊓ 𝓟 V) :
    t₁ = t₂ := by
  classical
  -- For `i = 1, 2`, denote by `𝓕ᵢ` the filter of neighborhoods of `0` for the topology `tᵢ`.
  set 𝓕₁ := @nhds E t₁ 0
  set 𝓕₂ := @nhds E t₂ 0
  -- Note that, because `V ∈ 𝓕₁`, `H` may be rewritten as `𝓕₁ = 𝓕₂ ⊓ 𝓟 V`.
  replace H : 𝓕₁ = 𝓕₂ ⊓ 𝓟 V := by simpa [← H]
  -- Because both `t₁` and `t₂` are additive group topologies, it is enough to show `𝓕₁ = 𝓕₂`.
  suffices 𝓕₁ = 𝓕₂ by rwa [IsTopologicalAddGroup.ext_iff] <;> infer_instance
  -- If we can show that `V ∈ 𝓕₂` we are done, because then `𝓕₁ = 𝓕₂ ⊓ 𝓟 V = 𝓕₂`.
  suffices V ∈ 𝓕₂ by simpa [H]
  -- Hence, let us show that `V ∈ 𝓕₂`. Fix a scalar `c` with `0 < ‖c‖ < 1`.
  obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt_one 𝕜₁
  have c_ne : c ≠ 0 := norm_pos_iff.mp hc₀
  -- We know that `c • V ∈ 𝓕₁ = 𝓕₂ ⊓ 𝓟 V`.
  have cV_mem : c • V ∈ 𝓕₂ ⊓ 𝓟 V := by
    simpa [← H, 𝓕₁, set_smul_mem_nhds_zero_iff c_ne]
  -- Furthermore, we know that `𝓕₂` has a basis of balanced sets
  have basis_𝓕₂ : HasBasis 𝓕₂ (fun (s : Set E) ↦ s ∈ 𝓕₂ ∧ Balanced 𝕜₁ s) id :=
    let := t₂; nhds_basis_balanced 𝕜₁ E
  -- Hence, we get a balanced set `W ∈ 𝓕₂` such that `W ∩ V ⊆ c • V`.
  obtain ⟨W, ⟨W_mem_𝓕₂, W_bal⟩, hW⟩ := basis_𝓕₂.inf_principal V |>.mem_iff.mp cV_mem
  -- We claim that `W ⊆ V`. This will conclude the proof, since `W ∈ 𝓕₂`.
  suffices W ⊆ V from mem_of_superset W_mem_𝓕₂ this
  -- Let `w ∈ W` be arbitrary.
  intro w w_in_W
  -- Because `V` is a `t₁`-neighborhood of `0`, we have `c ^ n • w ∈ V` for some natural number `n`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, c ^ n • w ∈ V :=
    let := t₁
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc₁ |>.zero_smul_const w
      |>.eventually_mem V_mem |>.exists
  -- We will conclude by reducing `c ^ n • w ∈ V` to `w = c ^ 0 • w ∈ V` inductively.
  suffices c ^ 0 • w ∈ V by simpa
  apply Nat.decreasingInduction (motive := fun (k : ℕ) _ ↦ c^k • w ∈ V) ?_ hn n.zero_le
  -- To do so, we show that if `k : ℕ` is such that `c ^ (k + 1) • w ∈ V` then `c ^ k • w ∈ V`.
  intro k _ (hk : c ^ (k + 1) • w ∈ V)
  -- Indeed, because `W` is balanced, we have `c ^ (k + 1) • w ∈ W ∩ V ⊆ c • V`
  have : c ^ (k + 1) • w ∈ c • V :=
    hW ⟨W_bal.smul_mem (by grw [norm_pow, hc₁.le, one_pow]) w_in_W, hk⟩
  -- Cancelling `c`, we get `c ^ k • w ∈ V` as we claimed.
  rwa [pow_add, pow_one, mul_comm, mul_smul, smul_mem_smul_set_iff₀ c_ne V] at this

variable (𝕜₁) in
/-- Consider a vector space `E` over a `NontriviallyNormedField` `𝕜`, and `t₁`, `t₂` two topologies
on `E` which are compatible with the vector space structure.

Assume that there is a `t₁`-neighborhood of zero `V` such that the two topogies induce the
same topology *on the subspace `V`*. Then `t₁ = t₂`. -/
/-
**ContinuousSMul.topology_eq_of_induced_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousSMul.topology_eq_of_induced_eq (t₁ t₂ : TopologicalSpace E) [@Is
TopologicalAddGroup E t₁ _] [@IsTopologicalAddGroup E t₂ _] [@ContinuousSMul 𝕜₁ 
E _ _ t₁] [@ContinuousSMul 𝕜₁ E _ _ t₂] {V : Set E} (V_mem : V in @nhds E t₁ 0) 
(H : t₁.induced ((↑) : V -> E) = t₂.induced ((↑) : V -> E)) : t₁ = t₂
参数：t₁ t₂ : TopologicalSpace E；V_mem : V in @nhds E t₁ 0；H : t₁.induced ((↑) : V 
-> E) = t₂.induced ((↑) : V -> E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousSMul.topology_eq_of_nhds_inf_principal_eq`：ContinuousSMul.topo
logy_eq_of_nhds_inf_principal_eq (t₁ t₂ : TopologicalSpace E) [@IsTopologicalAdd
Group E t₁ _] [@IsTopologicalAddGroup E t…
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Consider a vector space `E` over a `NontriviallyNormedField` `𝕜`, and `t₁`, `t₂`
 two topologies
on `E` which are compatible with the vector space structure.

Assume that there is a `t₁`-neighborhood of zero `V` such that the two topogies 
induce the
same topology *on the subspace `V`*. Then `t₁ = t₂`.
-/
lemma ContinuousSMul.topology_eq_of_induced_eq (t₁ t₂ : TopologicalSpace E)
    [@IsTopologicalAddGroup E t₁ _] [@IsTopologicalAddGroup E t₂ _]
    [@ContinuousSMul 𝕜₁ E _ _ t₁] [@ContinuousSMul 𝕜₁ E _ _ t₂]
    {V : Set E} (V_mem : V ∈ @nhds E t₁ 0)
    (H : t₁.induced ((↑) : V → E) = t₂.induced ((↑) : V → E)) :
    t₁ = t₂ := by
  apply topology_eq_of_nhds_inf_principal_eq 𝕜₁ t₁ t₂ V_mem
  set o : V := ⟨0, letI := t₁; mem_of_mem_nhds V_mem⟩
  simp_rw [← map_comap_setCoe_val, show 0 = (o : E) from rfl, ← nhds_induced]
  rw [H]

variable [TopologicalSpace E] [TopologicalSpace F]
  [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜₁ E] [ContinuousSMul 𝕜₂ F] [RingHomIsometric σ]
/-
**LinearMap.isInducing_of_restrict_nhds_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.isInducing_of_restrict_nhds_zero {V : Set E} (V_mem : V in 𝓝 0) 
(H : IsInducing (Set.domRestrict V f)) : IsInducing f
参数：V_mem : V in 𝓝 0；H : IsInducing (Set.domRestrict V f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.isInducing_iff`：∀ {X : Type u_1} {Y : Type u_2} [tX : Topologic
alSpace X] [tY : TopologicalSpace Y] (f : X → Y),   Topology.IsInducing f ↔ tX =
 TopologicalS…
· 使用定理 `topologicalAddGroup_induced`：∀ {G : Type w} {H : Type x} [inst : Topolog
icalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {F : Type u_1}   [i
nst_3 : AddGroup …
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `continuousSMul_inducedₛₗ`：continuousSMul_inducedₛₗ (hφ : Continuous φ) :
 @ContinuousSMul R M₁ _ u (t'.induced f')
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用引理 `RingHom.isometry`：RingHom.isometry {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [
SeminormedRing 𝕜₂] (σ : 𝕜₁ ->+* 𝕜₂) [RingHomIsometric σ] : Isometry σ
· 使用引理 `ContinuousSMul.topology_eq_of_induced_eq`：ContinuousSMul.topology_eq_of_
induced_eq (t₁ t₂ : TopologicalSpace E) [@IsTopologicalAddGroup E t₁ _] [@IsTopo
logicalAddGroup E t₂ _] [@Cont…
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.domRestrict_eq`：domRestrict_eq (f : α -> β) (s : Set α) : s.domRestr
ict f = f ∘ Subtype.val
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
-/
lemma LinearMap.isInducing_of_restrict_nhds_zero {V : Set E}
    (V_mem : V ∈ 𝓝 0) (H : IsInducing (Set.domRestrict V f)) : IsInducing f := by
  rw [isInducing_iff]
  -- Call `t₁` the original topology on `E`, and `t₂` the topology induced by `f`. Because
  -- `f` is linear, `t₂` is also a vector space topology.
  have := topologicalAddGroup_induced f
  have := continuousSMul_inducedₛₗ f σ.isometry.continuous
  -- Because `Set.domRestrict V f` is an inducing, `t₁` and `t₂` induce the same topology
  -- on `V`, so we get `t₁ = t₂` from the lemmas above.
  apply ContinuousSMul.topology_eq_of_induced_eq 𝕜₁ _ (.induced f _) V_mem
  rw [induced_compose, ← domRestrict_eq, ← H.eq_induced, ← IsInducing.subtypeVal.eq_induced]
/-
**LinearMap.isEmbedding_of_restrict_nhds_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.isEmbedding_of_restrict_nhds_zero {V : Set E} (V_mem : V in 𝓝 0)
 (H : IsEmbedding (Set.domRestrict V f)) : IsEmbedding f
参数：V_mem : V in 𝓝 0；H : IsEmbedding (Set.domRestrict V f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.isInducing_of_restrict_nhds_zero`：LinearMap.isInducing_of_rest
rict_nhds_zero {V : Set E} (V_mem : V in 𝓝 0) (H : IsInducing (Set.domRestrict V
 f)) : IsInducing f
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Absorbent.eventually_nhdsNE_zero`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst 
: NormedDivisionRing 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]  
 {s : Set E}, Absorben…
· 使用定理 `absorbent_nhds_zero`：absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbe
nt 𝕜 A
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用引理 `smul_eq_zero_iff_right`：smul_eq_zero_iff_right (hr : r != 0) : r • m = 0
 ↔ m = 0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma LinearMap.isEmbedding_of_restrict_nhds_zero {V : Set E}
    (V_mem : V ∈ 𝓝 0) (H : IsEmbedding (Set.domRestrict V f)) : IsEmbedding f := by
  refine ⟨isInducing_of_restrict_nhds_zero V_mem H.isInducing, ?_⟩
  have f_injOn : InjOn f V := injOn_iff_injective.2 H.injective
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨c, hc, c_ne : c ≠ 0⟩ := absorbent_nhds_zero (𝕜 := 𝕜₁) V_mem
    |>.eventually_nhdsNE_zero x |>.and eventually_mem_nhdsWithin |>.exists
  rw [← smul_eq_zero_iff_right c_ne, ← f_injOn.eq_iff hc (mem_of_mem_nhds V_mem), map_zero,
    map_smulₛₗ, hx, smul_zero]
