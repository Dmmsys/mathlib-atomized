/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Basic

/-!
# Hausdorff properties of uniform spaces. Separation quotient.

Two points of a topological space are called `Inseparable`,
if their neighborhoods filter are equal.
Equivalently, `Inseparable x y` means that any open set that contains `x` must contain `y`
and vice versa.

In a uniform space, points `x` and `y` are inseparable
if and only if `(x, y)` belongs to all entourages,
see `inseparable_iff_ker_uniformity`.

A uniform space is a regular topological space,
hence separation axioms `T0Space`, `T1Space`, `T2Space`, and `T3Space`
are equivalent for uniform spaces,
and Lean typeclass search can automatically convert from one assumption to another.
We say that a uniform space is *separated*, if it satisfies these axioms.
If you need an `Iff` statement (e.g., to rewrite),
then see `R1Space.t0Space_iff_t2Space` and `RegularSpace.t0Space_iff_t3Space`.

In this file we prove several facts
that relate `Inseparable` and `Specializes` to the uniformity filter.
Most of them are simple corollaries of `Filter.HasBasis.inseparable_iff_uniformity`
for different filter bases of `𝓤 α`.

Then we study the Kolmogorov quotient `SeparationQuotient X` of a uniform space.
For a general topological space,
this quotient is defined as the quotient by `Inseparable` equivalence relation.
It is the maximal T₀ quotient of a topological space.

In case of a uniform space, we equip this quotient with a `UniformSpace` structure
that agrees with the quotient topology.
We also prove that the quotient map induces uniformity on the original space.

Finally, we turn `SeparationQuotient` into a functor
(not in terms of `CategoryTheory.Functor` to avoid extra imports)
by defining `SeparationQuotient.lift'` and `SeparationQuotient.map` operations.

## Main definitions

* `SeparationQuotient.instUniformSpace`: uniform space structure on `SeparationQuotient α`,
  where `α` is a uniform space;

* `SeparationQuotient.lift'`: given a map `f : α → β`
  from a uniform space to a separated uniform space,
  lift it to a map `SeparationQuotient α → β`;
  if the original map is not uniformly continuous, then returns a constant map.

* `SeparationQuotient.map`: given a map `f : α → β` between uniform spaces,
  returns a map `SeparationQuotient α → SeparationQuotient β`.
  If the original map is not uniformly continuous, then returns a constant map.
  Otherwise, `SeparationQuotient.map f (SeparationQuotient.mk x) = SeparationQuotient.mk (f x)`.

## Main results

* `SeparationQuotient.uniformity_eq`: the uniformity filter on `SeparationQuotient α`
  is the push forward of the uniformity filter on `α`.
* `SeparationQuotient.comap_mk_uniformity`: the quotient map `α → SeparationQuotient α`
  induces uniform space structure on the original space.
* `SeparationQuotient.uniformContinuous_lift'`: factoring a uniformly continuous map through the
  separation quotient gives a uniformly continuous map.
* `SeparationQuotient.uniformContinuous_map`: maps induced between separation quotients are
  uniformly continuous.

## Implementation notes

This file used to contain definitions of `separationRel α` and `UniformSpace.SeparationQuotient α`.
These definitions were equal (but not definitionally equal)
to `{x : α × α | Inseparable x.1 x.2}` and `SeparationQuotient α`, respectively,
and were added to the library before their generalizations to topological spaces.

In https://github.com/leanprover-community/mathlib4/pull/10644, we migrated from these definitions
to more general `Inseparable` and `SeparationQuotient`.

## TODO

Definitions `SeparationQuotient.lift'` and `SeparationQuotient.map`
rely on `UniformSpace` structures in the domain and in the codomain.
We should generalize them to topological spaces.
This generalization will drop `UniformContinuous` assumptions in some lemmas,
and add these assumptions in other lemmas,
so it was not done in https://github.com/leanprover-community/mathlib4/pull/10644 to keep it reasonably sized.

## Keywords

uniform space, separated space, Hausdorff space, separation quotient
-/

@[expose] public section

open Filter Set Function Topology Uniformity UniformSpace

noncomputable section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

/-!
### Separated uniform spaces
-/

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Separated uniform spaces
-/
instance (priority := 100) UniformSpace.to_regularSpace : RegularSpace α :=
  .of_hasBasis
    (fun _ ↦ nhds_basis_uniformity' uniformity_hasBasis_closed)
    fun a _V hV ↦ isClosed_ball a hV.2

/--
If the uniformity has a linearly ordered basis, then the space is completely normal.
-/
/-
**UniformSpace.completelyNormalSpace_of_hasAntitoneBasis** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：UniformSpace.completelyNormalSpace_of_hasAntitoneBasis {ι : Type*} [Linear
Order ι] {B : ι -> SetRel α α} (hB : (uniformity α).HasAntitoneBasis B) : Comple
telyNormalSpace α where completely_normal s t hSt hsT
参数：hB : (uniformity α).HasAntitoneBasis B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UniformSpace.mem_nhds_iff`：UniformSpace.mem_nhds_iff {x : α} {s : Set α}
 : s in 𝓝 x ↔ exists V in 𝓤 α, ball x V subseteq s
· 使用定理 `nhds_le_nhdsSet`：nhds_le_nhdsSet (h : x in s) : 𝓝 x <= 𝓝ˢ s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.disjoint_principal_right`：disjoint_principal_right {f : Filter α}
 {s : Set α} : Disjoint f (𝓟 s) ↔ sᶜ in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `disjoint_nhdsSet_principal`：disjoint_nhdsSet_principal : Disjoint (𝓝ˢ s)
 (𝓟 t) ↔ Disjoint s (closure t)
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用定理 `Filter.HasAntitoneBasis.mem_iff`：∀ {α : Type u_1} {ι : Type u_4} [inst :
 Preorder ι] {l : Filter α} {s : ι → Set α},   l.HasAntitoneBasis s → ∀ {t : Set
 α}, t ∈ l ↔ ∃ i, s i…
· 使用引理 `Set.subset_compl_iff_disjoint_right`：subset_compl_iff_disjoint_right : s
 subseteq tᶜ ↔ Disjoint s t
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用引理 `SetRel.comp_subset_comp`：comp_subset_comp {S₁ S₂ : SetRel β γ} (hR : R₁ 
subseteq R₂) (hS : S₁ subseteq S₂) : R₁ ○ S₁ subseteq R₂ ○ S₂
· 使用定理 `SetRel.inv_mono`：∀ {α : Type u_1} {β : Type u_2} {R₁ R₂ : SetRel α β}, R
₁ ⊆ R₂ → R₁.inv ⊆ R₂.inv
· 使用定理 `SetRel.inv_eq_self`：∀ {α : Type u_1} (R : SetRel α α) [R.IsSymm], R.inv 
= R
· 使用定理 `mem_nhdsSet_iff_forall`：mem_nhdsSet_iff_forall : s in 𝓝ˢ t ↔ forall x : 
X, x in t -> s in 𝓝 x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `UniformSpace.ball_mem_nhds`：UniformSpace.ball_mem_nhds (x : α) ⦃V : SetR
el α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x
· 使用定理 `Filter.HasAntitoneBasis.mem`：∀ {α : Type u_1} {ι : Type u_4} [inst : Pre
order ι] {l : Filter α} {s : ι → Set α},   l.HasAntitoneBasis s → ∀ (i : ι), s i
 ∈ l
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Filter.disjoint_iff`：∀ {α : Type u} {f g : Filter α}, Disjoint f g ↔ ∃ s
 ∈ f, ∃ t ∈ g, Disjoint s t
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `Disjoint.notMem_of_mem_left`：∀ {α : Type u} {s t : Set α}, Disjoint s t 
→ ∀ ⦃a : α⦄, a ∈ s → a ∉ t
· 使用定理 `UniformSpace.mem_ball_comp`：mem_ball_comp {V W : Set (β × β)} {x y z} (h
 : y in ball x V) (h' : z in ball y W) : z in ball x (V ○ W)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.HasAntitoneBasis.antitone`：∀ {α : Type u_1} {ι'' : Type u_6} [ins
t : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → Ant
itone s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If the uniformity has a linearly ordered basis, then the space is completely nor
mal.
-/
theorem UniformSpace.completelyNormalSpace_of_hasAntitoneBasis {ι : Type*} [LinearOrder ι]
    {B : ι → SetRel α α} (hB : (uniformity α).HasAntitoneBasis B) : CompletelyNormalSpace α where
  completely_normal s t hSt hsT := by
    let S (b : Bool) : Set α := b.casesOn (false := s) (true := t)
    have hx (b : Bool) (x : S b) : ∃ i, Disjoint (ball x.1 ((B i).comp (B i).inv)) (S (!b)) := by
      have hST : Disjoint (S b) (closure (S !b)) := b.casesOn (false := hsT) (true := hSt.symm)
      rw [← disjoint_nhdsSet_principal, disjoint_principal_right] at hST
      obtain ⟨U, hUu, hU⟩ := UniformSpace.mem_nhds_iff.1 (nhds_le_nhdsSet x.2 hST)
      obtain ⟨(V : SetRel α α), hV, hVs, hVU⟩ := comp_symm_mem_uniformity_sets hUu
      obtain ⟨i, hi⟩ := hB.mem_iff.1 hV
      refine ⟨i, subset_compl_iff_disjoint_right.1 (subset_trans (ball_mono ?_ x.1) hU)⟩
      exact subset_trans (SetRel.comp_subset_comp hi (V.inv_eq_self ▸ (SetRel.inv_mono hi))) hVU
    choose U hU using hx
    have hUS (b : Bool) : ⋃ x, ball x.1 (B (U b x)) ∈ nhdsSet (S b) := by
      rw [mem_nhdsSet_iff_forall]
      intro x hx
      apply mem_of_superset (ball_mem_nhds x (hB.mem (U b ⟨x, hx⟩)))
      exact subset_iUnion (fun x => ball x.1 (B (U b x))) ⟨x, hx⟩
    rw [Filter.disjoint_iff]
    refine ⟨_, hUS false, _, hUS true, ?_⟩
    have hdj (b : Bool) (x : S b) (y : S (!b)) (hxy : U b x ≤ U (!b) y) :
        Disjoint (ball x.1 (B (U b x))) (ball y.1 (B (U (!b) y))) := by
      rw [Set.disjoint_iff]
      intro z hz
      exact (hU b x).notMem_of_mem_left (mem_ball_comp hz.1 (hB.antitone hxy hz.2)) y.2
    simp_rw [disjoint_iUnion_left, disjoint_iUnion_right]
    intro x y
    exact (le_total (U false x) (U true y)).elim
      (fun h => hdj false x y h) (fun h => (hdj true y x h).symm)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity
    [(uniformity α).IsCountablyGenerated] : CompletelyNormalSpace α :=
  (has_seq_basis α).elim fun _ hB =>
    UniformSpace.completelyNormalSpace_of_hasAntitoneBasis hB.1
/-
**Filter.HasBasis.specializes_iff_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.specializes_iff_uniformity {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set (α × α)} (h : (𝓤 α).HasBasis p s) {x y : α} : x ⤳ y ↔ forall i, p i -
> (x, y) in s i
参数：α × α；h : (𝓤 α).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.specializes_iff`：Filter.HasBasis.specializes_iff {ι} {p 
: ι -> Prop} {s : ι -> Set X} (h : (𝓝 y).HasBasis p s) : x ⤳ y ↔ forall i, p i -
> x in s i
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
-/
theorem Filter.HasBasis.specializes_iff_uniformity {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {x y : α} : x ⤳ y ↔ ∀ i, p i → (x, y) ∈ s i :=
  (nhds_basis_uniformity h).specializes_iff
/-
**Filter.HasBasis.inseparable_iff_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.inseparable_iff_uniformity {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set (α × α)} (h : (𝓤 α).HasBasis p s) {x y : α} : Inseparable x y ↔ foral
l i, p i -> (x, y) in s i
参数：α × α；h : (𝓤 α).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `specializes_iff_inseparable`：specializes_iff_inseparable : x ⤳ y ↔ Insep
arable x y
· 使用定理 `instR0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space X], R
0Space X
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `Filter.HasBasis.specializes_iff_uniformity`：Filter.HasBasis.specializes_
iff_uniformity {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)} (h : (𝓤 α).Has
Basis p s) {x y : α} : x ⤳ y ↔ f…
-/
theorem Filter.HasBasis.inseparable_iff_uniformity {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {x y : α} : Inseparable x y ↔ ∀ i, p i → (x, y) ∈ s i :=
  specializes_iff_inseparable.symm.trans h.specializes_iff_uniformity
/-
**inseparable_iff_ker_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inseparable_iff_ker_uniformity {x y : α} : Inseparable x y ↔ (x, y) in (𝓤 
α).ker
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.inseparable_iff_uniformity`：Filter.HasBasis.inseparable_
iff_uniformity {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)} (h : (𝓤 α).Has
Basis p s) {x y : α} : Inseparab…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem inseparable_iff_ker_uniformity {x y : α} : Inseparable x y ↔ (x, y) ∈ (𝓤 α).ker :=
  (𝓤 α).basis_sets.inseparable_iff_uniformity
/-
**Inseparable.nhds_le_uniformity** 是 Mathlib 中的一个定理，位于命名空间 `Inseparable`。
形式化陈述：∀ {α : Type u} [inst : UniformSpace α] {x y : α}, Inseparable x y → nhds (
x, y) ≤ uniformity α
参数：x, y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Inseparable.prod`：Inseparable.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ᵢ x
₂) (hy : y₁ ~ᵢ y₂) : (x₁, y₁) ~ᵢ (x₂, y₂)
· 使用定理 `Inseparable.rfl`：rfl : x ~ᵢ x
· 使用定理 `nhds_le_uniformity`：nhds_le_uniformity (x : α) : 𝓝 (x, x) <= 𝓤 α
-/
protected theorem Inseparable.nhds_le_uniformity {x y : α} (h : Inseparable x y) :
    𝓝 (x, y) ≤ 𝓤 α := by
  rw [h.prod rfl]
  apply nhds_le_uniformity
/-
**inseparable_iff_clusterPt_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inseparable_iff_clusterPt_uniformity {x y : α} : Inseparable x y ↔ Cluster
Pt (x, y) (𝓤 α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.of_nhds_le`：ClusterPt.of_nhds_le {f : Filter X} (H : 𝓝 x <= f)
 : ClusterPt x f
· 使用定理 `Inseparable.nhds_le_uniformity`：∀ {α : Type u} [inst : UniformSpace α] {
x y : α}, Inseparable x y → nhds (x, y) ≤ uniformity α
· 使用定理 `Filter.HasBasis.inseparable_iff_uniformity`：Filter.HasBasis.inseparable_
iff_uniformity {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)} (h : (𝓤 α).Has
Basis p s) {x y : α} : Inseparab…
· 使用定理 `uniformity_hasBasis_closed`：uniformity_hasBasis_closed : HasBasis (𝓤 α) 
(fun V : SetRel α α => V in 𝓤 α ∧ IsClosed V) id
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
-/
theorem inseparable_iff_clusterPt_uniformity {x y : α} :
    Inseparable x y ↔ ClusterPt (x, y) (𝓤 α) := by
  refine ⟨fun h ↦ .of_nhds_le h.nhds_le_uniformity, fun h ↦ ?_⟩
  simp_rw [uniformity_hasBasis_closed.inseparable_iff_uniformity, isClosed_iff_clusterPt]
  exact fun U ⟨hU, hUc⟩ ↦ hUc _ <| h.mono <| le_principal_iff.2 hU
/-
**t0Space_iff_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t0Space_iff_uniformity : T0Space α ↔ forall x y, (forall r in 𝓤 α, (x, y) 
in r) -> x = y
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem t0Space_iff_uniformity :
    T0Space α ↔ ∀ x y, (∀ r ∈ 𝓤 α, (x, y) ∈ r) → x = y := by
  simp only [t0Space_iff_inseparable, inseparable_iff_ker_uniformity, mem_ker]
/-
**t0Space_iff_uniformity'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t0Space_iff_uniformity' : T0Space α ↔ Pairwise fun x y => exists r in 𝓤 α,
 (x, y) ∉ r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem t0Space_iff_uniformity' :
    T0Space α ↔ Pairwise fun x y ↦ ∃ r ∈ 𝓤 α, (x, y) ∉ r := by
  simp [t0Space_iff_not_inseparable, inseparable_iff_ker_uniformity]
/-
**t0Space_iff_ker_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t0Space_iff_ker_uniformity : T0Space α ↔ (𝓤 α).ker = diagonal α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `refl_mem_uniformity`：refl_mem_uniformity {x : α} {s : SetRel α α} (h : s
 in 𝓤 α) : (x, x) in s
-/
theorem t0Space_iff_ker_uniformity : T0Space α ↔ (𝓤 α).ker = diagonal α := by
  simp_rw [t0Space_iff_uniformity, subset_antisymm_iff, diagonal_subset_iff, subset_def,
    Prod.forall, Filter.mem_ker, mem_diagonal_iff, iff_self_and]
  exact fun _ x s hs ↦ refl_mem_uniformity hs
/-
**eq_of_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_uniformity {α : Type*} [UniformSpace α] [T0Space α] {x y : α} (h : f
orall {V}, V in 𝓤 α -> (x, y) in V) : x = y
参数：h : forall {V}, V in 𝓤 α -> (x, y) in V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `t0Space_iff_uniformity`：t0Space_iff_uniformity : T0Space α ↔ forall x y,
 (forall r in 𝓤 α, (x, y) in r) -> x = y
-/
theorem eq_of_uniformity {α : Type*} [UniformSpace α] [T0Space α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → (x, y) ∈ V) : x = y :=
  t0Space_iff_uniformity.mp ‹T0Space α› x y @h
/-
**eq_of_uniformity_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_uniformity_basis {α : Type*} [UniformSpace α] [T0Space α] {ι : Sort*
} {p : ι -> Prop} {s : ι -> Set (α × α)} (hs : (𝓤 α).HasBasis p s) {x y : α} (h 
: forall {i}, p i -> (x, y) in s i) : x = y
参数：α × α；hs : (𝓤 α).HasBasis p s；h : forall {i}, p i -> (x, y) in s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.inseparable_iff_uniformity`：Filter.HasBasis.inseparable_
iff_uniformity {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)} (h : (𝓤 α).Has
Basis p s) {x y : α} : Inseparab…
-/
theorem eq_of_uniformity_basis {α : Type*} [UniformSpace α] [T0Space α] {ι : Sort*}
    {p : ι → Prop} {s : ι → Set (α × α)} (hs : (𝓤 α).HasBasis p s) {x y : α}
    (h : ∀ {i}, p i → (x, y) ∈ s i) : x = y :=
  (hs.inseparable_iff_uniformity.2 @h).eq
/-
**eq_of_forall_symmetric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_forall_symmetric {α : Type*} [UniformSpace α] [T0Space α] {x y : α} 
(h : forall {V}, V in 𝓤 α -> SetRel.IsSymm V -> (x, y) in V) : x = y
参数：h : forall {V}, V in 𝓤 α -> SetRel.IsSymm V -> (x, y) in V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_uniformity_basis`：eq_of_uniformity_basis {α : Type*} [UniformSpace
 α] [T0Space α] {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)} (hs : (𝓤 α).H
asBasis p s)…
· 使用定理 `UniformSpace.hasBasis_symmetric`：UniformSpace.hasBasis_symmetric : (𝓤 α)
.HasBasis (fun s : SetRel α α => s in 𝓤 α ∧ SetRel.IsSymm s) id
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem eq_of_forall_symmetric {α : Type*} [UniformSpace α] [T0Space α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → SetRel.IsSymm V → (x, y) ∈ V) : x = y :=
  eq_of_uniformity_basis hasBasis_symmetric (by simpa)
/-
**eq_of_clusterPt_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_clusterPt_uniformity [T0Space α] {x y : α} (h : ClusterPt (x, y) (𝓤 
α)) : x = y
参数：h : ClusterPt (x, y) (𝓤 α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inseparable_iff_clusterPt_uniformity`：inseparable_iff_clusterPt_uniformi
ty {x y : α} : Inseparable x y ↔ ClusterPt (x, y) (𝓤 α)
-/
theorem eq_of_clusterPt_uniformity [T0Space α] {x y : α} (h : ClusterPt (x, y) (𝓤 α)) : x = y :=
  (inseparable_iff_clusterPt_uniformity.2 h).eq
/-
**Filter.Tendsto.inseparable_iff_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.inseparable_iff_uniformity {β} {l : Filter β} [NeBot l] {f 
g : β -> α} {a b : α} (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) : Insepa
rable a b ↔ Tendsto (fun x => (f x, g x)) l (𝓤 α)
参数：ha : Tendsto f l (𝓝 a)；hb : Tendsto g l (𝓝 b)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
· 使用定理 `Inseparable.nhds_le_uniformity`：∀ {α : Type u} [inst : UniformSpace α] {
x y : α}, Inseparable x y → nhds (x, y) ≤ uniformity α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inseparable_iff_clusterPt_uniformity`：inseparable_iff_clusterPt_uniformi
ty {x y : α} : Inseparable x y ↔ ClusterPt (x, y) (𝓤 α)
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `ClusterPt.of_le_nhds`：ClusterPt.of_le_nhds {f : Filter X} (H : f <= 𝓝 x)
 [NeBot f] : ClusterPt x f
-/
theorem Filter.Tendsto.inseparable_iff_uniformity {β} {l : Filter β} [NeBot l] {f g : β → α}
    {a b : α} (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) :
    Inseparable a b ↔ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α) := by
  refine ⟨fun h ↦ (ha.prodMk_nhds hb).mono_right h.nhds_le_uniformity, fun h ↦ ?_⟩
  rw [inseparable_iff_clusterPt_uniformity]
  exact (ClusterPt.of_le_nhds (ha.prodMk_nhds hb)).mono h
/-
**isClosed_of_spaced_out** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_of_spaced_out [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ in 𝓤 α) 
{s : Set α} (hs : s.Pairwise fun x y => (x, y) ∉ V₀) : IsClosed s
参数：α × α；V₀_in : V₀ in 𝓤 α；hs : s.Pairwise fun x y => (x, y) ∉ V₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用定理 `isClosed_of_closure_subset`：isClosed_of_closure_subset (h : closure s su
bseteq s) : IsClosed s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.mem_closure_iff_ball`：UniformSpace.mem_closure_iff_ball {s 
: Set α} {x} : x in closure s ↔ forall {V}, V in 𝓤 α -> (ball x V inter s).Nonem
pty
· 使用定理 `eq_of_forall_symmetric`：eq_of_forall_symmetric {α : Type*} [UniformSpace
 α] [T0Space α] {x y : α} (h : forall {V}, V in 𝓤 α -> SetRel.IsSymm V -> (x, y)
 in V) : x =…
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `UniformSpace.ball_inter_right`：ball_inter_right (x : β) (V W : Set (β × 
β)) : ball x (V inter W) subseteq ball x W
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `UniformSpace.mem_comp_of_mem_ball`：mem_comp_of_mem_ball {V W : SetRel β 
β} {x y z : β} [V.IsSymm] (hx : x in ball z V) (hy : y in ball z W) : (x, y) in 
V ○ W
· 使用定理 `UniformSpace.ball_inter_left`：ball_inter_left (x : β) (V W : Set (β × β)
) : ball x (V inter W) subseteq ball x V
-/
theorem isClosed_of_spaced_out [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α) {s : Set α}
    (hs : s.Pairwise fun x y => (x, y) ∉ V₀) : IsClosed s := by
  rcases comp_symm_mem_uniformity_sets V₀_in with ⟨V₁, V₁_in, V₁_symm, h_comp⟩
  apply isClosed_of_closure_subset
  intro x hx
  rw [mem_closure_iff_ball] at hx
  rcases hx V₁_in with ⟨y, hy, hy'⟩
  suffices x = y by rwa [this]
  apply eq_of_forall_symmetric
  intro V V_in _
  rcases hx (inter_mem V₁_in V_in) with ⟨z, hz, hz'⟩
  obtain rfl : z = y := by
    by_contra hzy
    exact hs hz' hy' hzy (h_comp <| mem_comp_of_mem_ball (ball_inter_left x _ _ hz) hy)
  exact ball_inter_right x _ _ hz
/-
**isClosed_range_of_spaced_out** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_range_of_spaced_out {ι} [T0Space α] {V₀ : Set (α × α)} (V₀_in : V
₀ in 𝓤 α) {f : ι -> α} (hf : Pairwise fun x y => (f x, f y) ∉ V₀) : IsClosed (ra
nge f)
参数：α × α；V₀_in : V₀ in 𝓤 α；hf : Pairwise fun x y => (f x, f y) ∉ V₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_of_spaced_out`：isClosed_of_spaced_out [T0Space α] {V₀ : Set (α 
× α)} (V₀_in : V₀ in 𝓤 α) {s : Set α} (hs : s.Pairwise fun x y => (x, y) ∉ V₀) :
 IsClosed s
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
theorem isClosed_range_of_spaced_out {ι} [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α)
    {f : ι → α} (hf : Pairwise fun x y => (f x, f y) ∉ V₀) : IsClosed (range f) :=
  isClosed_of_spaced_out V₀_in <| by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    exact hf (ne_of_apply_ne f h)

/-!
### Separation quotient
-/

namespace SeparationQuotient

/-
**SeparationQuotient.comap_map_mk_uniformity** 是 Mathlib 中的一个定理，位于命名空间 `Separati
onQuotient`。
形式化陈述：comap_map_mk_uniformity : comap (Prod.map mk mk) (map (Prod.map mk mk) (𝓤 
α)) = 𝓤 α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `uniformity_hasBasis_open`：uniformity_hasBasis_open : HasBasis (𝓤 α) (fun
 V : SetRel α α => V in 𝓤 α ∧ IsOpen V) id
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Inseparable.mem_open_iff`：mem_open_iff (h : x ~ᵢ y) (hs : IsOpen s) : x 
in s ↔ y in s
· 使用定理 `Inseparable.prod`：Inseparable.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ᵢ x
₂) (hy : y₁ ~ᵢ y₂) : (x₁, y₁) ~ᵢ (x₂, y₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.le_comap_map`：le_comap_map : f <= comap m (map m f)
-/
theorem comap_map_mk_uniformity : comap (Prod.map mk mk) (map (Prod.map mk mk) (𝓤 α)) = 𝓤 α := by
  refine le_antisymm ?_ le_comap_map
  refine ((((𝓤 α).basis_sets.map _).comap _).le_basis_iff uniformity_hasBasis_open).2 fun U hU ↦ ?_
  refine ⟨U, hU.1, fun (x₁, x₂) ⟨(y₁, y₂), hyU, hxy⟩ ↦ ?_⟩
  simp only [Prod.map, Prod.ext_iff, mk_eq_mk] at hxy
  exact ((hxy.1.prod hxy.2).mem_open_iff hU.2).1 hyU
/-
**SeparationQuotient.instUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuoti
ent`。
形式化陈述：instUniformSpace : UniformSpace (SeparationQuotient α) where uniformity
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniformSpace : UniformSpace (SeparationQuotient α) where
  uniformity := map (Prod.map mk mk) (𝓤 α)
  symm := tendsto_map' <| tendsto_map.comp tendsto_swap_uniformity
  comp := fun t ht ↦ by
    rcases comp_open_symm_mem_uniformity_sets ht with ⟨U, hU, hUo, -, hUt⟩
    refine mem_of_superset (mem_lift' <| image_mem_map hU) ?_
    simp only [subset_def, Prod.forall, SetRel.mem_comp, mem_image, Prod.ext_iff]
    rintro _ _ ⟨_, ⟨⟨x, y⟩, hxyU, rfl, rfl⟩, ⟨⟨y', z⟩, hyzU, hy, rfl⟩⟩
    have : y' ⤳ y := (mk_eq_mk.1 hy).specializes
    exact @hUt (x, z) ⟨y', this.mem_open (UniformSpace.isOpen_ball _ hUo) hxyU, hyzU⟩
  nhds_eq_comap_uniformity := surjective_mk.forall.2 fun x ↦ comap_injective surjective_mk <| by
    conv_lhs => rw [comap_mk_nhds_mk, nhds_eq_comap_uniformity, ← comap_map_mk_uniformity]
    simp only [Filter.comap_comap, Function.comp_def, Prod.map_apply]
/-
**SeparationQuotient.uniformity_eq** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient
`。
形式化陈述：uniformity_eq : 𝓤 (SeparationQuotient α) = (𝓤 α).map (Prod.map mk mk)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformity_eq : 𝓤 (SeparationQuotient α) = (𝓤 α).map (Prod.map mk mk) := rfl

@[fun_prop]
/-
**SeparationQuotient.uniformContinuous_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQ
uotient`。
形式化陈述：uniformContinuous_mk : UniformContinuous (mk : α -> SeparationQuotient α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem uniformContinuous_mk : UniformContinuous (mk : α → SeparationQuotient α) :=
  le_rfl
/-
**SeparationQuotient.uniformContinuous_dom** 是 Mathlib 中的一个定理，位于命名空间 `Separation
Quotient`。
形式化陈述：uniformContinuous_dom {f : SeparationQuotient α -> β} : UniformContinuous 
f ↔ UniformContinuous (f ∘ mk)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniformContinuous_dom {f : SeparationQuotient α → β} :
    UniformContinuous f ↔ UniformContinuous (f ∘ mk) :=
  .rfl
/-
**SeparationQuotient.uniformContinuous_dom** 是 Mathlib 中的一个定理，位于命名空间 `Separation
Quotient`。
形式化陈述：uniformContinuous_dom {f : SeparationQuotient α -> β} : UniformContinuous 
f ↔ UniformContinuous (f ∘ mk)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniformContinuous_dom₂ {f : SeparationQuotient α × SeparationQuotient β → γ} :
    UniformContinuous f ↔ UniformContinuous fun p : α × β ↦ f (mk p.1, mk p.2) := by
  simp only [UniformContinuous, uniformity_prod_eq_prod, uniformity_eq, prod_map_map_eq,
    tendsto_map'_iff]
  rfl
/-
**SeparationQuotient.uniformContinuous_lift** 是 Mathlib 中的一个定理，位于命名空间 `Separatio
nQuotient`。
形式化陈述：uniformContinuous_lift {f : α -> β} (h : forall a b, Inseparable a b -> f 
a = f b) : UniformContinuous (lift f h) ↔ UniformContinuous f
参数：h : forall a b, Inseparable a b -> f a = f b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniformContinuous_lift {f : α → β} (h : ∀ a b, Inseparable a b → f a = f b) :
    UniformContinuous (lift f h) ↔ UniformContinuous f :=
  .rfl
/-
**SeparationQuotient.uniformContinuous_uncurry_lift** 是 Mathlib 中的一个定理，位于命名空间 `S
eparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformContinuous_uncurry_lift₂ {f : α → β → γ}
    (h : ∀ a c b d, Inseparable a b → Inseparable c d → f a c = f b d) :
    UniformContinuous (uncurry <| lift₂ f h) ↔ UniformContinuous (uncurry f) :=
  uniformContinuous_dom₂
/-
**SeparationQuotient.comap_mk_uniformity** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQu
otient`。
形式化陈述：comap_mk_uniformity : (𝓤 (SeparationQuotient α)).comap (Prod.map mk mk) = 
𝓤 α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.comap_map_mk_uniformity`：comap_map_mk_uniformity : co
map (Prod.map mk mk) (map (Prod.map mk mk) (𝓤 α)) = 𝓤 α
-/
theorem comap_mk_uniformity : (𝓤 (SeparationQuotient α)).comap (Prod.map mk mk) = 𝓤 α :=
  comap_map_mk_uniformity

open scoped Classical in
/-- Factoring functions to a separated space through the separation quotient.

TODO: unify with `SeparationQuotient.lift`. -/
/-
**SeparationQuotient.lift'** 是 Mathlib 中的一个定义，位于命名空间 `SeparationQuotient`。
形式化陈述：lift' [T0Space β] (f : α -> β) : SeparationQuotient α -> β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Factoring functions to a separated space through the separation quotient.

TODO: unify with `SeparationQuotient.lift`.
-/
def lift' [T0Space β] (f : α → β) : SeparationQuotient α → β :=
  if hc : UniformContinuous f then lift f fun _ _ h => (h.map hc.continuous).eq
  else fun x => f (Nonempty.some ⟨x.out⟩)
/-
**SeparationQuotient.lift'_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : UniformSpace α] [inst_1 : UniformSpace
 β] [inst_2 : T0Space β] {f : α → β},   UniformContinuous f → ∀ (a : α), Separat
ionQuotient.lift' f (SeparationQuotient.mk a) = f a
参数：a : α；SeparationQuotient.mk a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeparationQuotient.lift'.eq_1`：∀ {α : Type u} {β : Type v} [inst : Unifo
rmSpace α] [inst_1 : UniformSpace β] [inst_2 : T0Space β] (f : α → β),   Separat
ionQuotient.lift' f…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `SeparationQuotient.lift_mk`：lift_mk {f : X -> α} (hf : forall x y, (x ~ᵢ
 y) -> f x = f y) (x : X) : lift f hf (mk x) = f x
-/
theorem lift'_mk [T0Space β] {f : α → β} (h : UniformContinuous f) (a : α) :
    lift' f (mk a) = f a := by rw [lift', dif_pos h, lift_mk]

@[fun_prop]
/-
**SeparationQuotient.uniformContinuous_lift'** 是 Mathlib 中的一个定理，位于命名空间 `Separati
onQuotient`。
形式化陈述：uniformContinuous_lift' [T0Space β] (f : α -> β) : UniformContinuous (lift
' f)
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeparationQuotient.lift'.eq_1`：∀ {α : Type u} {β : Type v} [inst : Unifo
rmSpace α] [inst_1 : UniformSpace β] [inst_2 : T0Space β] (f : α → β),   Separat
ionQuotient.lift' f…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `SeparationQuotient.uniformContinuous_lift`：uniformContinuous_lift {f : α
 -> β} (h : forall a b, Inseparable a b -> f a = f b) : UniformContinuous (lift 
f h) ↔ UniformContinuous f
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `uniformContinuous_of_const`：uniformContinuous_of_const {c : α -> β} (h :
 forall a b, c a = c b) : UniformContinuous c
-/
theorem uniformContinuous_lift' [T0Space β] (f : α → β) : UniformContinuous (lift' f) := by
  by_cases hf : UniformContinuous f
  · rwa [lift', dif_pos hf, uniformContinuous_lift]
  · rw [lift', dif_neg hf]
    exact uniformContinuous_of_const fun a _ => rfl

/-- The separation quotient functor acting on functions. -/
/-
**SeparationQuotient.map** 是 Mathlib 中的一个定义，位于命名空间 `SeparationQuotient`。
形式化陈述：map (f : α -> β) : SeparationQuotient α -> SeparationQuotient β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The separation quotient functor acting on functions.
-/
def map (f : α → β) : SeparationQuotient α → SeparationQuotient β := lift' (mk ∘ f)
/-
**SeparationQuotient.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：map_mk {f : α -> β} (h : UniformContinuous f) (a : α) : map f (mk a) = mk 
(f a)
参数：h : UniformContinuous f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeparationQuotient.map.eq_1`：∀ {α : Type u} {β : Type v} [inst : Uniform
Space α] [inst_1 : UniformSpace β] (f : α → β),   SeparationQuotient.map f = Sep
arationQuotient.l…
· 使用定理 `SeparationQuotient.lift'_mk`：∀ {α : Type u} {β : Type v} [inst : Uniform
Space α] [inst_1 : UniformSpace β] [inst_2 : T0Space β] {f : α → β},   UniformCo
ntinuous f → ∀ (a…
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `SeparationQuotient.uniformContinuous_mk`：uniformContinuous_mk : UniformC
ontinuous (mk : α -> SeparationQuotient α)
-/
theorem map_mk {f : α → β} (h : UniformContinuous f) (a : α) : map f (mk a) = mk (f a) := by
  rw [map, lift'_mk (uniformContinuous_mk.comp h)]; rfl

@[fun_prop]
/-
**SeparationQuotient.uniformContinuous_map** 是 Mathlib 中的一个定理，位于命名空间 `Separation
Quotient`。
形式化陈述：uniformContinuous_map (f : α -> β) : UniformContinuous (map f)
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.uniformContinuous_lift'`：uniformContinuous_lift' [T0S
pace β] (f : α -> β) : UniformContinuous (lift' f)
-/
theorem uniformContinuous_map (f : α → β) : UniformContinuous (map f) :=
  uniformContinuous_lift' _

set_option backward.isDefEq.respectTransparency false in
/-
**SeparationQuotient.map_unique** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：map_unique {f : α -> β} (hf : UniformContinuous f) {g : SeparationQuotient
 α -> SeparationQuotient β} (comm : mk ∘ f = g ∘ mk) : map f = g
参数：hf : UniformContinuous f；comm : mk ∘ f = g ∘ mk。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SeparationQuotient.map_mk`：map_mk {f : α -> β} (h : UniformContinuous f)
 (a : α) : map f (mk a) = mk (f a)
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem map_unique {f : α → β} (hf : UniformContinuous f)
    {g : SeparationQuotient α → SeparationQuotient β} (comm : mk ∘ f = g ∘ mk) : map f = g := by
  ext ⟨a⟩
  calc
    map f ⟦a⟧ = ⟦f a⟧ := map_mk hf a
    _ = g ⟦a⟧ := congr_fun comm a

@[simp]
/-
**SeparationQuotient.map_id** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：map_id : map (@id α) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.map_unique`：map_unique {f : α -> β} (hf : UniformCont
inuous f) {g : SeparationQuotient α -> SeparationQuotient β} (comm : mk ∘ f = g 
∘ mk) : map f = g
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem map_id : map (@id α) = id := map_unique uniformContinuous_id rfl
/-
**SeparationQuotient.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：map_comp {f : α -> β} {g : β -> γ} (hf : UniformContinuous f) (hg : Unifor
mContinuous g) : map g ∘ map f = map (g ∘ f)
参数：hf : UniformContinuous f；hg : UniformContinuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeparationQuotient.map_unique`：map_unique {f : α -> β} (hf : UniformCont
inuous f) {g : SeparationQuotient α -> SeparationQuotient β} (comm : mk ∘ f = g 
∘ mk) : map f = g
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SeparationQuotient.map_mk`：map_mk {f : α -> β} (h : UniformContinuous f)
 (a : α) : map f (mk a) = mk (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp {f : α → β} {g : β → γ} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    map g ∘ map f = map (g ∘ f) :=
  (map_unique (hg.comp hf) <| by simp only [Function.comp_def, map_mk, hf, hg]).symm

end SeparationQuotient

namespace IndiscreteTopology

variable {α : Type*} [u : UniformSpace α]

/-
**IndiscreteTopology.of_uniformity_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `IndiscreteT
opology`。
形式化陈述：of_uniformity_eq_top (h : uniformity α = ⊤) : IndiscreteTopology α
参数：h : uniformity α = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem of_uniformity_eq_top (h : uniformity α = ⊤) : IndiscreteTopology α :=
  ⟨(UniformSpace.ext h.symm : ⊤ = u) ▸ rfl⟩
/-
**IndiscreteTopology.eq_top_uniformSpace** 是 Mathlib 中的一个引理，位于命名空间 `IndiscreteTo
pology`。
形式化陈述：eq_top_uniformSpace [IndiscreteTopology α] : u = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `top_uniformity`：top_uniformity : 𝓤[(⊤ : UniformSpace α)] = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.ker_eq_univ`：∀ {α : Type u_2} {f : Filter α}, f.ker = Set.univ ↔ 
f = ⊤
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `inseparable_iff_ker_uniformity`：inseparable_iff_ker_uniformity {x y : α}
 : Inseparable x y ↔ (x, y) in (𝓤 α).ker
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma eq_top_uniformSpace [IndiscreteTopology α] : u = ⊤ := by
  refine UniformSpace.ext ?_
  rw [top_uniformity, ← Filter.ker_eq_univ]
  ext x
  rw [← inseparable_iff_ker_uniformity]
  simp
/-
**IndiscreteTopology.eq_top_iff_indiscrete** 是 Mathlib 中的一个引理，位于命名空间 `Indiscrete
Topology`。
形式化陈述：eq_top_iff_indiscrete : u = ⊤ ↔ IndiscreteTopology α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.toTopologicalSpace_top`：toTopologicalSpace_top : @UniformSp
ace.toTopologicalSpace α ⊤ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IndiscreteTopology.eq_top_uniformSpace`：eq_top_uniformSpace [IndiscreteT
opology α] : u = ⊤
-/
lemma eq_top_iff_indiscrete : u = ⊤ ↔ IndiscreteTopology α :=
  ⟨fun h ↦ IndiscreteTopology.mk <| h ▸ UniformSpace.toTopologicalSpace_top (α := α),
  fun _ ↦ eq_top_uniformSpace⟩

@[fun_prop]
/-
**IndiscreteTopology.uniformContinuous** 是 Mathlib 中的一个引理，位于命名空间 `IndiscreteTopo
logy`。
形式化陈述：uniformContinuous [IndiscreteTopology β] {f : α -> β} : UniformContinuous 
f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformContinuous.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (f : α → β),   UniformContinuous f = Filter.Tend
sto (fun x =…
· 使用引理 `IndiscreteTopology.eq_top_uniformSpace`：eq_top_uniformSpace [IndiscreteT
opology α] : u = ⊤
· 使用引理 `top_uniformity`：top_uniformity : 𝓤[(⊤ : UniformSpace α)] = ⊤
· 使用定理 `Filter.tendsto_top`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : Fil
ter α}, Filter.Tendsto f l ⊤
-/
lemma uniformContinuous [IndiscreteTopology β] {f : α → β} : UniformContinuous f := by
  rw [UniformContinuous, eq_top_uniformSpace (α := β), top_uniformity]
  exact Filter.tendsto_top

end IndiscreteTopology

