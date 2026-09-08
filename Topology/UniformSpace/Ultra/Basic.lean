/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.Bases

/-!
# Ultrametric (nonarchimedean) uniform spaces

Ultrametric (nonarchimedean) uniform spaces are ones that generalize ultrametric spaces by
having a uniformity based on equivalence relations.

## Main definitions

In this file we define `IsUltraUniformity`, a Prop mixin typeclass.

## Main results

* `TopologicalSpace.isTopologicalBasis_clopens`: a uniform space with a nonarchimedean uniformity
  has a topological basis of clopen sets in the topology, meaning that it is topologically
  zero-dimensional.

## Implementation notes

As in the `Mathlib/Topology/UniformSpace/Defs.lean` file, we do not reuse `Mathlib/Data/Rel.lean`
but rather extend the relation properties as needed.

## TODOs

* Prove that `IsUltraUniformity` iff metrizable by `IsUltrametricDist` on a `PseudoMetricSpace`
  under a countable system/basis condition
* Generalize `IsUltrametricDist` to `IsUltrametricUniformity`
* Provide `IsUltraUniformity` for the uniformity in a `Valued` ring
* Generalize results about open/closed balls and spheres in `IsUltraUniformity` to
  combine applications for `MetricSpace.ball` and valued "balls"
* Use `IsUltraUniformity` to work with profinite/totally separated spaces

## References

* [D. Windisch, *Equivalent characterizations of non-Archimedean uniform spaces*][windisch2021]
* [A. C. M. van Rooij, *Non-Archimedean uniformities*][vanrooij1970]

-/

@[expose] public section

open Set Filter Topology
open scoped SetRel Uniformity

variable {X : Type*}

/-
**IsTransitiveRel.prod_subset_trans** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsTransitiveRel.prod_subset_trans {s : SetRel X X} {t u v : Set X} [s.IsTr
ans] (htu : t ×ˢ u subseteq s) (huv : u ×ˢ v subseteq s) (hu : u.Nonempty) : t ×
ˢ v subseteq s
参数：htu : t ×ˢ u subseteq s；huv : u ×ˢ v subseteq s；hu : u.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.trans`：∀ {α : Type u_1} (R : SetRel α α) {a b c : α} [R.IsTrans],
 (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsTransitiveRel.prod_subset_trans {s : SetRel X X} {t u v : Set X} [s.IsTrans]
    (htu : t ×ˢ u ⊆ s) (huv : u ×ˢ v ⊆ s) (hu : u.Nonempty) :
    t ×ˢ v ⊆ s := by
  rintro ⟨a, b⟩ hab
  simp only [mem_prod] at hab
  obtain ⟨x, hx⟩ := hu
  exact s.trans (@htu ⟨a, x⟩ ⟨hab.left, hx⟩) (@huv ⟨x, b⟩ ⟨hx, hab.right⟩)
/-
**IsTransitiveRel.mem_filter_prod_trans** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsTransitiveRel.mem_filter_prod_trans {s : SetRel X X} {f g h : Filter X} 
[g.NeBot] [s.IsTrans] (hfg : s in f ×ˢ g) (hgh : s in g ×ˢ h) : s in f ×ˢ h
参数：hfg : s in f ×ˢ g；hgh : s in g ×ˢ h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.trans_prod`：∀ {α : Type u_1} {β : Type u_2} {γ : Type 
u_3} {f : Filter α} {g : Filter β} {h : Filter γ} [g.NeBot] {p : α → β → Prop}  
 {q : β → γ → Prop…
· 使用定理 `SetRel.trans`：∀ {α : Type u_1} (R : SetRel α α) {a b c : α} [R.IsTrans],
 (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R
-/
lemma IsTransitiveRel.mem_filter_prod_trans {s : SetRel X X} {f g h : Filter X} [g.NeBot]
    [s.IsTrans] (hfg : s ∈ f ×ˢ g) (hgh : s ∈ g ×ˢ h) :
    s ∈ f ×ˢ h :=
  Eventually.trans_prod (p := (fun x y ↦ (x, y) ∈ s)) (q := (fun x y ↦ (x, y) ∈ s))
    (r := (fun x y ↦ (x, y) ∈ s)) hfg hgh fun _ _ _ ↦ s.trans

open UniformSpace
/-
**ball_subset_of_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ball_subset_of_mem {V : SetRel X X} [V.IsTrans] {x y : X} (hy : y in ball 
x V) : ball y V subseteq ball x V
参数：hy : y in ball x V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ball_subset_of_comp_subset`：ball_subset_of_comp_subset {V W
 : Set (β × β)} {x y} (h : x in ball y W) (h' : W ○ W subseteq V) : ball x W sub
seteq ball y V
· 使用引理 `SetRel.comp_subset_self`：comp_subset_self [R.IsTrans] : R ○ R subseteq R
-/
lemma ball_subset_of_mem {V : SetRel X X} [V.IsTrans] {x y : X} (hy : y ∈ ball x V) :
    ball y V ⊆ ball x V :=
  ball_subset_of_comp_subset hy SetRel.comp_subset_self
/-
**ball_eq_of_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ball_eq_of_mem {V : SetRel X X} [V.IsSymm] [V.IsTrans] {x y : X} (hy : y i
n ball x V) : ball x V = ball y V
参数：hy : y in ball x V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `ball_subset_of_mem`：ball_subset_of_mem {V : SetRel X X} [V.IsTrans] {x y
 : X} (hy : y in ball x V) : ball y V subseteq ball x V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniformSpace.mem_ball_symmetry`：mem_ball_symmetry {V : SetRel β β} [V.Is
Symm] {x y} : x in ball y V ↔ y in ball x V
-/
lemma ball_eq_of_mem {V : SetRel X X} [V.IsSymm] [V.IsTrans] {x y : X} (hy : y ∈ ball x V) :
    ball x V = ball y V := by
  refine le_antisymm (ball_subset_of_mem ?_) (ball_subset_of_mem hy)
  rwa [← mem_ball_symmetry]

variable [UniformSpace X]

variable (X) in
/-- A uniform space is ultrametric if the uniformity `𝓤 X` has a basis of equivalence relations. -/
/-
**IsUltraUniformity** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_1) → [UniformSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A uniform space is ultrametric if the uniformity `𝓤 X` has a basis of equivalenc
e relations.
-/
class IsUltraUniformity : Prop where
  hasBasis : (𝓤 X).HasBasis
    (fun s : SetRel X X => s ∈ 𝓤 X ∧ SetRel.IsSymm s ∧ SetRel.IsTrans s) id
/-
**IsUltraUniformity.mk_of_hasBasis** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUltraUniformity.mk_of_hasBasis {ι : Type*} {p : ι -> Prop} {s : ι -> Set
Rel X X} (h_basis : (𝓤 X).HasBasis p s) (h_symm : forall i, p i -> SetRel.IsSymm
 (s i)) (h_trans : forall i, p i -> SetRel.IsTrans (s i)) : IsUltraUniformity X 
where hasBasis
参数：h_basis : (𝓤 X).HasBasis p s；h_symm : forall i, p i -> SetRel.IsSymm (s i)；h_
trans : forall i, p i -> SetRel.IsTrans (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' 
→ Set α},   l.HasB…
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsUltraUniformity.mk_of_hasBasis {ι : Type*} {p : ι → Prop} {s : ι → SetRel X X}
    (h_basis : (𝓤 X).HasBasis p s) (h_symm : ∀ i, p i → SetRel.IsSymm (s i))
    (h_trans : ∀ i, p i → SetRel.IsTrans (s i)) :
    IsUltraUniformity X where
  hasBasis := h_basis.to_hasBasis'
    (fun i hi ↦ ⟨s i, ⟨h_basis.mem_of_mem hi, h_symm i hi, h_trans i hi⟩, subset_rfl⟩)
    (fun _ hs ↦ hs.1)
/-
**IsUltraUniformity.mem_nhds_iff_symm_trans** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUltraUniformity.mem_nhds_iff_symm_trans [IsUltraUniformity X] {x : X} {s
 : Set X} : s in 𝓝 x ↔ exists V in 𝓤 X, SetRel.IsSymm V ∧ SetRel.IsTrans V ∧ Uni
formSpace.ball x V subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.mem_nhds_iff`：UniformSpace.mem_nhds_iff {x : α} {s : Set α}
 : s in 𝓝 x ↔ exists V in 𝓤 α, ball x V subseteq s
· 使用定理 `Filter.HasBasis.mem_iff'`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (t : Set α), t ∈ l ↔ ∃ i, 
p i ∧ s i ⊆ t
· 使用定理 `IsUltraUniformity.hasBasis`：∀ {X : Type u_1} {inst : UniformSpace X} [se
lf : IsUltraUniformity X],   (uniformity X).HasBasis (fun s => s ∈ uniformity X 
∧ s.IsSymm ∧ s.I…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
-/
lemma IsUltraUniformity.mem_nhds_iff_symm_trans [IsUltraUniformity X] {x : X} {s : Set X} :
    s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 X, SetRel.IsSymm V ∧ SetRel.IsTrans V ∧ UniformSpace.ball x V ⊆ s := by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  · rintro ⟨V, V_in, V_sub⟩
    rw [IsUltraUniformity.hasBasis.mem_iff'] at V_in
    obtain ⟨U, ⟨U_in, U_sym, U_trans⟩, U_sub⟩ := V_in
    refine ⟨U, U_in, U_sym, U_trans, (UniformSpace.ball_mono U_sub _).trans V_sub⟩
  · rintro ⟨V, V_in, _, _, V_sub⟩
    exact ⟨V, V_in, V_sub⟩

namespace UniformSpace

/-
**UniformSpace.isOpen_ball_of_mem_uniformity** 是 Mathlib 中的一个引理，位于命名空间 `UniformS
pace`。
形式化陈述：isOpen_ball_of_mem_uniformity (x : X) {V : SetRel X X} [V.IsTrans] (h' : V
 in 𝓤 X) : IsOpen (ball x V)
参数：x : X；h' : V in 𝓤 X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_ball_subset`：isOpen_iff_ball_subset {s : Set α} : IsOpen s ↔ 
forall x in s, exists V in 𝓤 α, ball x V subseteq s
· 使用引理 `ball_subset_of_mem`：ball_subset_of_mem {V : SetRel X X} [V.IsTrans] {x y
 : X} (hy : y in ball x V) : ball y V subseteq ball x V
-/
lemma isOpen_ball_of_mem_uniformity (x : X) {V : SetRel X X} [V.IsTrans] (h' : V ∈ 𝓤 X) :
    IsOpen (ball x V) := by
  rw [isOpen_iff_ball_subset]
  intro y hy
  exact ⟨V, h', ball_subset_of_mem hy⟩
/-
**UniformSpace.isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity** 是 Mathlib 
中的一个引理，位于命名空间 `UniformSpace`。
形式化陈述：isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity (x : X) {V : SetRel X
 X} [V.IsSymm] [V.IsTrans] (h' : V in 𝓤 X) : IsClosed (ball x V)
参数：x : X；h' : V in 𝓤 X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isOpen_iff_ball_subset`：isOpen_iff_ball_subset {s : Set α} : IsOpen s ↔ 
forall x in s, exists V in 𝓤 α, ball x V subseteq s
· 使用定理 `SetRel.trans`：∀ {α : Type u_1} (R : SetRel α α) {a b c : α} [R.IsTrans],
 (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
-/
lemma isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity (x : X) {V : SetRel X X} [V.IsSymm]
    [V.IsTrans] (h' : V ∈ 𝓤 X) :
    IsClosed (ball x V) := by
  rw [← isOpen_compl_iff, isOpen_iff_ball_subset]
  exact fun y hy ↦ ⟨V, h', fun z hyz hxz ↦ hy <| V.trans hxz <| V.symm hyz⟩
/-
**UniformSpace.isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity** 是 Mathlib 
中的一个引理，位于命名空间 `UniformSpace`。
形式化陈述：isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity (x : X) {V : SetRel X
 X} [V.IsSymm] [V.IsTrans] (h' : V in 𝓤 X) : IsClopen (ball x V)
参数：x : X；h' : V in 𝓤 X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniformSpace.isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity`：isClo
sed_ball_of_isSymm_of_isTrans_of_mem_uniformity (x : X) {V : SetRel X X} [V.IsSy
mm] [V.IsTrans] (h' : V in 𝓤 X) : IsClosed (ball x V)
· 使用引理 `UniformSpace.isOpen_ball_of_mem_uniformity`：isOpen_ball_of_mem_uniformit
y (x : X) {V : SetRel X X} [V.IsTrans] (h' : V in 𝓤 X) : IsOpen (ball x V)
-/
lemma isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity (x : X) {V : SetRel X X} [V.IsSymm]
    [V.IsTrans] (h' : V ∈ 𝓤 X) :
    IsClopen (ball x V) :=
  ⟨isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity _ ‹_›, isOpen_ball_of_mem_uniformity _ ‹_›⟩

variable [IsUltraUniformity X]
/-
**UniformSpace.nhds_basis_clopens** 是 Mathlib 中的一个引理，位于命名空间 `UniformSpace`。
形式化陈述：nhds_basis_clopens (x : X) : (𝓝 x).HasBasis (fun s : Set X => x in s ∧ IsC
lopen s) id
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' 
→ Set α},   l.HasB…
· 使用定理 `nhds_basis_uniformity'`：nhds_basis_uniformity' {p : ι -> Prop} {s : ι ->
 SetRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => ball x
 (s i)
· 使用定理 `IsUltraUniformity.hasBasis`：∀ {X : Type u_1} {inst : UniformSpace X} [se
lf : IsUltraUniformity X],   (uniformity X).HasBasis (fun s => s ∈ uniformity X 
∧ s.IsSymm ∧ s.I…
· 使用引理 `UniformSpace.mem_ball_self`：mem_ball_self (x : α) {V : SetRel α α} : V i
n 𝓤 α -> x in ball x V
· 使用引理 `UniformSpace.isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity`：isClo
pen_ball_of_isSymm_of_isTrans_of_mem_uniformity (x : X) {V : SetRel X X} [V.IsSy
mm] [V.IsTrans] (h' : V in 𝓤 X) : IsClopen (ball x V)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOpen.mem_nhds_iff`：∀ {X : Type u} [inst : TopologicalSpace X] {x : X} 
{s : Set X}, IsOpen s → (s ∈ nhds x ↔ x ∈ s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma nhds_basis_clopens (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ IsClopen s) id := by
  refine (nhds_basis_uniformity' (IsUltraUniformity.hasBasis)).to_hasBasis' ?_ ?_
  · intro V ⟨hV, h_symm, h_trans⟩
    exact ⟨ball x V, ⟨mem_ball_self _ hV,
      isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity _ hV⟩, le_rfl⟩
  · rintro u ⟨hx, hu⟩
    simp [hu.right.mem_nhds_iff, hx]

/-- A uniform space with a nonarchimedean uniformity is zero-dimensional. -/
/-
**UniformSpace._root_.TopologicalSpace.isTopologicalBasis_clopens** 是 Mathlib 中的
一个引理，位于命名空间 `UniformSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A uniform space with a nonarchimedean uniformity is zero-dimensional.
-/
lemma _root_.TopologicalSpace.isTopologicalBasis_clopens :
    TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s} :=
  .of_hasBasis_nhds fun x ↦ by simpa [and_comm] using nhds_basis_clopens x

end UniformSpace

