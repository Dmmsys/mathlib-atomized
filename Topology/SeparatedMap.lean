/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Connected.Clopen
/-!
# Separated maps and locally injective maps out of a topological space.

This module introduces a pair of dual notions `IsSeparatedMap` and `IsLocallyInjective`.

A function from a topological space `X` to a type `Y` is a separated map if any two distinct
points in `X` with the same image in `Y` can be separated by open neighborhoods.
A constant function is a separated map if and only if `X` is a `T2Space`.

A function from a topological space `X` is locally injective if every point of `X`
has a neighborhood on which `f` is injective.
A constant function is locally injective if and only if `X` is discrete.

Given `f : X → Y` we can form the pullback $X \times_Y X$; the diagonal map
$\Delta: X \to X \times_Y X$ is always an embedding. It is a closed embedding
iff `f` is a separated map, iff the equal locus of any two continuous maps
coequalized by `f` is closed. It is an open embedding iff `f` is locally injective,
iff any such equal locus is open. Therefore, if `f` is a locally injective separated map,
the equal locus of two continuous maps coequalized by `f` is clopen, so if the two maps
agree on a point, then they agree on the whole connected component.

The analogue of separated maps and locally injective maps in algebraic geometry are
separated morphisms and unramified morphisms, respectively.

## Reference

https://stacks.math.columbia.edu/tag/0CY0
-/

@[expose] public section

open Topology

variable {X Y A} [TopologicalSpace X] [TopologicalSpace A]

/-
**Topology.IsEmbedding.toPullbackDiag** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbe
dding`。
形式化陈述：∀ {X : Type u_1} {Y : Sort u_2} [inst : TopologicalSpace X] (f : X → Y), T
opology.IsEmbedding (toPullbackDiag f)
参数：f : X → Y；toPullbackDiag f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.mk'`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y),   Function.Injective f 
→ (∀ (x : X), …
· 使用定理 `injective_toPullbackDiag`：injective_toPullbackDiag (f : X -> Y) : (toPul
lbackDiag f).Injective
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `toPullbackDiag_coe`：∀ {X : Type u_1} {Y : Sort u_2} (f : X → Y) (x : X),
 ↑(toPullbackDiag f x) = (x, x)
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.comap_prod`：comap_prod (f : α -> β × γ) (b : Filter β) (c : Filte
r γ) : comap f (b ×ˢ c) = comap (Prod.fst ∘ f) b ⊓ comap (Prod.snd ∘ f) c
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.comap_id'`：comap_id' : comap (fun x => x) f = f
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma Topology.IsEmbedding.toPullbackDiag (f : X → Y) : IsEmbedding (toPullbackDiag f) :=
  .mk' _ (injective_toPullbackDiag f) fun x ↦ by
    simp [nhds_induced, Filter.comap_comap, nhds_prod_eq, Filter.comap_prod, Function.comp_def,
      Filter.comap_id']
/-
**Continuous.mapPullback** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.mapPullback {X₁ X₂ Y₁ Y₂ Z₁ Z₂} [TopologicalSpace X₁] [Topologi
calSpace X₂] [TopologicalSpace Z₁] [TopologicalSpace Z₂] {f₁ : X₁ -> Y₁} {g₁ : Z
₁ -> Y₁} {f₂ : X₂ -> Y₂} {g₂ : Z₂ -> Y₂} {mapX : X₁ -> X₂} (contX : Continuous m
apX) {mapY : Y₁ -> Y₂} {mapZ : Z₁ -> Z₂} (contZ : Continuous mapZ) {commX : f₂ ∘
 mapX = mapY ∘ f₁} {commZ : g₂ ∘ mapZ = mapY ∘ g₁} : Continuous (Function.mapPul
lback mapX mapY mapZ commX commZ)
参数：contX : Continuous mapX；contZ : Continuous mapZ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
lemma Continuous.mapPullback {X₁ X₂ Y₁ Y₂ Z₁ Z₂}
    [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z₁] [TopologicalSpace Z₂]
    {f₁ : X₁ → Y₁} {g₁ : Z₁ → Y₁} {f₂ : X₂ → Y₂} {g₂ : Z₂ → Y₂}
    {mapX : X₁ → X₂} (contX : Continuous mapX) {mapY : Y₁ → Y₂}
    {mapZ : Z₁ → Z₂} (contZ : Continuous mapZ)
    {commX : f₂ ∘ mapX = mapY ∘ f₁} {commZ : g₂ ∘ mapZ = mapY ∘ g₁} :
    Continuous (Function.mapPullback mapX mapY mapZ commX commZ) := by
  refine continuous_induced_rng.mpr (.prodMk ?_ ?_) <;>
    apply_rules [continuous_fst, continuous_snd, continuous_subtype_val, Continuous.comp]

/-- A function from a topological space `X` to a type `Y` is a separated map if any two distinct
  points in `X` with the same image in `Y` can be separated by open neighborhoods. -/
/-
**IsSeparatedMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsSeparatedMap (f : X -> Y) : Prop
参数：f : X -> Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function from a topological space `X` to a type `Y` is a separated map if any 
two distinct
  points in `X` with the same image in `Y` can be separated by open neighborhood
s.
-/
def IsSeparatedMap (f : X → Y) : Prop := ∀ x₁ x₂, f x₁ = f x₂ →
    x₁ ≠ x₂ → ∃ s₁ s₂, IsOpen s₁ ∧ IsOpen s₂ ∧ x₁ ∈ s₁ ∧ x₂ ∈ s₂ ∧ Disjoint s₁ s₂
/-
**t2space_iff_isSeparatedMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：t2space_iff_isSeparatedMap (y : Y) : T2Space X ↔ IsSeparatedMap fun _ : X 
=> y
参数：y : Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma t2space_iff_isSeparatedMap (y : Y) : T2Space X ↔ IsSeparatedMap fun _ : X ↦ y :=
  ⟨fun ⟨t2⟩ _ _ _ hne ↦ t2 hne, fun sep ↦ ⟨fun x₁ x₂ hne ↦ sep x₁ x₂ rfl hne⟩⟩
/-
**T2Space.isSeparatedMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：T2Space.isSeparatedMap [T2Space X] (f : X -> Y) : IsSeparatedMap f
参数：f : X -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `t2_separation`：t2_separation [T2Space X] {x y : X} (h : x != y) : exists
 u v : Set X, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v
-/
lemma T2Space.isSeparatedMap [T2Space X] (f : X → Y) : IsSeparatedMap f := fun _ _ _ ↦ t2_separation
/-
**Function.Injective.isSeparatedMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Injective.isSeparatedMap {f : X -> Y} (inj : f.Injective) : IsSep
aratedMap f
参数：inj : f.Injective。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Function.Injective.isSeparatedMap {f : X → Y} (inj : f.Injective) : IsSeparatedMap f :=
  fun _ _ he hne ↦ (hne (inj he)).elim
/-
**isSeparatedMap_iff_disjoint_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSeparatedMap_iff_disjoint_nhds {f : X -> Y} : IsSeparatedMap f ↔ forall 
x₁ x₂, f x₁ = f x₂ -> x₁ != x₂ -> Disjoint (𝓝 x₁) (𝓝 x₂)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₃_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {p q : (a : α) → (b : β a) → γ a b → Prop},   (∀ (a : α) (b : β a) (c 
: γ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.HasBasis.disjoint_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α},   l.H…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isSeparatedMap_iff_disjoint_nhds {f : X → Y} : IsSeparatedMap f ↔
    ∀ x₁ x₂, f x₁ = f x₂ → x₁ ≠ x₂ → Disjoint (𝓝 x₁) (𝓝 x₂) :=
  forall₃_congr fun x x' _ ↦ by simp only [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens x'),
    ← exists_and_left, and_assoc, and_comm, and_left_comm]
/-
**isSeparatedMap_iff_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSeparatedMap_iff_nhds {f : X -> Y} : IsSeparatedMap f ↔ forall x₁ x₂, f 
x₁ = f x₂ -> x₁ != x₂ -> exists s₁ in 𝓝 x₁, exists s₂ in 𝓝 x₂, Disjoint s₁ s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isSeparatedMap_iff_nhds {f : X → Y} : IsSeparatedMap f ↔
    ∀ x₁ x₂, f x₁ = f x₂ → x₁ ≠ x₂ → ∃ s₁ ∈ 𝓝 x₁, ∃ s₂ ∈ 𝓝 x₂, Disjoint s₁ s₂ := by
  simp_rw [isSeparatedMap_iff_disjoint_nhds, Filter.disjoint_iff]

open Set Filter in
/-
**isSeparatedMap_iff_isClosed_diagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSeparatedMap_iff_isClosed_diagonal {f : X -> Y} : IsSeparatedMap f ↔ IsC
losed f.pullbackDiagonal
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
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `forall₄_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {p q : (a : α) → (b : β
 a)…
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
-/
theorem isSeparatedMap_iff_isClosed_diagonal {f : X → Y} :
    IsSeparatedMap f ↔ IsClosed f.pullbackDiagonal := by
  simp_rw [isSeparatedMap_iff_nhds, ← isOpen_compl_iff, isOpen_iff_mem_nhds,
    Subtype.forall, Prod.forall, nhds_induced, nhds_prod_eq]
  refine forall₄_congr fun x₁ x₂ _ _ ↦ ⟨fun h ↦ ?_, fun ⟨t, ht, t_sub⟩ ↦ ?_⟩
  · simp_rw [← Filter.disjoint_iff, ← compl_diagonal_mem_prod] at h
    exact ⟨_, h, subset_rfl⟩
  · obtain ⟨s₁, h₁, s₂, h₂, s_sub⟩ := mem_prod_iff.mp ht
    exact ⟨s₁, h₁, s₂, h₂, disjoint_left.2 fun x h₁ h₂ ↦ @t_sub ⟨(x, x), rfl⟩ (s_sub ⟨h₁, h₂⟩) rfl⟩
/-
**isSeparatedMap_iff_isClosedEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSeparatedMap_iff_isClosedEmbedding {f : X -> Y} : IsSeparatedMap f ↔ IsC
losedEmbedding (toPullbackDiag f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSeparatedMap_iff_isClosed_diagonal`：isSeparatedMap_iff_isClosed_diagon
al {f : X -> Y} : IsSeparatedMap f ↔ IsClosed f.pullbackDiagonal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `range_toPullbackDiag`：range_toPullbackDiag (f : X -> Y) : range (toPullb
ackDiag f) = pullbackDiagonal f
· 使用定理 `Topology.IsEmbedding.toPullbackDiag`：∀ {X : Type u_1} {Y : Sort u_2} [in
st : TopologicalSpace X] (f : X → Y), Topology.IsEmbedding (toPullbackDiag f)
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
-/
theorem isSeparatedMap_iff_isClosedEmbedding {f : X → Y} :
    IsSeparatedMap f ↔ IsClosedEmbedding (toPullbackDiag f) := by
  rw [isSeparatedMap_iff_isClosed_diagonal, ← range_toPullbackDiag]
  exact ⟨fun h ↦ ⟨.toPullbackDiag f, h⟩, fun h ↦ h.isClosed_range⟩
/-
**isSeparatedMap_iff_isClosedMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSeparatedMap_iff_isClosedMap {f : X -> Y} : IsSeparatedMap f ↔ IsClosedM
ap (toPullbackDiag f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isSeparatedMap_iff_isClosedEmbedding`：isSeparatedMap_iff_isClosedEmbeddi
ng {f : X -> Y} : IsSeparatedMap f ↔ IsClosedEmbedding (toPullbackDiag f)
· 使用定理 `Topology.IsClosedEmbedding.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → IsCl…
· 使用定理 `Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap`：∀ {X : T
ype u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topolo
gicalSpace Y],   Continuous f → Function.Injective f…
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `Topology.IsEmbedding.toPullbackDiag`：∀ {X : Type u_1} {Y : Sort u_2} [in
st : TopologicalSpace X] (f : X → Y), Topology.IsEmbedding (toPullbackDiag f)
· 使用定理 `injective_toPullbackDiag`：injective_toPullbackDiag (f : X -> Y) : (toPul
lbackDiag f).Injective
-/
theorem isSeparatedMap_iff_isClosedMap {f : X → Y} :
    IsSeparatedMap f ↔ IsClosedMap (toPullbackDiag f) :=
  isSeparatedMap_iff_isClosedEmbedding.trans
    ⟨IsClosedEmbedding.isClosedMap, .of_continuous_injective_isClosedMap
      (IsEmbedding.toPullbackDiag f).continuous (injective_toPullbackDiag f)⟩

open Function.Pullback in
/-
**IsSeparatedMap.pullback** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeparatedMap.pullback {f : X -> Y} (sep : IsSeparatedMap f) (g : A -> Y)
 : IsSeparatedMap (@snd X Y A f g)
参数：sep : IsSeparatedMap f；g : A -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSeparatedMap_iff_isClosed_diagonal`：isSeparatedMap_iff_isClosed_diagon
al {f : X -> Y} : IsSeparatedMap f ↔ IsClosed f.pullbackDiagonal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `preimage_map_fst_pullbackDiagonal`：preimage_map_fst_pullbackDiagonal {f 
: X -> Y} {g : Z -> Y} : @map_fst X Y Z f g ⁻¹' pullbackDiagonal f = pullbackDia
gonal (@snd X Y Z f g)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用引理 `Function.pullback_comm_sq`：Function.pullback_comm_sq (f : X -> Y) (g : Z
 -> Y) : f ∘ @fst X Y Z f g = g ∘ @snd X Y Z f g
· 使用引理 `Continuous.mapPullback`：Continuous.mapPullback {X₁ X₂ Y₁ Y₂ Z₁ Z₂} [Topo
logicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z₁] [TopologicalSpace Z
₂] {f₁ : X₁ …
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem IsSeparatedMap.pullback {f : X → Y} (sep : IsSeparatedMap f) (g : A → Y) :
    IsSeparatedMap (@snd X Y A f g) := by
  rw [isSeparatedMap_iff_isClosed_diagonal] at sep ⊢
  rw [← preimage_map_fst_pullbackDiagonal]
  refine sep.preimage (Continuous.mapPullback ?_ ?_) <;>
  apply_rules [continuous_fst, continuous_subtype_val, Continuous.comp]
/-
**IsSeparatedMap.comp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeparatedMap.comp_left {A} {f : X -> Y} (sep : IsSeparatedMap f) {g : Y 
-> A} (inj : g.Injective) : IsSeparatedMap (g ∘ f)
参数：sep : IsSeparatedMap f；inj : g.Injective。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsSeparatedMap.comp_left {A} {f : X → Y} (sep : IsSeparatedMap f) {g : Y → A}
    (inj : g.Injective) : IsSeparatedMap (g ∘ f) := fun x₁ x₂ he ↦ sep x₁ x₂ (inj he)
/-
**IsSeparatedMap.comp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeparatedMap.comp_right {f : X -> Y} (sep : IsSeparatedMap f) {g : A -> 
X} (cont : Continuous g) (inj : g.Injective) : IsSeparatedMap (f ∘ g)
参数：sep : IsSeparatedMap f；cont : Continuous g；inj : g.Injective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSeparatedMap_iff_isClosed_diagonal`：isSeparatedMap_iff_isClosed_diagon
al {f : X -> Y} : IsSeparatedMap f ↔ IsClosed f.pullbackDiagonal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.preimage_pullbackDiagonal`：Function.Injective.preimag
e_pullbackDiagonal {f : X -> Y} {g : Z -> X} (inj : g.Injective) : mapPullback g
 id g (by rfl) (by rfl) ⁻¹' pullba…
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用引理 `Continuous.mapPullback`：Continuous.mapPullback {X₁ X₂ Y₁ Y₂ Z₁ Z₂} [Topo
logicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z₁] [TopologicalSpace Z
₂] {f₁ : X₁ …
-/
theorem IsSeparatedMap.comp_right {f : X → Y} (sep : IsSeparatedMap f) {g : A → X}
    (cont : Continuous g) (inj : g.Injective) : IsSeparatedMap (f ∘ g) := by
  rw [isSeparatedMap_iff_isClosed_diagonal] at sep ⊢
  rw [← inj.preimage_pullbackDiagonal]
  exact sep.preimage (cont.mapPullback cont)

/-- A function from a topological space `X` is locally injective if every point of `X`
  has a neighborhood on which `f` is injective. -/
/-
**IsLocallyInjective** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocallyInjective (f : X -> Y) : Prop
参数：f : X -> Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function from a topological space `X` is locally injective if every point of `
X`
  has a neighborhood on which `f` is injective.
-/
def IsLocallyInjective (f : X → Y) : Prop := ∀ x : X, ∃ U, IsOpen U ∧ x ∈ U ∧ U.InjOn f
/-
**Function.Injective.IsLocallyInjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Injective.IsLocallyInjective {f : X -> Y} (inj : f.Injective) : I
sLocallyInjective f
参数：inj : f.Injective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `trivial`：True
-/
lemma Function.Injective.IsLocallyInjective {f : X → Y} (inj : f.Injective) :
    IsLocallyInjective f := fun _ ↦ ⟨_, isOpen_univ, trivial, fun _ _ _ _ ↦ @inj _ _⟩
/-
**isLocallyInjective_iff_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocallyInjective_iff_nhds {f : X -> Y} : IsLocallyInjective f ↔ forall x
 : X, exists U in 𝓝 x, U.InjOn f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
lemma isLocallyInjective_iff_nhds {f : X → Y} :
    IsLocallyInjective f ↔ ∀ x : X, ∃ U ∈ 𝓝 x, U.InjOn f := by
  constructor <;> intro h x
  · obtain ⟨U, ho, hm, hi⟩ := h x; exact ⟨U, ho.mem_nhds hm, hi⟩
  · obtain ⟨U, hn, hi⟩ := h x
    exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hn, hi.mono interior_subset⟩
/-
**isLocallyInjective_iff_isOpen_diagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocallyInjective_iff_isOpen_diagonal {f : X -> Y} : IsLocallyInjective f
 ↔ IsOpen f.pullbackDiagonal
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
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.prod_mem_prod`：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t
 in f ×ˢ g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
-/
theorem isLocallyInjective_iff_isOpen_diagonal {f : X → Y} :
    IsLocallyInjective f ↔ IsOpen f.pullbackDiagonal := by
  simp_rw [isLocallyInjective_iff_nhds, isOpen_iff_mem_nhds,
    Subtype.forall, Prod.forall, nhds_induced, nhds_prod_eq, Filter.mem_comap]
  refine ⟨?_, fun h x ↦ ?_⟩
  · rintro h x x' hx (rfl : x = x')
    obtain ⟨U, hn, hi⟩ := h x
    exact ⟨_, Filter.prod_mem_prod hn hn, fun {p} hp ↦ hi hp.1 hp.2 p.2⟩
  · obtain ⟨t, ht, t_sub⟩ := h x x rfl rfl
    obtain ⟨t₁, h₁, t₂, h₂, prod_sub⟩ := Filter.mem_prod_iff.mp ht
    exact ⟨t₁ ∩ t₂, Filter.inter_mem h₁ h₂,
      fun x₁ h₁ x₂ h₂ he ↦ @t_sub ⟨(x₁, x₂), he⟩ (prod_sub ⟨h₁.1, h₂.2⟩)⟩
/-
**IsLocallyInjective_iff_isOpenEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocallyInjective_iff_isOpenEmbedding {f : X -> Y} : IsLocallyInjective f
 ↔ IsOpenEmbedding (toPullbackDiag f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isLocallyInjective_iff_isOpen_diagonal`：isLocallyInjective_iff_isOpen_di
agonal {f : X -> Y} : IsLocallyInjective f ↔ IsOpen f.pullbackDiagonal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `range_toPullbackDiag`：range_toPullbackDiag (f : X -> Y) : range (toPullb
ackDiag f) = pullbackDiagonal f
· 使用定理 `Topology.IsEmbedding.toPullbackDiag`：∀ {X : Type u_1} {Y : Sort u_2} [in
st : TopologicalSpace X] (f : X → Y), Topology.IsEmbedding (toPullbackDiag f)
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
-/
theorem IsLocallyInjective_iff_isOpenEmbedding {f : X → Y} :
    IsLocallyInjective f ↔ IsOpenEmbedding (toPullbackDiag f) := by
  rw [isLocallyInjective_iff_isOpen_diagonal, ← range_toPullbackDiag]
  exact ⟨fun h ↦ ⟨.toPullbackDiag f, h⟩, fun h ↦ h.isOpen_range⟩
/-
**isLocallyInjective_iff_isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocallyInjective_iff_isOpenMap {f : X -> Y} : IsLocallyInjective f ↔ IsO
penMap (toPullbackDiag f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsLocallyInjective_iff_isOpenEmbedding`：IsLocallyInjective_iff_isOpenEmb
edding {f : X -> Y} : IsLocallyInjective f ↔ IsOpenEmbedding (toPullbackDiag f)
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap`：∀ {X : Type 
u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topologica
lSpace Y],   Continuous f → Function.Injective f…
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `Topology.IsEmbedding.toPullbackDiag`：∀ {X : Type u_1} {Y : Sort u_2} [in
st : TopologicalSpace X] (f : X → Y), Topology.IsEmbedding (toPullbackDiag f)
· 使用定理 `injective_toPullbackDiag`：injective_toPullbackDiag (f : X -> Y) : (toPul
lbackDiag f).Injective
-/
theorem isLocallyInjective_iff_isOpenMap {f : X → Y} :
    IsLocallyInjective f ↔ IsOpenMap (toPullbackDiag f) :=
  IsLocallyInjective_iff_isOpenEmbedding.trans
    ⟨IsOpenEmbedding.isOpenMap, .of_continuous_injective_isOpenMap
      (IsEmbedding.toPullbackDiag f).continuous (injective_toPullbackDiag f)⟩
/-
**discreteTopology_iff_locallyInjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_iff_locallyInjective (y : Y) : DiscreteTopology X ↔ IsLoc
allyInjective fun _ : X => y
参数：y : Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `discreteTopology_iff_singleton_mem_nhds`：discreteTopology_iff_singleton_
mem_nhds [TopologicalSpace α] : DiscreteTopology α ↔ forall x : α, {x} in 𝓝 x
· 使用引理 `isLocallyInjective_iff_nhds`：isLocallyInjective_iff_nhds {f : X -> Y} : 
IsLocallyInjective f ↔ forall x : X, exists U in 𝓝 x, U.InjOn f
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Set.injOn_singleton`：injOn_singleton (f : α -> β) (a : α) : InjOn f {a}
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem discreteTopology_iff_locallyInjective (y : Y) :
    DiscreteTopology X ↔ IsLocallyInjective fun _ : X ↦ y := by
  rw [discreteTopology_iff_singleton_mem_nhds, isLocallyInjective_iff_nhds]
  refine forall_congr' fun x ↦ ⟨fun h ↦ ⟨{x}, h, Set.injOn_singleton _ _⟩, fun ⟨U, hU, inj⟩ ↦ ?_⟩
  convert! hU; ext x'; refine ⟨?_, fun h ↦ inj h (mem_of_mem_nhds hU) rfl⟩
  rintro rfl; exact mem_of_mem_nhds hU
/-
**IsLocallyInjective.comp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocallyInjective.comp_left {A} {f : X -> Y} (hf : IsLocallyInjective f) 
{g : Y -> A} (hg : g.Injective) : IsLocallyInjective (g ∘ f)
参数：hf : IsLocallyInjective f；hg : g.Injective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp_injOn`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {f : α → β} {g : β → γ} {s : Set α},   Function.Injective g → Set.InjOn f 
s → Set.InjOn (g ∘ …
-/
theorem IsLocallyInjective.comp_left {A} {f : X → Y} (hf : IsLocallyInjective f) {g : Y → A}
    (hg : g.Injective) : IsLocallyInjective (g ∘ f) :=
  fun x ↦ let ⟨U, hU, hx, inj⟩ := hf x; ⟨U, hU, hx, hg.comp_injOn inj⟩
/-
**IsLocallyInjective.comp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocallyInjective.comp_right {f : X -> Y} (hf : IsLocallyInjective f) {g 
: A -> X} (cont : Continuous g) (hg : g.Injective) : IsLocallyInjective (f ∘ g)
参数：hf : IsLocallyInjective f；cont : Continuous g；hg : g.Injective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isLocallyInjective_iff_isOpen_diagonal`：isLocallyInjective_iff_isOpen_di
agonal {f : X -> Y} : IsLocallyInjective f ↔ IsOpen f.pullbackDiagonal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.preimage_pullbackDiagonal`：Function.Injective.preimag
e_pullbackDiagonal {f : X -> Y} {g : Z -> X} (inj : g.Injective) : mapPullback g
 id g (by rfl) (by rfl) ⁻¹' pullba…
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用引理 `Continuous.mapPullback`：Continuous.mapPullback {X₁ X₂ Y₁ Y₂ Z₁ Z₂} [Topo
logicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z₁] [TopologicalSpace Z
₂] {f₁ : X₁ …
-/
theorem IsLocallyInjective.comp_right {f : X → Y} (hf : IsLocallyInjective f) {g : A → X}
    (cont : Continuous g) (hg : g.Injective) : IsLocallyInjective (f ∘ g) := by
  rw [isLocallyInjective_iff_isOpen_diagonal] at hf ⊢
  rw [← hg.preimage_pullbackDiagonal]
  apply hf.preimage (cont.mapPullback cont)

section eqLocus

variable {f : X → Y} {g₁ g₂ : A → X} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
include h₁ h₂

/-
**IsSeparatedMap.isClosed_eqLocus** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeparatedMap.isClosed_eqLocus (sep : IsSeparatedMap f) (he : f ∘ g₁ = f 
∘ g₂) : IsClosed {a | g₁ a = g₂ a}
参数：sep : IsSeparatedMap f；he : f ∘ g₁ = f ∘ g₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isSeparatedMap_iff_isClosed_diagonal`：isSeparatedMap_iff_isClosed_diagon
al {f : X -> Y} : IsSeparatedMap f ↔ IsClosed f.pullbackDiagonal
-/
theorem IsSeparatedMap.isClosed_eqLocus (sep : IsSeparatedMap f) (he : f ∘ g₁ = f ∘ g₂) :
    IsClosed {a | g₁ a = g₂ a} :=
  let g : A → f.Pullback f := fun a ↦ ⟨⟨g₁ a, g₂ a⟩, congr_fun he a⟩
  (isSeparatedMap_iff_isClosed_diagonal.mp sep).preimage (by fun_prop : Continuous g)
/-
**IsLocallyInjective.isOpen_eqLocus** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocallyInjective.isOpen_eqLocus (inj : IsLocallyInjective f) (he : f ∘ g
₁ = f ∘ g₂) : IsOpen {a | g₁ a = g₂ a}
参数：inj : IsLocallyInjective f；he : f ∘ g₁ = f ∘ g₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isLocallyInjective_iff_isOpen_diagonal`：isLocallyInjective_iff_isOpen_di
agonal {f : X -> Y} : IsLocallyInjective f ↔ IsOpen f.pullbackDiagonal
-/
theorem IsLocallyInjective.isOpen_eqLocus (inj : IsLocallyInjective f) (he : f ∘ g₁ = f ∘ g₂) :
    IsOpen {a | g₁ a = g₂ a} :=
  let g : A → f.Pullback f := fun a ↦ ⟨⟨g₁ a, g₂ a⟩, congr_fun he a⟩
  (isLocallyInjective_iff_isOpen_diagonal.mp inj).preimage (by fun_prop : Continuous g)

end eqLocus

variable {X E A : Type*} [TopologicalSpace E] [TopologicalSpace A] {p : E → X}

namespace IsSeparatedMap

variable {s : Set A} {g g₁ g₂ : A → E} (sep : IsSeparatedMap p) (inj : IsLocallyInjective p)
include sep inj

/-- If `p` is a locally injective separated map, and `A` is a connected space,
  then two lifts `g₁, g₂ : A → E` of a map `f : A → X` are equal if they agree at one point. -/
/-
**IsSeparatedMap.eq_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsSeparatedMap`。
形式化陈述：eq_of_comp_eq [PreconnectedSpace A] (h₁ : Continuous g₁) (h₂ : Continuous 
g₂) (he : p ∘ g₁ = p ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂
参数：h₁ : Continuous g₁；h₂ : Continuous g₂；he : p ∘ g₁ = p ∘ g₂；a : A；ha : g₁ a = 
g₂ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClopen.eq_univ`：IsClopen.eq_univ [PreconnectedSpace α] {s : Set α} (h'
 : IsClopen s) (h : s.Nonempty) : s = univ
· 使用定理 `IsSeparatedMap.isClosed_eqLocus`：IsSeparatedMap.isClosed_eqLocus (sep : 
IsSeparatedMap f) (he : f ∘ g₁ = f ∘ g₂) : IsClosed {a | g₁ a = g₂ a}
· 使用定理 `IsLocallyInjective.isOpen_eqLocus`：IsLocallyInjective.isOpen_eqLocus (in
j : IsLocallyInjective f) (he : f ∘ g₁ = f ∘ g₂) : IsOpen {a | g₁ a = g₂ a}

--- 原说明 ---
If `p` is a locally injective separated map, and `A` is a connected space,
  then two lifts `g₁, g₂ : A → E` of a map `f : A → X` are equal if they agree a
t one point.
-/
theorem eq_of_comp_eq
    [PreconnectedSpace A] (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (he : p ∘ g₁ = p ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ := funext fun a' ↦ by
  apply (IsClopen.eq_univ ⟨sep.isClosed_eqLocus h₁ h₂ he, inj.isOpen_eqLocus h₁ h₂ he⟩ ⟨a, ha⟩).symm
    ▸ Set.mem_univ a'
/-
**IsSeparatedMap.eqOn_of_comp_eqOn** 是 Mathlib 中的一个定理，位于命名空间 `IsSeparatedMap`。
形式化陈述：eqOn_of_comp_eqOn (hs : IsPreconnected s) (h₁ : ContinuousOn g₁ s) (h₂ : C
ontinuousOn g₂ s) (he : s.EqOn (p ∘ g₁) (p ∘ g₂)) {a : A} (has : a in s) (ha : g
₁ a = g₂ a) : s.EqOn g₁ g₂
参数：hs : IsPreconnected s；h₁ : ContinuousOn g₁ s；h₂ : ContinuousOn g₂ s；he : s.Eq
On (p ∘ g₁) (p ∘ g₂)；has : a in s；ha : g₁ a = g₂ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.domRestrict_eq_domRestrict_iff`：domRestrict_eq_domRestrict_iff : dom
Restrict s f₁ = domRestrict s f₂ ↔ EqOn f₁ f₂ s
· 使用定理 `IsSeparatedMap.eq_of_comp_eq`：eq_of_comp_eq [PreconnectedSpace A] (h₁ : 
Continuous g₁) (h₂ : Continuous g₂) (he : p ∘ g₁ = p ∘ g₂) (a : A) (ha : g₁ a = 
g₂ a) : g₁ = g₂
· 使用定理 `isPreconnected_iff_preconnectedSpace`：isPreconnected_iff_preconnectedSpa
ce {s : Set α} : IsPreconnected s ↔ PreconnectedSpace s
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
-/
theorem eqOn_of_comp_eqOn (hs : IsPreconnected s) (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
    (he : s.EqOn (p ∘ g₁) (p ∘ g₂)) {a : A} (has : a ∈ s) (ha : g₁ a = g₂ a) : s.EqOn g₁ g₂ := by
  rw [← Set.domRestrict_eq_domRestrict_iff] at he ⊢
  rw [continuousOn_iff_continuous_domRestrict] at h₁ h₂
  rw [isPreconnected_iff_preconnectedSpace] at hs
  exact sep.eq_of_comp_eq inj h₁ h₂ he ⟨a, has⟩ ha
/-
**IsSeparatedMap.const_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsSeparatedMap`。
形式化陈述：const_of_comp [PreconnectedSpace A] (cont : Continuous g) (he : forall a a
', p (g a) = p (g a')) (a a') : g a = g a'
参数：cont : Continuous g；he : forall a a', p (g a) = p (g a')；a a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `IsSeparatedMap.eq_of_comp_eq`：eq_of_comp_eq [PreconnectedSpace A] (h₁ : 
Continuous g₁) (h₂ : Continuous g₂) (he : p ∘ g₁ = p ∘ g₂) (a : A) (ha : g₁ a = 
g₂ a) : g₁ = g₂
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem const_of_comp [PreconnectedSpace A] (cont : Continuous g)
    (he : ∀ a a', p (g a) = p (g a')) (a a') : g a = g a' :=
  congr_fun (sep.eq_of_comp_eq inj cont continuous_const (funext fun a ↦ he a a') a' rfl) a
/-
**IsSeparatedMap.constOn_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsSeparatedMap`。
形式化陈述：constOn_of_comp (hs : IsPreconnected s) (cont : ContinuousOn g s) (he : fo
rall a in s, forall a' in s, p (g a) = p (g a')) {a a'} (ha : a in s) (ha' : a' 
in s) : g a = g a'
参数：hs : IsPreconnected s；cont : ContinuousOn g s；he : forall a in s, forall a' i
n s, p (g a) = p (g a')；ha : a in s；ha' : a' in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeparatedMap.eqOn_of_comp_eqOn`：eqOn_of_comp_eqOn (hs : IsPreconnected
 s) (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s) (he : s.EqOn (p ∘ g₁) (p ∘
 g₂)) {a : A} (has : a…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem constOn_of_comp (hs : IsPreconnected s) (cont : ContinuousOn g s)
    (he : ∀ a ∈ s, ∀ a' ∈ s, p (g a) = p (g a'))
    {a a'} (ha : a ∈ s) (ha' : a' ∈ s) : g a = g a' :=
  sep.eqOn_of_comp_eqOn inj hs cont continuous_const.continuousOn
    (fun a ha ↦ he a ha a' ha') ha' rfl ha

end IsSeparatedMap

