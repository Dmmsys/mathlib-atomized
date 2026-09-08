/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Order.Ideal
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.Spectral.Hom

/-!

# Prespectral spaces

In this file, we define prespectral spaces as spaces whose lattice of compact opens forms a basis.

-/

@[expose] public section

open TopologicalSpace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A space is prespectral if the lattice of compact opens forms a basis. -/
@[stacks 08YG "The last condition for spectral spaces", mk_iff]
/-
**PrespectralSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_3) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A space is prespectral if the lattice of compact opens forms a basis.
-/
class PrespectralSpace (X : Type*) [TopologicalSpace X] : Prop where
  isTopologicalBasis : IsTopologicalBasis { U : Set X | IsOpen U ∧ IsCompact U }

/-- A space is prespectral if it has a basis consisting of compact opens. -/
/-
**PrespectralSpace.of_isTopologicalBasis** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PrespectralSpace.of_isTopologicalBasis {B : Set (Set X)} (basis : IsTopolo
gicalBasis B) (isCompact_basis : forall U in B, IsCompact U) : PrespectralSpace 
X where isTopologicalBasis
参数：Set X；basis : IsTopologicalBasis B；isCompact_basis : forall U in B, IsCompact
 U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.of_isOpen_of_subset`：∀ {α : Type u} 
[t : TopologicalSpace α] {s s' : Set (Set α)},   (∀ u ∈ s', IsOpen u) → Topologi
calSpace.IsTopologicalBasis s → s ⊆ s' → Topo…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen`：∀ {α : Type u} [t : Topologi
calSpace α] {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTopologicalBasis
 b → s ∈ b → IsOpen s

--- 原说明 ---
A space is prespectral if it has a basis consisting of compact opens.
-/
lemma PrespectralSpace.of_isTopologicalBasis {B : Set (Set X)}
    (basis : IsTopologicalBasis B) (isCompact_basis : ∀ U ∈ B, IsCompact U) :
    PrespectralSpace X where
  isTopologicalBasis := basis.of_isOpen_of_subset (fun _ h ↦ h.1)
    fun s hs ↦ ⟨basis.isOpen hs, isCompact_basis s hs⟩

/-- A space is prespectral if it has a basis consisting of compact opens.
This is the variant with an indexed basis instead. -/
/-
**PrespectralSpace.of_isTopologicalBasis'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PrespectralSpace.of_isTopologicalBasis' {ι : Type*} {b : ι -> Set X} (basi
s : IsTopologicalBasis (Set.range b)) (isCompact_basis : forall i, IsCompact (b 
i)) : PrespectralSpace X
参数：basis : IsTopologicalBasis (Set.range b)；isCompact_basis : forall i, IsCompac
t (b i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrespectralSpace.of_isTopologicalBasis`：PrespectralSpace.of_isTopologica
lBasis {B : Set (Set X)} (basis : IsTopologicalBasis B) (isCompact_basis : foral
l U in B, IsCompact U) : Pre…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A space is prespectral if it has a basis consisting of compact opens.
This is the variant with an indexed basis instead.
-/
lemma PrespectralSpace.of_isTopologicalBasis' {ι : Type*} {b : ι → Set X}
    (basis : IsTopologicalBasis (Set.range b)) (isCompact_basis : ∀ i, IsCompact (b i)) :
    PrespectralSpace X :=
  .of_isTopologicalBasis basis (by simp_all)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [NoetherianSpace X] : PrespectralSpace X :=
  .of_isTopologicalBasis isTopologicalBasis_opens fun _ _ ↦ NoetherianSpace.isCompact _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [PrespectralSpace X] : LocallyCompactSpace X where
  local_compact_nhds _ _ hn :=
    have ⟨V, ⟨hV₁, hV₂⟩, hxV, hVn⟩ := PrespectralSpace.isTopologicalBasis.mem_nhds_iff.mp hn
    ⟨V, hV₁.mem_nhds hxV, hVn, hV₂⟩

open PrespectralSpace in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [T2Space X] [PrespectralSpace X] : TotallySeparatedSpace X :=
  totallySeparatedSpace_iff_exists_isClopen.mpr fun _ _ hxy ↦
    have ⟨U, ⟨hU₁, hU₂⟩, hxU, hyU⟩ :=
      isTopologicalBasis.exists_subset_of_mem_open hxy isClosed_singleton.isOpen_compl
    ⟨U, ⟨hU₂.isClosed, hU₁⟩, hxU, fun h ↦ hyU h rfl⟩
/-
**PrespectralSpace.of_isOpenCover** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PrespectralSpace.of_isOpenCover {ι : Type*} {U : ι -> Opens X} (hU : IsOpe
nCover U) [forall i, PrespectralSpace (U i)] : PrespectralSpace X
参数：hU : IsOpenCover U；U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrespectralSpace.of_isTopologicalBasis`：PrespectralSpace.of_isTopologica
lBasis {B : Set (Set X)} (basis : IsTopologicalBasis B) (isCompact_basis : foral
l U in B, IsCompact U) : Pre…
· 使用引理 `TopologicalSpace.IsOpenCover.isTopologicalBasis`：isTopologicalBasis (hu 
: IsOpenCover u) {B : forall i, Set (Set (u i))} (hB : forall i, IsTopologicalBa
sis (B i)) : IsTopologicalBasis (⋃ i,…
· 使用定理 `PrespectralSpace.isTopologicalBasis`：∀ {X : Type u_3} {inst : Topologica
lSpace X} [self : PrespectralSpace X],   TopologicalSpace.IsTopologicalBasis {U 
| IsOpen U ∧ IsCompact U}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
lemma PrespectralSpace.of_isOpenCover
    {ι : Type*} {U : ι → Opens X} (hU : IsOpenCover U) [∀ i, PrespectralSpace (U i)] :
    PrespectralSpace X := by
  refine .of_isTopologicalBasis (hU.isTopologicalBasis fun i ↦ isTopologicalBasis) ?_
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp,
    forall_comm (α := Set _), forall_apply_eq_imp_iff₂]
  exact fun i V hV hV' ↦ hV'.image continuous_subtype_val
/-
**PrespectralSpace.of_isInducing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PrespectralSpace.of_isInducing [PrespectralSpace Y] (f : X -> Y) (hf : IsI
nducing f) (hf' : IsSpectralMap f) : PrespectralSpace X
参数：f : X -> Y；hf : IsInducing f；hf' : IsSpectralMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrespectralSpace.of_isTopologicalBasis`：PrespectralSpace.of_isTopologica
lBasis {B : Set (Set X)} (basis : IsTopologicalBasis B) (isCompact_basis : foral
l U in B, IsCompact U) : Pre…
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isInducing`：∀ {α : Type u} {β : Type
 u_1} [t : TopologicalSpace α] [inst : TopologicalSpace β] {f : α → β} {T : Set 
(Set β)},   Topology.IsInducing f → …
· 使用定理 `PrespectralSpace.isTopologicalBasis`：∀ {X : Type u_3} {inst : Topologica
lSpace X} [self : PrespectralSpace X],   TopologicalSpace.IsTopologicalBasis {U 
| IsOpen U ∧ IsCompact U}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsSpectralMap.isCompact_preimage_of_isOpen`：∀ {α : Type u_2} {β : Type u
_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β},   IsS
pectralMap f → ∀ ⦃s : Set β⦄, Is…
-/
lemma PrespectralSpace.of_isInducing [PrespectralSpace Y]
    (f : X → Y) (hf : IsInducing f) (hf' : IsSpectralMap f) : PrespectralSpace X :=
  .of_isTopologicalBasis (PrespectralSpace.isTopologicalBasis.isInducing hf) (by
    simp only [Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp]
    rintro _ U h₁ h₂ rfl
    exact hf'.isCompact_preimage_of_isOpen h₁ h₂)
/-
**PrespectralSpace.of_isClosedEmbedding** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PrespectralSpace.of_isClosedEmbedding [PrespectralSpace Y] (f : X -> Y) (h
f : IsClosedEmbedding f) : PrespectralSpace X
参数：f : X -> Y；hf : IsClosedEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrespectralSpace.of_isInducing`：PrespectralSpace.of_isInducing [Prespect
ralSpace Y] (f : X -> Y) (hf : IsInducing f) (hf' : IsSpectralMap f) : Prespectr
alSpace X
· 使用定理 `Topology.IsClosedEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Topo…
· 使用定理 `IsProperMap.isSpectralMap`：IsProperMap.isSpectralMap {f : α -> β} (hf : 
IsProperMap f) : IsSpectralMap f
· 使用引理 `Topology.IsClosedEmbedding.isProperMap`：Topology.IsClosedEmbedding.isPro
perMap (hf : IsClosedEmbedding f) : IsProperMap f
-/
lemma PrespectralSpace.of_isClosedEmbedding [PrespectralSpace Y]
    (f : X → Y) (hf : IsClosedEmbedding f) : PrespectralSpace X :=
  .of_isInducing f hf.isInducing hf.isProperMap.isSpectralMap

/-- Let `f : X → Y` be an open embedding of topological spaces.
If `Y` is a prespectral space (i.e., the quasi-compact opens of `Y` form a basis),
then `X` is also a prespectral space. -/
/-
**Topology.IsOpenEmbedding.prespectralSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.prespectralSpace [PrespectralSpace Y] {f : X -> Y
} (hf : IsOpenEmbedding f) : PrespectralSpace X where isTopologicalBasis
参数：hf : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`：isTopologicalBasi
s_of_isOpen_of_nhds {s : Set (Set α)} (h_open : forall u in s, IsOpen u) (h_nhds
 : forall (a : α) (u : Set α), a in u -> Is…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen_iff`：∀ {α : Type u} [t : Topo
logicalSpace α] {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTopologicalB
asis b → (IsOpen s ↔ ∀ a ∈ s, ∃ t ∈ …
· 使用定理 `PrespectralSpace.isTopologicalBasis`：∀ {X : Type u_3} {inst : Topologica
lSpace X} [self : PrespectralSpace X],   TopologicalSpace.IsTopologicalBasis {U 
| IsOpen U ∧ IsCompact U}
· 使用定理 `Topology.IsOpenEmbedding.isOpen_iff_image_isOpen`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   Topology.IsOpenEmbedding f → ∀ {s :…
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
· 使用引理 `Topology.IsInducing.isCompact_preimage'`：Topology.IsInducing.isCompact_p
reimage' (hf : IsInducing f) {K : Set Y} (hK : IsCompact K) (Kf : K subseteq ran
ge f) : IsCompact (f ⁻¹' K)
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `Set.SurjOn.subset_range`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.SurjOn f s t → t ⊆ Set.range f
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…

--- 原说明 ---
Let `f : X → Y` be an open embedding of topological spaces.
If `Y` is a prespectral space (i.e., the quasi-compact opens of `Y` form a basis
),
then `X` is also a prespectral space.
-/
lemma Topology.IsOpenEmbedding.prespectralSpace [PrespectralSpace Y]
    {f : X → Y} (hf : IsOpenEmbedding f) :
    PrespectralSpace X where
  isTopologicalBasis := by
    apply isTopologicalBasis_of_isOpen_of_nhds (fun U hU ↦ hU.1) <| fun x U hx hU ↦ ?_
    obtain ⟨V, ⟨hoV, hcV⟩, hfx, hVf⟩ : ∃ V ∈ {V | IsOpen V ∧ IsCompact V}, f x ∈ V ∧ V ⊆ f '' U :=
      (PrespectralSpace.isTopologicalBasis (X := Y)).isOpen_iff.mp
        (hf.isOpen_iff_image_isOpen.mp hU) (f x) ⟨x, hx, rfl⟩
    refine ⟨f ⁻¹' V, ⟨hoV.preimage hf.continuous, ?_⟩, ⟨hfx, fun y hy ↦ ?_⟩⟩
    · exact hf.toIsInducing.isCompact_preimage' hcV <| Set.SurjOn.subset_range hVf
    · exact hf.injective.mem_set_image.mp (hVf hy)
/-
**PrespectralSpace.sigma** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PrespectralSpace.sigma {ι : Type*} (X : ι -> Type*) [forall i, Topological
Space (X i)] [forall i, PrespectralSpace (X i)] : PrespectralSpace (Σ i, X i)
参数：X : ι -> Type*；X i；X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `PrespectralSpace.of_isTopologicalBasis`：PrespectralSpace.of_isTopologica
lBasis {B : Set (Set X)} (basis : IsTopologicalBasis B) (isCompact_basis : foral
l U in B, IsCompact U) : Pre…
· 使用定理 `TopologicalSpace.IsTopologicalBasis.sigma`：∀ {ι : Type u_1} {E : ι → Typ
e u_2} [inst : (i : ι) → TopologicalSpace (E i)] {s : (i : ι) → Set (Set (E i))}
,   (∀ (i : ι), TopologicalSpac…
· 使用定理 `PrespectralSpace.isTopologicalBasis`：∀ {X : Type u_3} {inst : Topologica
lSpace X} [self : PrespectralSpace X],   TopologicalSpace.IsTopologicalBasis {U 
| IsOpen U ∧ IsCompact U}
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `continuous_sigmaMk`：continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι
 σ i)
-/
instance PrespectralSpace.sigma {ι : Type*} (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    [∀ i, PrespectralSpace (X i)] : PrespectralSpace (Σ i, X i) :=
  .of_isTopologicalBasis (IsTopologicalBasis.sigma fun i ↦ isTopologicalBasis) fun U hU ↦ by
    simp_rw [Set.mem_iUnion] at hU
    obtain ⟨i, V, hV, rfl⟩ := hU
    exact hV.2.image continuous_sigmaMk

variable (X) in
/-
**PrespectralSpace.isBasis_opens** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PrespectralSpace.isBasis_opens [PrespectralSpace X] : TopologicalSpace.Ope
ns.IsBasis { U : Opens X | IsCompact (U : Set X) }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PrespectralSpace.isTopologicalBasis`：∀ {X : Type u_3} {inst : Topologica
lSpace X} [self : PrespectralSpace X],   TopologicalSpace.IsTopologicalBasis {U 
| IsOpen U ∧ IsCompact U}
-/
lemma PrespectralSpace.isBasis_opens [PrespectralSpace X] :
    TopologicalSpace.Opens.IsBasis { U : Opens X | IsCompact (U : Set X) } := by
  dsimp only [TopologicalSpace.Opens.IsBasis]
  convert! isTopologicalBasis (X := X)
  ext s
  exact ⟨fun ⟨V, hV, heq⟩ ↦ heq ▸ ⟨V.2, hV⟩, fun h ↦ ⟨⟨s, h.1⟩, h.2, rfl⟩⟩

/-- In a prespectral space, the lattice of opens is determined by its lattice of compact opens. -/
/-
**PrespectralSpace.opensEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PrespectralSpace.opensEquiv [PrespectralSpace X] : Opens X ≃o Order.Ideal 
(CompactOpens X) where toFun U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a prespectral space, the lattice of opens is determined by its lattice of com
pact opens.
-/
def PrespectralSpace.opensEquiv [PrespectralSpace X] :
    Opens X ≃o Order.Ideal (CompactOpens X) where
  toFun U := ⟨⟨{ V | (V : Set X) ⊆ U }, fun U₁ U₂ h₁ h₂ ↦ subset_trans (α := Set X) h₁ h₂⟩,
    ⟨⊥, by simp⟩, fun U₁ h₁ U₂ h₂ ↦ ⟨U₁ ⊔ U₂, by aesop, le_sup_left, le_sup_right⟩⟩
  invFun I := ⨆ U ∈ I, U.toOpens
  left_inv U := by
    apply le_antisymm
    · simp only [iSup_le_iff]
      exact fun _ ↦ id
    · intro x hxU
      obtain ⟨V, ⟨h₁, h₂⟩, hxV, hVU⟩ := isTopologicalBasis.exists_subset_of_mem_open hxU U.2
      simp only [Opens.mem_iSup]
      exact ⟨⟨⟨_, h₂⟩, h₁⟩, hVU, hxV⟩
  right_inv I := by
    ext U
    dsimp
    change U.toOpens ≤ _ ↔ _
    refine ⟨fun H ↦ ?_, fun h ↦ le_iSup₂ (f := fun U (h : U ∈ I) ↦ U.toOpens) U h⟩
    simp only [← SetLike.coe_subset_coe, Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_mk] at H
    obtain ⟨s, hsI, hs, hU⟩ := U.isCompact.elim_finite_subcover_image (fun U _ ↦ U.2) H
    exact I.lower (a := hs.toFinset.sup fun i ↦ i) (by simpa [← SetLike.coe_subset_coe]) (by simpa)
  map_rel_iff' {U V} := by
    change (∀ (W : CompactOpens X), (W : Set X) ⊆ U → (W : Set X) ⊆ V) ↔ U ≤ V
    refine ⟨?_, fun H W ↦ (le_trans · H)⟩
    intro H x hxU
    obtain ⟨W, ⟨h₁, h₂⟩, hxW, hWU⟩ := isTopologicalBasis.exists_subset_of_mem_open hxU U.2
    exact H ⟨⟨W, h₂⟩, h₁⟩ hWU hxW

open TopologicalSpace Opens in
/-- If `X` has a basis of compact opens and `f : X → S` is open, every
compact open of `S` is the image of a compact open of `X`. -/
/-
**IsOpenMap.exists_opens_image_eq_of_prespectralSpace** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：IsOpenMap.exists_opens_image_eq_of_prespectralSpace [PrespectralSpace X] {
f : X -> Y} (hfc : Continuous f) (h : IsOpenMap f) {U : Set Y} (hs : U subseteq 
Set.range f) (hU : IsOpen U) (hc : IsCompact U) : exists (V : Opens X), IsCompac
t V.1 ∧ f '' V = U
参数：hfc : Continuous f；h : IsOpenMap f；hs : U subseteq Set.range f；hU : IsOpen U；
hc : IsCompact U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.isBasis_iff_cover`：isBasis_iff_cover {B : Set (Op
ens α)} : IsBasis B ↔ forall U : Opens α, exists Us, Us subseteq B ∧ U = sSup Us
· 使用引理 `PrespectralSpace.isBasis_opens`：PrespectralSpace.isBasis_opens [Prespect
ralSpace X] : TopologicalSpace.Opens.IsBasis { U : Opens X | IsCompact (U : Set 
X) }
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `TopologicalSpace.Opens.mem_sSup`：mem_sSup {Us : Set (Opens α)} {x : α} :
 x in sSup Us ↔ exists u in Us, x in u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `Set.Finite.isCompact_biUnion`：Set.Finite.isCompact_biUnion {s : Set ι} {
f : ι -> Set X} (hs : s.Finite) (hf : forall i in s, IsCompact (f i)) : IsCompac
t (⋃ i in s, f i)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
If `X` has a basis of compact opens and `f : X → S` is open, every
compact open of `S` is the image of a compact open of `X`.
-/
lemma IsOpenMap.exists_opens_image_eq_of_prespectralSpace [PrespectralSpace X] {f : X → Y}
    (hfc : Continuous f) (h : IsOpenMap f) {U : Set Y} (hs : U ⊆ Set.range f) (hU : IsOpen U)
    (hc : IsCompact U) : ∃ (V : Opens X), IsCompact V.1 ∧ f '' V = U := by
  obtain ⟨Us, hUs, heq⟩ := TopologicalSpace.Opens.isBasis_iff_cover.mp
    (PrespectralSpace.isBasis_opens X) ⟨f ⁻¹' U, hU.preimage hfc⟩
  obtain ⟨t, ht⟩ := by
    refine hc.elim_finite_subcover (fun s : Us ↦ f '' s.1) (fun s ↦ h _ s.1.2) (fun x hx ↦ ?_)
    obtain ⟨x, rfl⟩ := hs hx
    obtain ⟨i, hi, hx⟩ := mem_sSup.mp <| by rwa [← heq]
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, x, hx, rfl⟩
  refine ⟨⨆ s ∈ t, s.1, ?_, ?_⟩
  · simp only [iSup_mk, carrier_eq_coe, coe_mk]
    exact t.finite_toSet.isCompact_biUnion fun i _ ↦ hUs i.2
  · simp only [iSup_mk, carrier_eq_coe, Set.iUnion_coe_set, coe_mk, Set.image_iUnion]
    convert_to ⋃ i ∈ t, f '' i.1 = U
    · simp
    · refine subset_antisymm (fun x ↦ ?_) ht
      simp_rw [Set.mem_iUnion]
      rintro ⟨i, hi, x, hx, rfl⟩
      have := heq ▸ mem_sSup.mpr ⟨i.1, i.2, hx⟩
      exact this
/-
**PrespectralSpace.exists_isCompact_and_isOpen_between** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：PrespectralSpace.exists_isCompact_and_isOpen_between [PrespectralSpace X] 
{K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K subseteq U) : exists (
W : Set X), IsCompact W ∧ IsOpen W ∧ K subseteq W ∧ W subseteq U
参数：hK : IsCompact K；hU : IsOpen U；hKU : K subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.induction_on`：IsCompact.induction_on (hs : IsCompact s) {p : S
et X -> Prop} (he : p ∅) (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hun
ion : forall…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `IsCompact.union`：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) :
 IsCompact (s union t)
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `PrespectralSpace.isTopologicalBasis`：∀ {X : Type u_3} {inst : Topologica
lSpace X} [self : PrespectralSpace X],   TopologicalSpace.IsTopologicalBasis {U 
| IsOpen U ∧ IsCompact U}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
lemma PrespectralSpace.exists_isCompact_and_isOpen_between [PrespectralSpace X] {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (W : Set X), IsCompact W ∧ IsOpen W ∧ K ⊆ W ∧ W ⊆ U := by
  refine hK.induction_on ⟨∅, by simp⟩ (fun s t hst ⟨W, Wc, Wo, hKW, hWU⟩ ↦ ?_) ?_ ?_
  · use W, Wc, Wo, subset_trans hst hKW, hWU
  · intro s t ⟨W₁, Wc₁, Wo₁, hKW₁, hWU₁⟩ ⟨W₂, Wc₂, Wo₂, hKW₂, hWU₂⟩
    exact ⟨W₁ ∪ W₂, Wc₁.union Wc₂, Wo₁.union Wo₂, Set.union_subset_union hKW₁ hKW₂,
      Set.union_subset hWU₁ hWU₂⟩
  · intro x hx
    obtain ⟨V, h, hxV, hVU⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (hKU hx) hU
    exact ⟨V, mem_nhdsWithin.mpr ⟨V, h.1, hxV, Set.inter_subset_left⟩, V, h.2, h.1, subset_rfl, hVU⟩
/-
**PrespectralSpace.exists_isClosed_of_not_isPreirreducible** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：PrespectralSpace.exists_isClosed_of_not_isPreirreducible [PrespectralSpace
 X] (Z : Set X) (hZ : ¬ IsPreirreducible Z) : exists (A B : Set X), IsClosed A ∧
 IsClosed B ∧ IsCompact Aᶜ ∧ IsCompact Bᶜ ∧ Z subseteq A union B ∧ (Z inter Aᶜ).
Nonempty ∧ (Z inter Bᶜ).Nonempty
参数：Z : Set X；hZ : ¬ IsPreirreducible Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen_iff`：∀ {α : Type u} [t : Topo
logicalSpace α] {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTopologicalB
asis b → (IsOpen s ↔ ∀ a ∈ s, ∃ t ∈ …
· 使用定理 `PrespectralSpace.isTopologicalBasis`：∀ {X : Type u_3} {inst : Topologica
lSpace X} [self : PrespectralSpace X],   TopologicalSpace.IsTopologicalBasis {U 
| IsOpen U ∧ IsCompact U}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma PrespectralSpace.exists_isClosed_of_not_isPreirreducible [PrespectralSpace X] (Z : Set X)
    (hZ : ¬ IsPreirreducible Z) :
    ∃ (A B : Set X), IsClosed A ∧ IsClosed B ∧ IsCompact Aᶜ ∧ IsCompact Bᶜ ∧
      Z ⊆ A ∪ B ∧ (Z ∩ Aᶜ).Nonempty ∧ (Z ∩ Bᶜ).Nonempty := by
  simp only [IsPreirreducible, not_forall] at hZ
  rcases hZ with ⟨U₁, U₂, hU₁, hU₂, hU₁Z, hU₂Z, hU₁₂⟩
  rw [Set.not_nonempty_iff_eq_empty, ← Set.subset_empty_iff] at hU₁₂
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ ∈ U₁, x₁ ∈ Z ∧ x₁ ∉ U₂ := by
    obtain ⟨x, hx⟩ := hU₁Z
    use x, hx.2, hx.1, fun h₂ ↦ hU₁₂ ⟨hx.1, hx.2, h₂⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ ∈ U₂, x₂ ∈ Z ∧ x₂ ∉ U₁ := by
    obtain ⟨x, hx⟩ := hU₂Z
    use x, hx.2, hx.1, fun h₁ ↦ hU₁₂ ⟨hx.1, h₁, hx.2⟩
  rw [PrespectralSpace.isTopologicalBasis.isOpen_iff] at hU₁ hU₂
  obtain ⟨W₁, hW₁⟩ := hU₁ x₁ hx₁.1
  obtain ⟨W₂, hW₂⟩ := hU₂ x₂ hx₂.1
  refine ⟨W₁ᶜ, W₂ᶜ, by simpa using hW₁.1.1, by simpa using hW₂.1.1, by simp [hW₁.1.2],
    by simp [hW₂.1.2], fun z hz ↦ ?_, ⟨x₁, by grind⟩, ⟨x₂, by grind⟩⟩
  · by_contra! hc
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hc
    exact hU₁₂ ⟨hz, hW₁.2.2 hc.1, hW₂.2.2 hc.2⟩
