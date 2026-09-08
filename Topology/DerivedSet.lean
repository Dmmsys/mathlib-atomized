/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.Topology.Perfect
public import Mathlib.Tactic.Peel

/-!
# Derived set

This file defines the derived set of a set, the set of all `AccPt`s of its principal filter,
and proves some properties of it.

-/

@[expose] public section

open Filter Topology

variable {X : Type*} [TopologicalSpace X]

/-
**AccPt.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AccPt.map {β : Type*} [TopologicalSpace β] {F : Filter X} {x : X} (h : Acc
Pt x F) {f : X -> β} (hf1 : ContinuousAt f x) (hf2 : Function.Injective f) : Acc
Pt (f x) (map f F)
参数：h : AccPt x F；hf1 : ContinuousAt f x；hf2 : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_inf`：map_inf {f g : Filter α} {m : α -> β} (h : Injective m) 
: map m (f ⊓ g) = map m f ⊓ map m g
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem AccPt.map {β : Type*} [TopologicalSpace β] {F : Filter X} {x : X}
    (h : AccPt x F) {f : X → β} (hf1 : ContinuousAt f x) (hf2 : Function.Injective f) :
    AccPt (f x) (map f F) := by
  apply map_neBot (m := f) (hf := h) |>.mono
  rw [Filter.map_inf hf2]
  gcongr
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hf1.continuousWithinAt
  simpa [hf2.eq_iff] using! eventually_mem_nhdsWithin

/--
The derived set of a set is the set of all accumulation points of it.
-/
/-
**derivedSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：derivedSet (A : Set X) : Set X
参数：A : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derived set of a set is the set of all accumulation points of it.
-/
def derivedSet (A : Set X) : Set X := {x | AccPt x (𝓟 A)}

@[simp]
/-
**mem_derivedSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_derivedSet {A : Set X} {x : X} : x in derivedSet A ↔ AccPt x (𝓟 A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_derivedSet {A : Set X} {x : X} : x ∈ derivedSet A ↔ AccPt x (𝓟 A) := Iff.rfl
/-
**derivedSet_union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：derivedSet_union (A B : Set X) : derivedSet (A union B) = derivedSet A uni
on derivedSet B
参数：A B : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma derivedSet_union (A B : Set X) : derivedSet (A ∪ B) = derivedSet A ∪ derivedSet B := by
  ext x
  simp [derivedSet, ← sup_principal, accPt_sup]
/-
**derivedSet_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：derivedSet_mono (A B : Set X) (h : A subseteq B) : derivedSet A subseteq d
erivedSet B
参数：A B : Set X；h : A subseteq B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AccPt.mono`：AccPt.mono {F G : Filter X} (h : AccPt x F) (hFG : F <= G) :
 AccPt x G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.mem_principal`：∀ {α : Type u_1} {s t : Set α}, s ∈ Filter.princip
al t ↔ t ⊆ s
-/
lemma derivedSet_mono (A B : Set X) (h : A ⊆ B) : derivedSet A ⊆ derivedSet B :=
  fun _ hx ↦ hx.mono <| le_principal_iff.mpr <| mem_principal.mpr h

/-- The relative derived set operator viewed as a monotone self-map of `Set X`. -/
/-
**relDerivedSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：relDerivedSet : Set X ->o Set X where toFun s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relative derived set operator viewed as a monotone self-map of `Set X`.
-/
def relDerivedSet : Set X →o Set X where
  toFun s := derivedSet s ∩ s
  monotone' s t h := Set.inter_subset_inter (derivedSet_mono s t h) h
/-
**relDerivedSet_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] (A : Set X), relDerivedSet A 
= derivedSet A ∩ A
参数：A : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma relDerivedSet_apply (A : Set X) : relDerivedSet A = derivedSet A ∩ A := rfl
/-
**relDerivedSet_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：relDerivedSet_subset {A : Set X} : relDerivedSet A subseteq A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma relDerivedSet_subset {A : Set X} : relDerivedSet A ⊆ A :=
  Set.inter_subset_right
/-
**Continuous.image_derivedSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.image_derivedSet {β : Type*} [TopologicalSpace β] {A : Set X} {
f : X -> β} (hf1 : Continuous f) (hf2 : Function.Injective f) : f '' derivedSet 
A subseteq derivedSet (f '' A)
参数：hf1 : Continuous f；hf2 : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `AccPt.map`：AccPt.map {β : Type*} [TopologicalSpace β] {F : Filter X} {x 
: X} (h : AccPt x F) {f : X -> β} (hf1 : ContinuousAt f x) (hf2 : Function.Inje…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.image_derivedSet {β : Type*} [TopologicalSpace β] {A : Set X} {f : X → β}
    (hf1 : Continuous f) (hf2 : Function.Injective f) :
    f '' derivedSet A ⊆ derivedSet (f '' A) := by
  intro x hx
  simp only [Set.mem_image, mem_derivedSet] at hx
  obtain ⟨y, hy1, rfl⟩ := hx
  convert! hy1.map hf1.continuousAt hf2
  simp
/-
**derivedSet_subset_closure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：derivedSet_subset_closure (A : Set X) : derivedSet A subseteq closure A
参数：A : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
· 使用定理 `AccPt.clusterPt`：AccPt.clusterPt {x : X} {F : Filter X} (h : AccPt x F) 
: ClusterPt x F
-/
lemma derivedSet_subset_closure (A : Set X) : derivedSet A ⊆ closure A :=
  fun _ hx ↦ mem_closure_iff_clusterPt.mpr hx.clusterPt
/-
**isClosed_iff_derivedSet_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_iff_derivedSet_subset (A : Set X) : IsClosed A ↔ derivedSet A sub
seteq A where .trans h.closure_subset mp h
参数：A : Set X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `derivedSet_subset_closure`：derivedSet_subset_closure (A : Set X) : deriv
edSet A subseteq closure A
· 使用定理 `IsClosed.closure_subset`：IsClosed.closure_subset (hs : IsClosed s) : clo
sure s subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isClosed_iff_clusterPt`：isClosed_iff_clusterPt : IsClosed s ↔ forall a, 
ClusterPt a (𝓟 s) -> a in s
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `accPt_principal_iff_clusterPt`：accPt_principal_iff_clusterPt {x : X} {C 
: Set X} : AccPt x (𝓟 C) ↔ ClusterPt x (𝓟 (C \ { x }))
-/
lemma isClosed_iff_derivedSet_subset (A : Set X) : IsClosed A ↔ derivedSet A ⊆ A where
  mp h := derivedSet_subset_closure A |>.trans h.closure_subset
  mpr h := by
    rw [isClosed_iff_clusterPt]
    intro a ha
    by_contra! nh
    have : A = A \ {a} := by simp [nh]
    rw [this, ← accPt_principal_iff_clusterPt] at ha
    exact nh (h ha)
/-
**IsClosed.relDerivedSet_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.relDerivedSet_eq {A : Set X} (hA : IsClosed A) : relDerivedSet A 
= derivedSet A
参数：hA : IsClosed A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isClosed_iff_derivedSet_subset`：isClosed_iff_derivedSet_subset (A : Set 
X) : IsClosed A ↔ derivedSet A subseteq A where .trans h.closure_subset mp h
-/
lemma IsClosed.relDerivedSet_eq {A : Set X} (hA : IsClosed A) :
    relDerivedSet A = derivedSet A := by
  simpa using (isClosed_iff_derivedSet_subset A).mp hA
/-
**closure_eq_self_union_derivedSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：closure_eq_self_union_derivedSet (A : Set X) : closure A = A union derived
Set A
参数：A : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `closure_eq_cluster_pts`：closure_eq_cluster_pts : closure s = { a | Clust
erPt a (𝓟 s) }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma closure_eq_self_union_derivedSet (A : Set X) : closure A = A ∪ derivedSet A := by
  ext
  simp [closure_eq_cluster_pts, clusterPt_principal]

/-- In a `T1Space`, the `derivedSet` of the closure of a set is equal to the derived set of the
set itself.

Note: this doesn't hold in a space with the indiscrete topology. For example, if `X` is a type with
two elements, `x` and `y`, and `A := {x}`, then `closure A = Set.univ` and `derivedSet A = {y}`,
but `derivedSet Set.univ = Set.univ`. -/
/-
**derivedSet_closure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：derivedSet_closure [T1Space X] (A : Set X) : derivedSet (closure A) = deri
vedSet A
参数：A : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mem_derivedSet`：mem_derivedSet {A : Set X} {x : X} : x in derivedSet A ↔
 AccPt x (𝓟 A)
· 使用定理 `AccPt.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (F : Fi
lter X), AccPt x F = (nhdsWithin x {x}ᶜ ⊓ F).NeBot
· 使用定理 `Filter.HasBasis.inf_principal_neBot_iff`：∀ {α : Type u_1} {ι : Sort u_4}
 {l : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {t : Set α}
, (l ⊓ Filter.principal t).Ne…
· 使用定理 `nhdsWithin_basis_open`：nhdsWithin_basis_open (a : α) (t : Set α) : (𝓝[t]
 a).HasBasis (fun u => a in u ∧ IsOpen u) fun u => u inter t
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff`：mem_closure_iff : x in closure s ↔ forall o, IsOpen o -
> x in o -> (o inter s).Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `derivedSet_mono`：derivedSet_mono (A B : Set X) (h : A subseteq B) : deri
vedSet A subseteq derivedSet B
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
In a `T1Space`, the `derivedSet` of the closure of a set is equal to the derived
 set of the
set itself.

Note: this doesn't hold in a space with the indiscrete topology. For example, if
 `X` is a type with
two elements, `x` and `y`, and `A := {x}`, then `closure A = Set.univ` and `deri
vedSet A = {y}`,
but `derivedSet Set.univ = Set.univ`.
-/
lemma derivedSet_closure [T1Space X] (A : Set X) : derivedSet (closure A) = derivedSet A := by
  refine le_antisymm (fun x hx => ?_) (derivedSet_mono _ _ subset_closure)
  rw [mem_derivedSet, AccPt, (nhdsWithin_basis_open x {x}ᶜ).inf_principal_neBot_iff] at hx ⊢
  peel hx with u hu _
  obtain ⟨-, hu_open⟩ := hu
  exact mem_closure_iff.mp this.some_mem.2 (u ∩ {x}ᶜ) (hu_open.inter isOpen_compl_singleton)
    this.some_mem.1

@[simp]
/-
**isClosed_derivedSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_derivedSet [T1Space X] (A : Set X) : IsClosed (derivedSet A)
参数：A : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `derivedSet_closure`：derivedSet_closure [T1Space X] (A : Set X) : derived
Set (closure A) = derivedSet A
· 使用引理 `isClosed_iff_derivedSet_subset`：isClosed_iff_derivedSet_subset (A : Set 
X) : IsClosed A ↔ derivedSet A subseteq A where .trans h.closure_subset mp h
· 使用引理 `derivedSet_mono`：derivedSet_mono (A B : Set X) (h : A subseteq B) : deri
vedSet A subseteq derivedSet B
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma isClosed_derivedSet [T1Space X] (A : Set X) : IsClosed (derivedSet A) := by
  rw [← derivedSet_closure, isClosed_iff_derivedSet_subset]
  apply derivedSet_mono
  simp [← isClosed_iff_derivedSet_subset]
/-
**preperfect_iff_subset_derivedSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preperfect_iff_subset_derivedSet {U : Set X} : Preperfect U ↔ U subseteq d
erivedSet U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma preperfect_iff_subset_derivedSet {U : Set X} : Preperfect U ↔ U ⊆ derivedSet U :=
  Iff.rfl
/-
**preperfect_iff_eq_relDerivedSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preperfect_iff_eq_relDerivedSet {U : Set X} : Preperfect U ↔ U = relDerive
dSet U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma preperfect_iff_eq_relDerivedSet {U : Set X} : Preperfect U ↔ U = relDerivedSet U := by
  simp [preperfect_iff_subset_derivedSet]
/-
**perfect_iff_eq_derivedSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：perfect_iff_eq_derivedSet {U : Set X} : Perfect U ↔ U = derivedSet U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `perfect_def`：∀ {α : Type u_1} [inst : TopologicalSpace α] (C : Set α), P
erfect C ↔ IsClosed C ∧ Preperfect C
· 使用引理 `isClosed_iff_derivedSet_subset`：isClosed_iff_derivedSet_subset (A : Set 
X) : IsClosed A ↔ derivedSet A subseteq A where .trans h.closure_subset mp h
· 使用引理 `preperfect_iff_subset_derivedSet`：preperfect_iff_subset_derivedSet {U : 
Set X} : Preperfect U ↔ U subseteq derivedSet U
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subset_antisymm_iff`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a = b ↔ a ⊆ b ∧ b ⊆ a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma perfect_iff_eq_derivedSet {U : Set X} : Perfect U ↔ U = derivedSet U := by
  rw [perfect_def, isClosed_iff_derivedSet_subset, preperfect_iff_subset_derivedSet,
    ← subset_antisymm_iff, eq_comm]
/-
**IsPreconnected.inter_derivedSet_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsPreconnected.inter_derivedSet_nonempty [T1Space X] {U : Set X} (hs : IsP
reconnected U) (a b : Set X) (h : U subseteq a union b) (ha : (U inter derivedSe
t a).Nonempty) (hb : (U inter derivedSet b).Nonempty) : (U inter (derivedSet a i
nter derivedSet b)).Nonempty
参数：hs : IsPreconnected U；a b : Set X；h : U subseteq a union b；ha : (U inter deri
vedSet a).Nonempty；hb : (U inter derivedSet b).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPreconnected_closed_iff`：isPreconnected_closed_iff {s : Set α} : IsPre
connected s ↔ forall t t', IsClosed t -> IsClosed t' -> s subseteq t union t' ->
 (s inter t).No…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `IsPreconnected.preperfect_of_nontrivial`：IsPreconnected.preperfect_of_no
ntrivial [T1Space α] {U : Set α} (hu : U.Nontrivial) (h : IsPreconnected U) : Pr
eperfect U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `derivedSet_union`：derivedSet_union (A B : Set X) : derivedSet (A union B
) = derivedSet A union derivedSet B
· 使用引理 `derivedSet_mono`：derivedSet_mono (A B : Set X) (h : A subseteq B) : deri
vedSet A subseteq derivedSet B
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Set.Nonempty.exists_eq_singleton_or_nontrivial`：∀ {α : Type u} {s : Set 
α}, s.Nonempty → (∃ a, s = {a}) ∨ s.Nontrivial
· 使用定理 `Set.Nonempty.left`：∀ {α : Type u} {s t : Set α}, (s ∩ t).Nonempty → s.No
nempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.singleton_inter_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ s 
→ {a} ∩ s = {a}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma IsPreconnected.inter_derivedSet_nonempty [T1Space X] {U : Set X} (hs : IsPreconnected U)
    (a b : Set X) (h : U ⊆ a ∪ b) (ha : (U ∩ derivedSet a).Nonempty)
    (hb : (U ∩ derivedSet b).Nonempty) : (U ∩ (derivedSet a ∩ derivedSet b)).Nonempty := by
  by_cases hu : U.Nontrivial
  · apply isPreconnected_closed_iff.mp hs
    · simp
    · simp
    · trans derivedSet U
      · apply hs.preperfect_of_nontrivial hu
      · rw [← derivedSet_union]
        exact derivedSet_mono _ _ h
    · exact ha
    · exact hb
  · obtain ⟨x, hx⟩ := ha.left.exists_eq_singleton_or_nontrivial.resolve_right hu
    simp_all
