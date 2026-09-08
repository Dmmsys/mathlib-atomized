/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Sigma-compactness in topological spaces

## Main definitions
* `IsSigmaCompact`: a set that is the union of countably many compact sets.
* `SigmaCompactSpace X`: `X` is a σ-compact topological space; i.e., is the union
  of a countable collection of compact subspaces.

-/

@[expose] public section

open Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

/-- A subset `s ⊆ X` is called **σ-compact** if it is the union of countably many compact sets. -/
/-
**IsSigmaCompact** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsSigmaCompact (s : Set X) : Prop
参数：s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset `s ⊆ X` is called **σ-compact** if it is the union of countably many co
mpact sets.
-/
def IsSigmaCompact (s : Set X) : Prop :=
  ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = s

/-- Compact sets are σ-compact. -/
/-
**IsCompact.isSigmaCompact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.isSigmaCompact {s : Set X} (hs : IsCompact s) : IsSigmaCompact s
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.iUnion_const`：iUnion_const (s : Set β) : ⋃ _ : ι, s = s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
Compact sets are σ-compact.
-/
lemma IsCompact.isSigmaCompact {s : Set X} (hs : IsCompact s) : IsSigmaCompact s :=
  ⟨fun _ => s, fun _ => hs, iUnion_const _⟩

/-- The empty set is σ-compact. -/
@[simp]
/-
**isSigmaCompact_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSigmaCompact_empty : IsSigmaCompact (∅ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompact.isSigmaCompact`：IsCompact.isSigmaCompact {s : Set X} (hs : IsC
ompact s) : IsSigmaCompact s
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)

--- 原说明 ---
The empty set is σ-compact.
-/
lemma isSigmaCompact_empty : IsSigmaCompact (∅ : Set X) :=
  IsCompact.isSigmaCompact isCompact_empty

/-- Countable unions of compact sets are σ-compact. -/
/-
**isSigmaCompact_iUnion_of_isCompact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSigmaCompact_iUnion_of_isCompact [hι : Countable ι] (s : ι -> Set X) (hc
omp : forall i, IsCompact (s i)) : IsSigmaCompact (⋃ i, s i)
参数：s : ι -> Set X；hcomp : forall i, IsCompact (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `countable_iff_exists_surjective`：countable_iff_exists_surjective [Nonemp
ty α] : Countable α ↔ exists f : Nat -> α, Surjective f
· 使用定理 `Function.Surjective.iUnion_comp`：iUnion_comp {f : ι -> ι₂} (hf : Surject
ive f) (g : ι₂ -> Set α) : ⋃ x, g (f x) = ⋃ y, g y

--- 原说明 ---
Countable unions of compact sets are σ-compact.
-/
lemma isSigmaCompact_iUnion_of_isCompact [hι : Countable ι] (s : ι → Set X)
    (hcomp : ∀ i, IsCompact (s i)) : IsSigmaCompact (⋃ i, s i) := by
  rcases isEmpty_or_nonempty ι
  · simp only [iUnion_of_empty, isSigmaCompact_empty]
  · -- If ι is non-empty, choose a surjection f : ℕ → ι, this yields a map ℕ → Set X.
    obtain ⟨f, hf⟩ := countable_iff_exists_surjective.mp hι
    exact ⟨s ∘ f, fun n ↦ hcomp (f n), Function.Surjective.iUnion_comp hf _⟩

/-- Countable unions of compact sets are σ-compact. -/
/-
**isSigmaCompact_sUnion_of_isCompact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSigmaCompact_sUnion_of_isCompact {S : Set (Set X)} (hc : Set.Countable S
) (hcomp : forall (s : Set X), s in S -> IsCompact s) : IsSigmaCompact (⋃₀ S)
参数：Set X；hc : Set.Countable S；hcomp : forall (s : Set X), s in S -> IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.countable_coe_iff`：countable_coe_iff {s : Set α} : Countable s ↔ s.C
ountable
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用引理 `isSigmaCompact_iUnion_of_isCompact`：isSigmaCompact_iUnion_of_isCompact [
hι : Countable ι] (s : ι -> Set X) (hcomp : forall i, IsCompact (s i)) : IsSigma
Compact (⋃ i, s i)

--- 原说明 ---
Countable unions of compact sets are σ-compact.
-/
lemma isSigmaCompact_sUnion_of_isCompact {S : Set (Set X)} (hc : Set.Countable S)
    (hcomp : ∀ (s : Set X), s ∈ S → IsCompact s) : IsSigmaCompact (⋃₀ S) := by
  have : Countable S := countable_coe_iff.mpr hc
  rw [sUnion_eq_iUnion]
  apply isSigmaCompact_iUnion_of_isCompact _ (fun ⟨s, hs⟩ ↦ hcomp s hs)

/-- Countable unions of σ-compact sets are σ-compact. -/
/-
**isSigmaCompact_iUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSigmaCompact_iUnion [Countable ι] (s : ι -> Set X) (hcomp : forall i, Is
SigmaCompact (s i)) : IsSigmaCompact (⋃ i, s i)
参数：s : ι -> Set X；hcomp : forall i, IsSigmaCompact (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.uncurry_def`：uncurry_def {α β γ} (f : α -> β -> γ) : uncurry f 
= fun p => f p.1 p.2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.iUnion_prod'`：iUnion_prod' (f : β × γ -> Set α) : ⋃ x : β × γ, f x =
 ⋃ (i : β) (j : γ), f (i, j)
· 使用引理 `isSigmaCompact_iUnion_of_isCompact`：isSigmaCompact_iUnion_of_isCompact [
hι : Countable ι] (s : ι -> Set X) (hcomp : forall i, IsCompact (s i)) : IsSigma
Compact (⋃ i, s i)
· 使用定理 `instCountableProd`：∀ {α : Type u} {β : Type v} [Countable α] [Countable 
β], Countable (α × β)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Countable unions of σ-compact sets are σ-compact.
-/
lemma isSigmaCompact_iUnion [Countable ι] (s : ι → Set X)
    (hcomp : ∀ i, IsSigmaCompact (s i)) : IsSigmaCompact (⋃ i, s i) := by
  -- Choose a decomposition s_i = ⋃ K_i,j for each i.
  choose K hcomp hcov using fun i ↦ hcomp i
  -- Then, we have a countable union of countable unions of compact sets, i.e. countably many.
  have := calc
    ⋃ i, s i
    _ = ⋃ i, ⋃ n, (K i n) := by simp_rw [hcov]
    _ = ⋃ (i) (n : ℕ), (K.uncurry ⟨i, n⟩) := by rw [Function.uncurry_def]
    _ = ⋃ x, K.uncurry x := by rw [← iUnion_prod']
  rw [this]
  exact isSigmaCompact_iUnion_of_isCompact K.uncurry fun x ↦ (hcomp x.1 x.2)

/-- Countable unions of σ-compact sets are σ-compact. -/
/-
**isSigmaCompact_sUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSigmaCompact_sUnion (S : Set (Set X)) (hc : Set.Countable S) (hcomp : fo
rall s : S, IsSigmaCompact s (X
参数：S : Set (Set X)；hc : Set.Countable S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.countable_coe_iff`：countable_coe_iff {s : Set α} : Countable s ↔ s.C
ountable
· 使用引理 `isSigmaCompact_iUnion`：isSigmaCompact_iUnion [Countable ι] (s : ι -> Set
 X) (hcomp : forall i, IsSigmaCompact (s i)) : IsSigmaCompact (⋃ i, s i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i

--- 原说明 ---
Countable unions of σ-compact sets are σ-compact.
-/
lemma isSigmaCompact_sUnion (S : Set (Set X)) (hc : Set.Countable S)
    (hcomp : ∀ s : S, IsSigmaCompact s (X := X)) : IsSigmaCompact (⋃₀ S) := by
  have : Countable S := countable_coe_iff.mpr hc
  apply sUnion_eq_iUnion.symm ▸ isSigmaCompact_iUnion _ hcomp

/-- Countable unions of σ-compact sets are σ-compact. -/
/-
**isSigmaCompact_biUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSigmaCompact_biUnion {s : Set ι} {S : ι -> Set X} (hc : Set.Countable s)
 (hcomp : forall (i : ι), i in s -> IsSigmaCompact (S i)) : IsSigmaCompact (⋃ (i
 : ι) (_ : i in s), S i)
参数：hc : Set.Countable s；hcomp : forall (i : ι), i in s -> IsSigmaCompact (S i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.countable_coe_iff`：countable_coe_iff {s : Set α} : Countable s ↔ s.C
ountable
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用引理 `isSigmaCompact_iUnion`：isSigmaCompact_iUnion [Countable ι] (s : ι -> Set
 X) (hcomp : forall i, IsSigmaCompact (s i)) : IsSigmaCompact (⋃ i, s i)

--- 原说明 ---
Countable unions of σ-compact sets are σ-compact.
-/
lemma isSigmaCompact_biUnion {s : Set ι} {S : ι → Set X} (hc : Set.Countable s)
    (hcomp : ∀ (i : ι), i ∈ s → IsSigmaCompact (S i)) :
    IsSigmaCompact (⋃ (i : ι) (_ : i ∈ s), S i) := by
  have : Countable ↑s := countable_coe_iff.mpr hc
  rw [biUnion_eq_iUnion]
  exact isSigmaCompact_iUnion _ (fun ⟨i', hi'⟩ ↦ hcomp i' hi')

/-- A closed subset of a σ-compact set is σ-compact. -/
/-
**IsSigmaCompact.of_isClosed_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSigmaCompact.of_isClosed_subset {s t : Set X} (ht : IsSigmaCompact t) (h
s : IsClosed s) (h : s subseteq t) : IsSigmaCompact s
参数：ht : IsSigmaCompact t；hs : IsClosed s；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.inter_left`：IsCompact.inter_left (ht : IsCompact t) (hs : IsCl
osed s) : IsCompact (s inter t)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t

--- 原说明 ---
A closed subset of a σ-compact set is σ-compact.
-/
lemma IsSigmaCompact.of_isClosed_subset {s t : Set X} (ht : IsSigmaCompact t)
    (hs : IsClosed s) (h : s ⊆ t) : IsSigmaCompact s := by
  rcases ht with ⟨K, hcompact, hcov⟩
  refine ⟨(fun n ↦ s ∩ (K n)), fun n ↦ (hcompact n).inter_left hs, ?_⟩
  rw [← inter_iUnion, hcov]
  exact inter_eq_left.mpr h

/-- If `s` is σ-compact and `f` is continuous on `s`, `f(s)` is σ-compact. -/
/-
**IsSigmaCompact.image_of_continuousOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSigmaCompact.image_of_continuousOn {f : X -> Y} {s : Set X} (hs : IsSigm
aCompact s) (hf : ContinuousOn f s) : IsSigmaCompact (f '' s)
参数：hs : IsSigmaCompact s；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i

--- 原说明 ---
If `s` is σ-compact and `f` is continuous on `s`, `f(s)` is σ-compact.
-/
lemma IsSigmaCompact.image_of_continuousOn {f : X → Y} {s : Set X} (hs : IsSigmaCompact s)
    (hf : ContinuousOn f s) : IsSigmaCompact (f '' s) := by
  rcases hs with ⟨K, hcompact, hcov⟩
  refine ⟨fun n ↦ f '' K n, ?_, hcov.symm ▸ image_iUnion.symm⟩
  exact fun n ↦ (hcompact n).image_of_continuousOn (hf.mono (hcov.symm ▸ subset_iUnion K n))

/-- If `s` is σ-compact and `f` continuous, `f(s)` is σ-compact. -/
/-
**IsSigmaCompact.image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSigmaCompact.image {f : X -> Y} (hf : Continuous f) {s : Set X} (hs : Is
SigmaCompact s) : IsSigmaCompact (f '' s)
参数：hf : Continuous f；hs : IsSigmaCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSigmaCompact.image_of_continuousOn`：IsSigmaCompact.image_of_continuous
On {f : X -> Y} {s : Set X} (hs : IsSigmaCompact s) (hf : ContinuousOn f s) : Is
SigmaCompact (f '' s)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s

--- 原说明 ---
If `s` is σ-compact and `f` continuous, `f(s)` is σ-compact.
-/
lemma IsSigmaCompact.image {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsSigmaCompact s) :
    IsSigmaCompact (f '' s) := hs.image_of_continuousOn hf.continuousOn

/-- If `f : X → Y` is an inducing map, the image `f '' s` of a set `s` is σ-compact
  if and only `s` is σ-compact. -/
/-
**Topology.IsInducing.isSigmaCompact_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.isSigmaCompact_iff {f : X -> Y} {s : Set X} (hf : IsIn
ducing f) : IsSigmaCompact s ↔ IsSigmaCompact (f '' s)
参数：hf : IsInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSigmaCompact.image`：IsSigmaCompact.image {f : X -> Y} (hf : Continuous
 f) {s : Set X} (hs : IsSigmaCompact s) : IsSigmaCompact (f '' s)
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_inter`：image_preimage_inter (f : α -> β) (s : Set α) 
(t : Set β) : f '' (f ⁻¹' t inter s) = t inter f '' s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Topology.IsInducing.isCompact_iff`：Topology.IsInducing.isCompact_iff {f 
: X -> Y} (hf : IsInducing f) : IsCompact s ↔ IsCompact (f '' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s

--- 原说明 ---
If `f : X → Y` is an inducing map, the image `f '' s` of a set `s` is σ-compact
  if and only `s` is σ-compact.
-/
lemma Topology.IsInducing.isSigmaCompact_iff {f : X → Y} {s : Set X}
    (hf : IsInducing f) : IsSigmaCompact s ↔ IsSigmaCompact (f '' s) := by
  constructor
  · exact fun h ↦ h.image hf.continuous
  · rintro ⟨L, hcomp, hcov⟩
    -- Suppose f(s) is σ-compact; we want to show s is σ-compact.
    -- Write f(s) as a union of compact sets L n, so s = ⋃ K n with K n := f⁻¹(L n) ∩ s.
    -- Since f is inducing, each K n is compact iff L n is.
    refine ⟨fun n ↦ f ⁻¹' (L n) ∩ s, ?_, ?_⟩
    · intro n
      have : f '' (f ⁻¹' (L n) ∩ s) = L n := by
        rw [image_preimage_inter, inter_eq_left.mpr]
        exact (subset_iUnion _ n).trans hcov.le
      apply hf.isCompact_iff.mpr (this.symm ▸ (hcomp n))
    · calc ⋃ n, f ⁻¹' L n ∩ s
        _ = f ⁻¹' (⋃ n, L n) ∩ s := by rw [preimage_iUnion, iUnion_inter]
        _ = f ⁻¹' (f '' s) ∩ s := by rw [hcov]
        _ = s := inter_eq_right.mpr (subset_preimage_image _ _)

/-- If `f : X → Y` is an embedding, the image `f '' s` of a set `s` is σ-compact
if and only `s` is σ-compact. -/
/-
**Topology.IsEmbedding.isSigmaCompact_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.isSigmaCompact_iff {f : X -> Y} {s : Set X} (hf : IsE
mbedding f) : IsSigmaCompact s ↔ IsSigmaCompact (f '' s)
参数：hf : IsEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.isSigmaCompact_iff`：Topology.IsInducing.isSigmaCompa
ct_iff {f : X -> Y} {s : Set X} (hf : IsInducing f) : IsSigmaCompact s ↔ IsSigma
Compact (f '' s)
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…

--- 原说明 ---
If `f : X → Y` is an embedding, the image `f '' s` of a set `s` is σ-compact
if and only `s` is σ-compact.
-/
lemma Topology.IsEmbedding.isSigmaCompact_iff {f : X → Y} {s : Set X}
    (hf : IsEmbedding f) : IsSigmaCompact s ↔ IsSigmaCompact (f '' s) :=
  hf.isInducing.isSigmaCompact_iff

/-- Sets of subtype are σ-compact iff the image under a coercion is. -/
/-
**Subtype.isSigmaCompact_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subtype.isSigmaCompact_iff {p : X -> Prop} {s : Set { a // p a }} : IsSigm
aCompact s ↔ IsSigmaCompact ((↑) '' s : Set X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsEmbedding.isSigmaCompact_iff`：Topology.IsEmbedding.isSigmaCom
pact_iff {f : X -> Y} {s : Set X} (hf : IsEmbedding f) : IsSigmaCompact s ↔ IsSi
gmaCompact (f '' s)
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)

--- 原说明 ---
Sets of subtype are σ-compact iff the image under a coercion is.
-/
lemma Subtype.isSigmaCompact_iff {p : X → Prop} {s : Set { a // p a }} :
    IsSigmaCompact s ↔ IsSigmaCompact ((↑) '' s : Set X) :=
  IsEmbedding.subtypeVal.isSigmaCompact_iff

/-- A σ-compact space is a space that is the union of a countable collection of compact subspaces.
  Note that a locally compact separable T₂ space need not be σ-compact.
  The sequence can be extracted using `compactCovering`. -/
/-
**SigmaCompactSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_4) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A σ-compact space is a space that is the union of a countable collection of comp
act subspaces.
  Note that a locally compact separable T₂ space need not be σ-compact.
  The sequence can be extracted using `compactCovering`.
-/
class SigmaCompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a σ-compact space, `Set.univ` is a σ-compact set. -/
  isSigmaCompact_univ : IsSigmaCompact (univ : Set X)

/-- A topological space is σ-compact iff `univ` is σ-compact. -/
/-
**isSigmaCompact_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSigmaCompact_univ_iff : IsSigmaCompact (univ : Set X) ↔ SigmaCompactSpac
e X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SigmaCompactSpace.isSigmaCompact_univ`：∀ {X : Type u_4} {inst : Topologi
calSpace X} [self : SigmaCompactSpace X], IsSigmaCompact Set.univ

--- 原说明 ---
A topological space is σ-compact iff `univ` is σ-compact.
-/
lemma isSigmaCompact_univ_iff : IsSigmaCompact (univ : Set X) ↔ SigmaCompactSpace X :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

/-- In a σ-compact space, `univ` is σ-compact. -/
/-
**isSigmaCompact_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSigmaCompact_univ [h : SigmaCompactSpace X] : IsSigmaCompact (univ : Set
 X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isSigmaCompact_univ_iff`：isSigmaCompact_univ_iff : IsSigmaCompact (univ 
: Set X) ↔ SigmaCompactSpace X

--- 原说明 ---
In a σ-compact space, `univ` is σ-compact.
-/
lemma isSigmaCompact_univ [h : SigmaCompactSpace X] : IsSigmaCompact (univ : Set X) :=
  isSigmaCompact_univ_iff.mpr h

/-- A topological space is σ-compact iff there exists a countable collection of compact
subspaces that cover the entire space. -/
/-
**SigmaCompactSpace_iff_exists_compact_covering** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SigmaCompactSpace_iff_exists_compact_covering : SigmaCompactSpace X ↔ exis
ts K : Nat -> Set X, (forall n, IsCompact (K n)) ∧ ⋃ n, K n = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isSigmaCompact_univ_iff`：isSigmaCompact_univ_iff : IsSigmaCompact (univ 
: Set X) ↔ SigmaCompactSpace X
· 使用定理 `IsSigmaCompact.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : S
et X),   IsSigmaCompact s = ∃ K, (∀ (n : ℕ), IsCompact (K n)) ∧ ⋃ n, K n = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A topological space is σ-compact iff there exists a countable collection of comp
act
subspaces that cover the entire space.
-/
lemma SigmaCompactSpace_iff_exists_compact_covering :
    SigmaCompactSpace X ↔ ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = univ := by
  rw [← isSigmaCompact_univ_iff, IsSigmaCompact]
/-
**SigmaCompactSpace.exists_compact_covering** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SigmaCompactSpace.exists_compact_covering [h : SigmaCompactSpace X] : exis
ts K : Nat -> Set X, (forall n, IsCompact (K n)) ∧ ⋃ n, K n = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SigmaCompactSpace_iff_exists_compact_covering`：SigmaCompactSpace_iff_exi
sts_compact_covering : SigmaCompactSpace X ↔ exists K : Nat -> Set X, (forall n,
 IsCompact (K n)) ∧ ⋃ n, K n = univ
-/
lemma SigmaCompactSpace.exists_compact_covering [h : SigmaCompactSpace X] :
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = univ :=
  SigmaCompactSpace_iff_exists_compact_covering.mp h

/-- If `X` is σ-compact, `im f` is σ-compact. -/
/-
**isSigmaCompact_range** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSigmaCompact_range {f : X -> Y} (hf : Continuous f) [SigmaCompactSpace X
] : IsSigmaCompact (range f)
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSigmaCompact.image`：IsSigmaCompact.image {f : X -> Y} (hf : Continuous
 f) {s : Set X} (hs : IsSigmaCompact s) : IsSigmaCompact (f '' s)
· 使用引理 `isSigmaCompact_univ`：isSigmaCompact_univ [h : SigmaCompactSpace X] : IsS
igmaCompact (univ : Set X)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f

--- 原说明 ---
If `X` is σ-compact, `im f` is σ-compact.
-/
lemma isSigmaCompact_range {f : X → Y} (hf : Continuous f) [SigmaCompactSpace X] :
    IsSigmaCompact (range f) :=
  image_univ ▸ isSigmaCompact_univ.image hf

/-- A subset `s` is σ-compact iff `s` (with the subspace topology) is a σ-compact space. -/
/-
**isSigmaCompact_iff_isSigmaCompact_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSigmaCompact_iff_isSigmaCompact_univ {s : Set X} : IsSigmaCompact s ↔ Is
SigmaCompact (univ : Set s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subtype.isSigmaCompact_iff`：Subtype.isSigmaCompact_iff {p : X -> Prop} {
s : Set { a // p a }} : IsSigmaCompact s ↔ IsSigmaCompact ((↑) '' s : Set X)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A subset `s` is σ-compact iff `s` (with the subspace topology) is a σ-compact sp
ace.
-/
lemma isSigmaCompact_iff_isSigmaCompact_univ {s : Set X} :
    IsSigmaCompact s ↔ IsSigmaCompact (univ : Set s) := by
  rw [Subtype.isSigmaCompact_iff, image_univ, Subtype.range_coe]
/-
**isSigmaCompact_iff_sigmaCompactSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSigmaCompact_iff_sigmaCompactSpace {s : Set X} : IsSigmaCompact s ↔ Sigm
aCompactSpace s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `isSigmaCompact_iff_isSigmaCompact_univ`：isSigmaCompact_iff_isSigmaCompac
t_univ {s : Set X} : IsSigmaCompact s ↔ IsSigmaCompact (univ : Set s)
· 使用引理 `isSigmaCompact_univ_iff`：isSigmaCompact_univ_iff : IsSigmaCompact (univ 
: Set X) ↔ SigmaCompactSpace X
-/
lemma isSigmaCompact_iff_sigmaCompactSpace {s : Set X} :
    IsSigmaCompact s ↔ SigmaCompactSpace s :=
  isSigmaCompact_iff_isSigmaCompact_univ.trans isSigmaCompact_univ_iff

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 200) CompactSpace.sigmaCompact [CompactSpace X] : SigmaCompactSpace X :=
  ⟨⟨fun _ => univ, fun _ => isCompact_univ, iUnion_const _⟩⟩
/-
**SigmaCompactSpace.of_countable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SigmaCompactSpace.of_countable (S : Set (Set X)) (Hc : S.Countable) (Hcomp
 : forall s in S, IsCompact s) (HU : ⋃₀ S = univ) : SigmaCompactSpace X
参数：S : Set (Set X)；Hc : S.Countable；Hcomp : forall s in S, IsCompact s；HU : ⋃₀ S
 = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.exists_seq_cover_iff_countable`：exists_seq_cover_iff_countable {p : 
Set α -> Prop} (h : exists s, p s) : (exists s : Nat -> Set α, (forall n, p (s n
)) ∧ ⋃ n, s n = univ) ↔ …
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
-/
theorem SigmaCompactSpace.of_countable (S : Set (Set X)) (Hc : S.Countable)
    (Hcomp : ∀ s ∈ S, IsCompact s) (HU : ⋃₀ S = univ) : SigmaCompactSpace X :=
  ⟨(exists_seq_cover_iff_countable ⟨_, isCompact_empty⟩).2 ⟨S, Hc, Hcomp, HU⟩⟩

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) sigmaCompactSpace_of_locallyCompact_secondCountable
    [LocallyCompactSpace X] [SecondCountableTopology X] : SigmaCompactSpace X := by
  choose K hKc hxK using fun x : X => exists_compact_mem_nhds x
  rcases countable_cover_nhds hxK with ⟨s, hsc, hsU⟩
  refine SigmaCompactSpace.of_countable _ (hsc.image K) (forall_mem_image.2 fun x _ => hKc x) ?_
  rwa [sUnion_image]

section

variable (X)
variable [SigmaCompactSpace X]

open SigmaCompactSpace

/-- A choice of compact covering for a `σ`-compact space, chosen to be monotone. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**compactCovering** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：compactCovering : Nat -> Set X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SigmaCompactSpace.exists_compact_covering`：SigmaCompactSpace.exists_comp
act_covering [h : SigmaCompactSpace X] : exists K : Nat -> Set X, (forall n, IsC
ompact (K n)) ∧ ⋃ n, K n = univ
-/
noncomputable def compactCovering : ℕ → Set X :=
  accumulate exists_compact_covering.choose
/-
**isCompact_compactCovering** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_compactCovering (n : Nat) : IsCompact (compactCovering X n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_accumulate`：isCompact_accumulate {K : Nat -> Set X} (hK : fora
ll n, IsCompact (K n)) (n : Nat) : IsCompact (accumulate K n)
· 使用引理 `SigmaCompactSpace.exists_compact_covering`：SigmaCompactSpace.exists_comp
act_covering [h : SigmaCompactSpace X] : exists K : Nat -> Set X, (forall n, IsC
ompact (K n)) ∧ ⋃ n, K n = univ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem isCompact_compactCovering (n : ℕ) : IsCompact (compactCovering X n) :=
  isCompact_accumulate (Classical.choose_spec SigmaCompactSpace.exists_compact_covering).1 n
/-
**iUnion_compactCovering** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_compactCovering : ⋃ n, compactCovering X n = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SigmaCompactSpace.exists_compact_covering`：SigmaCompactSpace.exists_comp
act_covering [h : SigmaCompactSpace X] : exists K : Nat -> Set X, (forall n, IsC
ompact (K n)) ∧ ⋃ n, K n = univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compactCovering.eq_1`：∀ (X : Type u_1) [inst : TopologicalSpace X] [inst
_1 : SigmaCompactSpace X], compactCovering X = Set.accumulate ⋯.choose
· 使用定理 `Set.iUnion_accumulate`：iUnion_accumulate [Preorder α] : ⋃ x, accumulate 
s x = ⋃ x, s x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem iUnion_compactCovering : ⋃ n, compactCovering X n = univ := by
  rw [compactCovering, iUnion_accumulate]
  exact (Classical.choose_spec SigmaCompactSpace.exists_compact_covering).2
/-
**iUnion_closure_compactCovering** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_closure_compactCovering : ⋃ n, closure (compactCovering X n) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_mono`：eq_top_mono (h : a <= b) (h₂ : a = ⊤) : b = ⊤
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `iUnion_compactCovering`：iUnion_compactCovering : ⋃ n, compactCovering X 
n = univ
-/
theorem iUnion_closure_compactCovering : ⋃ n, closure (compactCovering X n) = univ :=
  eq_top_mono (iUnion_mono fun _ ↦ subset_closure) (iUnion_compactCovering X)

@[mono, gcongr]
/-
**compactCovering_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compactCovering_subset ⦃m n : Nat⦄ (h : m <= n) : compactCovering X m subs
eteq compactCovering X n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.monotone_accumulate`：monotone_accumulate [Preorder α] : Monotone (ac
cumulate s)
· 使用引理 `SigmaCompactSpace.exists_compact_covering`：SigmaCompactSpace.exists_comp
act_covering [h : SigmaCompactSpace X] : exists K : Nat -> Set X, (forall n, IsC
ompact (K n)) ∧ ⋃ n, K n = univ
-/
theorem compactCovering_subset ⦃m n : ℕ⦄ (h : m ≤ n) : compactCovering X m ⊆ compactCovering X n :=
  monotone_accumulate h

variable {X}
/-
**exists_mem_compactCovering** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_mem_compactCovering (x : X) : exists n, x in compactCovering X n
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.iUnion_eq_univ_iff`：iUnion_eq_univ_iff {f : ι -> Set α} : ⋃ i, f i =
 univ ↔ forall x, exists i, x in f i
· 使用定理 `iUnion_compactCovering`：iUnion_compactCovering : ⋃ n, compactCovering X 
n = univ
-/
theorem exists_mem_compactCovering (x : X) : ∃ n, x ∈ compactCovering X n :=
  iUnion_eq_univ_iff.mp (iUnion_compactCovering X) x
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SigmaCompactSpace Y] : SigmaCompactSpace (X × Y) :=
  ⟨⟨fun n => compactCovering X n ×ˢ compactCovering Y n, fun _ =>
      (isCompact_compactCovering _ _).prod (isCompact_compactCovering _ _), by
      simp only [iUnion_prod_of_monotone (compactCovering_subset X) (compactCovering_subset Y),
        iUnion_compactCovering, univ_prod_univ]⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, SigmaCompactSpace (X i)] :
    SigmaCompactSpace (∀ i, X i) := by
  refine ⟨⟨fun n => Set.pi univ fun i => compactCovering (X i) n,
    fun n => isCompact_univ_pi fun i => isCompact_compactCovering (X i) _, ?_⟩⟩
  rw [iUnion_univ_pi_of_monotone]
  · simp only [iUnion_compactCovering, pi_univ]
  · exact fun i => compactCovering_subset (X i)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SigmaCompactSpace Y] : SigmaCompactSpace (X ⊕ Y) :=
  ⟨⟨fun n => Sum.inl '' compactCovering X n ∪ Sum.inr '' compactCovering Y n, fun n =>
      ((isCompact_compactCovering X n).image continuous_inl).union
        ((isCompact_compactCovering Y n).image continuous_inr),
      by simp only [iUnion_union_distrib, ← image_iUnion, iUnion_compactCovering, image_univ,
        range_inl_union_range_inr]⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, SigmaCompactSpace (X i)] : SigmaCompactSpace (Σ i, X i) := by
  cases isEmpty_or_nonempty ι
  · infer_instance
  · rcases exists_surjective_nat ι with ⟨f, hf⟩
    refine ⟨⟨fun n => ⋃ k ≤ n, Sigma.mk (f k) '' compactCovering (X (f k)) n, fun n => ?_, ?_⟩⟩
    · refine (finite_le_nat _).isCompact_biUnion fun k _ => ?_
      exact (isCompact_compactCovering _ _).image continuous_sigmaMk
    · simp only [iUnion_eq_univ_iff, Sigma.forall, mem_iUnion, hf.forall]
      intro k y
      rcases exists_mem_compactCovering y with ⟨n, hn⟩
      refine ⟨max k n, k, le_max_left _ _, mem_image_of_mem _ ?_⟩
      exact compactCovering_subset _ (le_max_right _ _) hn
/-
**Topology.IsClosedEmbedding.sigmaCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gy.IsClosedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [SigmaCompactSpace X]   {e : Y → X}, Topology.IsClosedEmbedding 
e → SigmaCompactSpace Y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.isCompact_preimage`：Topology.IsClosedEmbeddin
g.isCompact_preimage (hf : IsClosedEmbedding f) {K : Set Y} (hK : IsCompact K) :
 IsCompact (f ⁻¹' K)
· 使用定理 `isCompact_compactCovering`：isCompact_compactCovering (n : Nat) : IsCompa
ct (compactCovering X n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `iUnion_compactCovering`：iUnion_compactCovering : ⋃ n, compactCovering X 
n = univ
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
-/
protected lemma Topology.IsClosedEmbedding.sigmaCompactSpace {e : Y → X}
    (he : IsClosedEmbedding e) : SigmaCompactSpace Y :=
  ⟨⟨fun n => e ⁻¹' compactCovering X n, fun _ =>
      he.isCompact_preimage (isCompact_compactCovering _ _), by
      rw [← preimage_iUnion, iUnion_compactCovering, preimage_univ]⟩⟩
/-
**IsClosed.sigmaCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.sigmaCompactSpace {s : Set X} (hs : IsClosed s) : SigmaCompactSpa
ce s
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.sigmaCompactSpace`：∀ {X : Type u_1} {Y : Type
 u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [SigmaCompactSpa
ce X]   {e : Y → X}, Topology.IsCl…
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)
-/
theorem IsClosed.sigmaCompactSpace {s : Set X} (hs : IsClosed s) : SigmaCompactSpace s :=
  hs.isClosedEmbedding_subtypeVal.sigmaCompactSpace
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SigmaCompactSpace Y] : SigmaCompactSpace (ULift.{u} Y) :=
  IsClosedEmbedding.uliftDown.sigmaCompactSpace

/-- If `X` is a `σ`-compact space, then a locally finite family of nonempty sets of `X` can have
only countably many elements, `Set.Countable` version. -/
/-
**LocallyFinite.countable_univ** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：∀ {X : Type u_1} {ι : Type u_3} [inst : TopologicalSpace X] [SigmaCompactS
pace X] {f : ι → Set X},   LocallyFinite f → (∀ (i : ι), (f i).Nonempty) → Set.u
niv.Countable
参数：∀ (i : ι), (f i).Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.finite_nonempty_inter_compact`：finite_nonempty_inter_compa
ct {f : ι -> Set X} (hf : LocallyFinite f) (hs : IsCompact s) : { i | (f i inter
 s).Nonempty }.Finite
· 使用定理 `isCompact_compactCovering`：isCompact_compactCovering (n : Nat) : IsCompa
ct (compactCovering X n)
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.iUnion_eq_univ_iff`：iUnion_eq_univ_iff {f : ι -> Set α} : ⋃ i, f i =
 univ ↔ forall x, exists i, x in f i
· 使用定理 `iUnion_compactCovering`：iUnion_compactCovering : ⋃ n, compactCovering X 
n = univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Set.countable_iUnion`：countable_iUnion {t : ι -> Set α} [Countable ι] (h
t : forall i, (t i).Countable) : (⋃ i, t i).Countable
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable

--- 原说明 ---
If `X` is a `σ`-compact space, then a locally finite family of nonempty sets of 
`X` can have
only countably many elements, `Set.Countable` version.
-/
protected theorem LocallyFinite.countable_univ {f : ι → Set X} (hf : LocallyFinite f)
    (hne : ∀ i, (f i).Nonempty) : (univ : Set ι).Countable := by
  have := fun n => hf.finite_nonempty_inter_compact (isCompact_compactCovering X n)
  refine (countable_iUnion fun n => (this n).countable).mono fun i _ => ?_
  rcases hne i with ⟨x, hx⟩
  rcases iUnion_eq_univ_iff.1 (iUnion_compactCovering X) x with ⟨n, hn⟩
  exact mem_iUnion.2 ⟨n, x, hx, hn⟩

/-- If `f : ι → Set X` is a locally finite covering of a σ-compact topological space by nonempty
sets, then the index type `ι` is encodable. -/
@[instance_reducible]
/-
**LocallyFinite.encodable** 是 Mathlib 中的一个定义，位于命名空间 `LocallyFinite`。
形式化陈述：{X : Type u_1} →   [inst : TopologicalSpace X] →     [SigmaCompactSpace X]
 →       {ι : Type u_4} → {f : ι → Set X} → LocallyFinite f → (∀ (i : ι), (f i).
Nonempty) → Encodable ι
参数：∀ (i : ι), (f i).Nonempty。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.countable_univ`：∀ {X : Type u_1} {ι : Type u_3} [inst : To
pologicalSpace X] [SigmaCompactSpace X] {f : ι → Set X},   LocallyFinite f → (∀ 
(i : ι), (f i).Non…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `f : ι → Set X` is a locally finite covering of a σ-compact topological space
 by nonempty
sets, then the index type `ι` is encodable.
-/
protected noncomputable def LocallyFinite.encodable {ι : Type*} {f : ι → Set X}
    (hf : LocallyFinite f) (hne : ∀ i, (f i).Nonempty) : Encodable ι :=
  @Encodable.ofEquiv _ _ (hf.countable_univ hne).toEncodable (Equiv.Set.univ _).symm

/-- In a topological space with sigma compact topology, if `f` is a function that sends each point
`x` of a closed set `s` to a neighborhood of `x` within `s`, then for some countable set `t ⊆ s`,
the neighborhoods `f x`, `x ∈ t`, cover the whole set `s`. -/
/-
**countable_cover_nhdsWithin_of_sigmaCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：countable_cover_nhdsWithin_of_sigmaCompact {f : X -> Set X} {s : Set X} (h
s : IsClosed s) (hf : forall x in s, f x in 𝓝[s] x) : exists t subseteq s, t.Cou
ntable ∧ s subseteq ⋃ x in t, f x
参数：hs : IsClosed s；hf : forall x in s, f x in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.countable_iUnion`：countable_iUnion {t : ι -> Set α} [Countable ι] (h
t : forall i, (t i).Countable) : (⋃ i, t i).Countable
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `exists_mem_compactCovering`：exists_mem_compactCovering (x : X) : exists 
n, x in compactCovering X n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `IsCompact.elim_nhds_subcover`：IsCompact.elim_nhds_subcover (hs : IsCompa
ct s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (
forall x in t, x i…
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `isCompact_compactCovering`：isCompact_compactCovering (n : Nat) : IsCompa
ct (compactCovering X n)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
In a topological space with sigma compact topology, if `f` is a function that se
nds each point
`x` of a closed set `s` to a neighborhood of `x` within `s`, then for some count
able set `t ⊆ s`,
the neighborhoods `f x`, `x ∈ t`, cover the whole set `s`.
-/
theorem countable_cover_nhdsWithin_of_sigmaCompact {f : X → Set X} {s : Set X} (hs : IsClosed s)
    (hf : ∀ x ∈ s, f x ∈ 𝓝[s] x) : ∃ t ⊆ s, t.Countable ∧ s ⊆ ⋃ x ∈ t, f x := by
  simp only [nhdsWithin, mem_inf_principal] at hf
  choose t ht hsub using fun n =>
    ((isCompact_compactCovering X n).inter_right hs).elim_nhds_subcover _ fun x hx => hf x hx.right
  refine
    ⟨⋃ n, (t n : Set X), iUnion_subset fun n x hx => (ht n x hx).2,
      countable_iUnion fun n => (t n).countable_toSet, fun x hx => mem_iUnion₂.2 ?_⟩
  rcases exists_mem_compactCovering x with ⟨n, hn⟩
  rcases mem_iUnion₂.1 (hsub n ⟨hn, hx⟩) with ⟨y, hyt : y ∈ t n, hyf : x ∈ s → x ∈ f y⟩
  exact ⟨y, mem_iUnion.2 ⟨n, hyt⟩, hyf hx⟩

/-- In a topological space with sigma compact topology, if `f` is a function that sends each
point `x` to a neighborhood of `x`, then for some countable set `s`, the neighborhoods `f x`,
`x ∈ s`, cover the whole space. -/
/-
**countable_cover_nhds_of_sigmaCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：countable_cover_nhds_of_sigmaCompact {f : X -> Set X} (hf : forall x, f x 
in 𝓝 x) : exists s : Set X, s.Countable ∧ ⋃ x in s, f x = univ
参数：hf : forall x, f x in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `countable_cover_nhdsWithin_of_sigmaCompact`：countable_cover_nhdsWithin_o
f_sigmaCompact {f : X -> Set X} {s : Set X} (hs : IsClosed s) (hf : forall x in 
s, f x in 𝓝[s] x) : exists t sub…
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ

--- 原说明 ---
In a topological space with sigma compact topology, if `f` is a function that se
nds each
point `x` to a neighborhood of `x`, then for some countable set `s`, the neighbo
rhoods `f x`,
`x ∈ s`, cover the whole space.
-/
theorem countable_cover_nhds_of_sigmaCompact {f : X → Set X} (hf : ∀ x, f x ∈ 𝓝 x) :
    ∃ s : Set X, s.Countable ∧ ⋃ x ∈ s, f x = univ := by
  simp only [← nhdsWithin_univ] at hf
  rcases countable_cover_nhdsWithin_of_sigmaCompact isClosed_univ fun x _ => hf x with
    ⟨s, -, hsc, hsU⟩
  exact ⟨s, hsc, univ_subset_iff.1 hsU⟩
end

/-- An [exhaustion by compact sets](https://en.wikipedia.org/wiki/Exhaustion_by_compact_sets) of a
topological space is a sequence of compact sets `K n` such that `K n ⊆ interior (K (n + 1))` and
`⋃ n, K n = univ`.

If `X` is a locally compact sigma compact space, then `CompactExhaustion.choice X` provides
a choice of an exhaustion by compact sets. This choice is also available as
`(default : CompactExhaustion X)`. -/
/-
**CompactExhaustion** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_4) → [TopologicalSpace X] → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An [exhaustion by compact sets](https://en.wikipedia.org/wiki/Exhaustion_by_comp
act_sets) of a
topological space is a sequence of compact sets `K n` such that `K n ⊆ interior 
(K (n + 1))` and
`⋃ n, K n = univ`.

If `X` is a locally compact sigma compact space, then `CompactExhaustion.choice 
X` provides
a choice of an exhaustion by compact sets. This choice is also available as
`(default : CompactExhaustion X)`.
-/
structure CompactExhaustion (X : Type*) [TopologicalSpace X] where
  /-- The sequence of compact sets that form a compact exhaustion. -/
  toFun : ℕ → Set X
  /-- The sets in the compact exhaustion are in fact compact. -/
  isCompact' : ∀ n, IsCompact (toFun n)
  /-- The sets in the compact exhaustion form a sequence:
  each set is contained in the interior of the next. -/
  subset_interior_succ' : ∀ n, toFun n ⊆ interior (toFun (n + 1))
  /-- The union of all sets in a compact exhaustion equals the entire space. -/
  iUnion_eq' : ⋃ n, toFun n = univ

namespace CompactExhaustion

/-
**CompactExhaustion.** 是 Mathlib 中的一个实例，位于命名空间 `CompactExhaustion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (CompactExhaustion X) ℕ (Set X) where
  coe := toFun
  coe_injective | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl
/-
**CompactExhaustion.** 是 Mathlib 中的一个实例，位于命名空间 `CompactExhaustion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderHomClass (CompactExhaustion X) ℕ (Set X) where
  map_rel f _ _ h := monotone_nat_of_le_succ
    (fun n ↦ (f.subset_interior_succ' n).trans interior_subset) h

variable (K : CompactExhaustion X)

@[simp]
/-
**CompactExhaustion.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `CompactExhaustion`。
形式化陈述：toFun_eq_coe : K.toFun = K
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe : K.toFun = K := rfl
/-
**CompactExhaustion.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `CompactExhaustion`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] (K : CompactExhaustion X) (n 
: ℕ), IsCompact (K n)
参数：K : CompactExhaustion X；n : ℕ；K n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactExhaustion.isCompact'`：∀ {X : Type u_4} [inst : TopologicalSpace 
X] (self : CompactExhaustion X) (n : ℕ), IsCompact (self.toFun n)
-/
protected theorem isCompact (n : ℕ) : IsCompact (K n) :=
  K.isCompact' n
/-
**CompactExhaustion.subset_interior_succ** 是 Mathlib 中的一个定理，位于命名空间 `CompactExhau
stion`。
形式化陈述：subset_interior_succ (n : Nat) : K n subseteq interior (K (n + 1))
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactExhaustion.subset_interior_succ'`：∀ {X : Type u_4} [inst : Topolo
gicalSpace X] (self : CompactExhaustion X) (n : ℕ),   self.toFun n ⊆ interior (s
elf.toFun (n + 1))
-/
theorem subset_interior_succ (n : ℕ) : K n ⊆ interior (K (n + 1)) :=
  K.subset_interior_succ' n

@[gcongr, mono]
/-
**CompactExhaustion.subset** 是 Mathlib 中的一个定理，位于命名空间 `CompactExhaustion`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] (K : CompactExhaustion X) ⦃m 
n : ℕ⦄, m ≤ n → K m ⊆ K n
参数：K : CompactExhaustion X。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `CompactExhaustion.instOrderHomClassNatSet`：∀ {X : Type u_1} [inst : Topo
logicalSpace X], OrderHomClass (CompactExhaustion X) ℕ (Set X)
-/
protected theorem subset ⦃m n : ℕ⦄ (h : m ≤ n) : K m ⊆ K n :=
  OrderHomClass.mono K h
/-
**CompactExhaustion.subset_succ** 是 Mathlib 中的一个定理，位于命名空间 `CompactExhaustion`。
形式化陈述：subset_succ (n : Nat) : K n subseteq K (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactExhaustion.subset`：∀ {X : Type u_1} [inst : TopologicalSpace X] (
K : CompactExhaustion X) ⦃m n : ℕ⦄, m ≤ n → K m ⊆ K n
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem subset_succ (n : ℕ) : K n ⊆ K (n + 1) := K.subset n.le_succ
/-
**CompactExhaustion.subset_interior** 是 Mathlib 中的一个定理，位于命名空间 `CompactExhaustion
`。
形式化陈述：subset_interior ⦃m n : Nat⦄ (h : m < n) : K m subseteq interior (K n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `CompactExhaustion.subset_interior_succ`：subset_interior_succ (n : Nat) :
 K n subseteq interior (K (n + 1))
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `CompactExhaustion.subset`：∀ {X : Type u_1} [inst : TopologicalSpace X] (
K : CompactExhaustion X) ⦃m n : ℕ⦄, m ≤ n → K m ⊆ K n
-/
theorem subset_interior ⦃m n : ℕ⦄ (h : m < n) : K m ⊆ interior (K n) :=
  Subset.trans (K.subset_interior_succ m) <| interior_mono <| K.subset h
/-
**CompactExhaustion.iUnion_eq** 是 Mathlib 中的一个定理，位于命名空间 `CompactExhaustion`。
形式化陈述：iUnion_eq : ⋃ n, K n = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactExhaustion.iUnion_eq'`：∀ {X : Type u_4} [inst : TopologicalSpace 
X] (self : CompactExhaustion X), ⋃ n, self.toFun n = Set.univ
-/
theorem iUnion_eq : ⋃ n, K n = univ :=
  K.iUnion_eq'
/-
**CompactExhaustion.exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `CompactExhaustion`。
形式化陈述：exists_mem (x : X) : exists n, x in K n
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.iUnion_eq_univ_iff`：iUnion_eq_univ_iff {f : ι -> Set α} : ⋃ i, f i =
 univ ↔ forall x, exists i, x in f i
· 使用定理 `CompactExhaustion.iUnion_eq`：iUnion_eq : ⋃ n, K n = univ
-/
theorem exists_mem (x : X) : ∃ n, x ∈ K n :=
  iUnion_eq_univ_iff.1 K.iUnion_eq x
/-
**CompactExhaustion.exists_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `CompactExhaustion
`。
形式化陈述：exists_mem_nhds (x : X) : exists n, K n in 𝓝 x
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactExhaustion.exists_mem`：exists_mem (x : X) : exists n, x in K n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `CompactExhaustion.subset_interior_succ`：subset_interior_succ (n : Nat) :
 K n subseteq interior (K (n + 1))
-/
theorem exists_mem_nhds (x : X) : ∃ n, K n ∈ 𝓝 x := by
  rcases K.exists_mem x with ⟨n, hn⟩
  exact ⟨n + 1, mem_interior_iff_mem_nhds.mp <| K.subset_interior_succ n hn⟩

/-- A compact exhaustion eventually covers any compact set. -/
/-
**CompactExhaustion.exists_superset_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 `Comp
actExhaustion`。
形式化陈述：exists_superset_of_isCompact {s : Set X} (hs : IsCompact s) : exists n, s 
subseteq K n
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_directed_cover`：IsCompact.elim_directed_cover {ι : Type v
} [hι : Nonempty ι] (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen 
(U i)) (hsU : s sub…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `CompactExhaustion.exists_mem`：exists_mem (x : X) : exists n, x in K n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `CompactExhaustion.subset_interior_succ`：subset_interior_succ (n : Nat) :
 K n subseteq interior (K (n + 1))
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `CompactExhaustion.subset`：∀ {X : Type u_1} [inst : TopologicalSpace X] (
K : CompactExhaustion X) ⦃m n : ℕ⦄, m ≤ n → K m ⊆ K n
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s

--- 原说明 ---
A compact exhaustion eventually covers any compact set.
-/
theorem exists_superset_of_isCompact {s : Set X} (hs : IsCompact s) : ∃ n, s ⊆ K n := by
  suffices ∃ n, s ⊆ interior (K n) from this.imp fun _ ↦ (Subset.trans · interior_subset)
  refine hs.elim_directed_cover (interior ∘ K) (fun _ ↦ isOpen_interior) ?_ ?_
  · intro x _
    rcases K.exists_mem x with ⟨k, hk⟩
    exact mem_iUnion.2 ⟨k + 1, K.subset_interior_succ _ hk⟩
  · exact Monotone.directed_le fun _ _ h ↦ interior_mono <| K.subset h

open scoped Classical in
/-- The minimal `n` such that `x ∈ K n`. -/
/-
**CompactExhaustion.find** 是 Mathlib 中的一个定义，位于命名空间 `CompactExhaustion`。
形式化陈述：{X : Type u_1} → [inst : TopologicalSpace X] → CompactExhaustion X → X → ℕ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompactExhaustion.exists_mem`：exists_mem (x : X) : exists n, x in K n

--- 原说明 ---
The minimal `n` such that `x ∈ K n`.
-/
protected noncomputable def find (x : X) : ℕ :=
  Nat.find (K.exists_mem x)
/-
**CompactExhaustion.mem_find** 是 Mathlib 中的一个定理，位于命名空间 `CompactExhaustion`。
形式化陈述：mem_find (x : X) : x in K (K.find x)
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `CompactExhaustion.exists_mem`：exists_mem (x : X) : exists n, x in K n
-/
theorem mem_find (x : X) : x ∈ K (K.find x) := by
  classical
  exact Nat.find_spec (K.exists_mem x)
/-
**CompactExhaustion.mem_iff_find_le** 是 Mathlib 中的一个定理，位于命名空间 `CompactExhaustion
`。
形式化陈述：mem_iff_find_le {x : X} {n : Nat} : x in K n ↔ K.find x <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
· 使用定理 `CompactExhaustion.exists_mem`：exists_mem (x : X) : exists n, x in K n
· 使用定理 `CompactExhaustion.subset`：∀ {X : Type u_1} [inst : TopologicalSpace X] (
K : CompactExhaustion X) ⦃m n : ℕ⦄, m ≤ n → K m ⊆ K n
· 使用定理 `CompactExhaustion.mem_find`：mem_find (x : X) : x in K (K.find x)
-/
theorem mem_iff_find_le {x : X} {n : ℕ} : x ∈ K n ↔ K.find x ≤ n := by
  classical
  exact ⟨fun h => Nat.find_min' (K.exists_mem x) h, fun h => K.subset h <| K.mem_find x⟩

/-- Prepend the empty set to a compact exhaustion `K n`. -/
/-
**CompactExhaustion.shiftr** 是 Mathlib 中的一个定义，位于命名空间 `CompactExhaustion`。
形式化陈述：shiftr : CompactExhaustion X where toFun n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prepend the empty set to a compact exhaustion `K n`.
-/
def shiftr : CompactExhaustion X where
  toFun n := Nat.casesOn n ∅ K
  isCompact' n := Nat.casesOn n isCompact_empty K.isCompact
  subset_interior_succ' n := Nat.casesOn n (empty_subset _) K.subset_interior_succ
  iUnion_eq' := iUnion_eq_univ_iff.2 fun x => ⟨K.find x + 1, K.mem_find x⟩

@[simp]
/-
**CompactExhaustion.find_shiftr** 是 Mathlib 中的一个定理，位于命名空间 `CompactExhaustion`。
形式化陈述：find_shiftr (x : X) : K.shiftr.find x = K.find x + 1
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.find_comp_succ`：find_comp_succ (h₁ : exists n, p n) (h₂ : exists n, 
p (n + 1)) (h0 : ¬p 0) : Nat.find h₁ = Nat.find h₂ + 1
· 使用定理 `CompactExhaustion.exists_mem`：exists_mem (x : X) : exists n, x in K n
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
theorem find_shiftr (x : X) : K.shiftr.find x = K.find x + 1 := by
  classical
  exact Nat.find_comp_succ _ _ (notMem_empty _)
/-
**CompactExhaustion.mem_sdiff_shiftr_find** 是 Mathlib 中的一个定理，位于命名空间 `CompactExha
ustion`。
形式化陈述：mem_sdiff_shiftr_find (x : X) : x in K.shiftr (K.find x + 1) \ K.shiftr (K
.find x)
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactExhaustion.mem_find`：mem_find (x : X) : x in K (K.find x)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CompactExhaustion.mem_iff_find_le`：mem_iff_find_le {x : X} {n : Nat} : x
 in K n ↔ K.find x <= n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CompactExhaustion.find_shiftr`：find_shiftr (x : X) : K.shiftr.find x = K
.find x + 1
-/
theorem mem_sdiff_shiftr_find (x : X) : x ∈ K.shiftr (K.find x + 1) \ K.shiftr (K.find x) :=
  ⟨K.mem_find _,
    mt K.shiftr.mem_iff_find_le.1 <| by simp only [find_shiftr, not_le, Nat.lt_succ_self]⟩

@[deprecated (since := "2026-06-03")] alias mem_diff_shiftr_find := mem_sdiff_shiftr_find

/-- A choice of an
[exhaustion by compact sets](https://en.wikipedia.org/wiki/Exhaustion_by_compact_sets)
of a weakly locally compact σ-compact space. -/
/-
**CompactExhaustion.choice** 是 Mathlib 中的一个定义，位于命名空间 `CompactExhaustion`。
形式化陈述：choice (X : Type*) [TopologicalSpace X] [WeaklyLocallyCompactSpace X] [Sig
maCompactSpace X] : CompactExhaustion X
参数：X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of an
[exhaustion by compact sets](https://en.wikipedia.org/wiki/Exhaustion_by_compact
_sets)
of a weakly locally compact σ-compact space.
-/
noncomputable def choice (X : Type*) [TopologicalSpace X] [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] : CompactExhaustion X := by
  apply Classical.choice
  let K : ℕ → { s : Set X // IsCompact s } := fun n =>
    Nat.recOn n ⟨∅, isCompact_empty⟩ fun n s =>
      ⟨(exists_compact_superset s.2).choose ∪ compactCovering X n,
        (exists_compact_superset s.2).choose_spec.1.union (isCompact_compactCovering _ _)⟩
  refine ⟨⟨fun n ↦ (K n).1, fun n => (K n).2, fun n ↦ ?_, ?_⟩⟩
  · exact Subset.trans (exists_compact_superset (K n).2).choose_spec.2
      (interior_mono subset_union_left)
  · refine univ_subset_iff.1 (iUnion_compactCovering X ▸ ?_)
    exact iUnion_mono' fun n => ⟨n + 1, subset_union_right⟩
/-
**CompactExhaustion.** 是 Mathlib 中的一个实例，位于命名空间 `CompactExhaustion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [SigmaCompactSpace X] [WeaklyLocallyCompactSpace X] :
    Inhabited (CompactExhaustion X) :=
  ⟨CompactExhaustion.choice X⟩

end CompactExhaustion

