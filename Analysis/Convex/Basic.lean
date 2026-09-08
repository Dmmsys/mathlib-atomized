/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.Analysis.Convex.Star
public import Mathlib.Tactic.Field
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.Tactic.NoncommRing

/-!
# Convex sets

In a 𝕜-vector space, we define the following property:
* `Convex 𝕜 s`: A set `s` is convex if for any two points `x y ∈ s` it includes `segment 𝕜 x y`.

We provide various equivalent versions, and prove that some specific sets are convex.

## TODO

Generalize all this file to affine spaces.
-/

@[expose] public section


variable {𝕜 E F β : Type*}

open LinearMap Set

open scoped Convex Pointwise

/-! ### Convexity of sets -/


section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section SMul

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 F] (s : Set E) {x : E}

/-- Convexity of sets. -/
/-
**Convex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Convex : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convexity of sets.
-/
def Convex : Prop :=
  ∀ ⦃x : E⦄, x ∈ s → StarConvex 𝕜 x s

variable {𝕜 s}
/-
**Convex.starConvex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.starConvex (hs : Convex 𝕜 s) (hx : x in s) : StarConvex 𝕜 x s
参数：hs : Convex 𝕜 s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Convex.starConvex (hs : Convex 𝕜 s) (hx : x ∈ s) : StarConvex 𝕜 x s :=
  hs hx
/-
**convex_iff_segment_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_iff_segment_subset : Convex 𝕜 s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄,
 y in s -> [x -[𝕜] y] subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `starConvex_iff_segment_subset`：starConvex_iff_segment_subset : StarConve
x 𝕜 x s ↔ forall ⦃y⦄, y in s -> [x -[𝕜] y] subseteq s
-/
theorem convex_iff_segment_subset : Convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → [x -[𝕜] y] ⊆ s :=
  forall₂_congr fun _ _ => starConvex_iff_segment_subset
/-
**Convex.segment_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in 
s) : [x -[𝕜] y] subseteq s
参数：h : Convex 𝕜 s；hx : x in s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `convex_iff_segment_subset`：convex_iff_segment_subset : Convex 𝕜 s ↔ fora
ll ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> [x -[𝕜] y] subseteq s
-/
theorem Convex.segment_subset (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    [x -[𝕜] y] ⊆ s :=
  convex_iff_segment_subset.1 h hx hy
/-
**Convex.openSegment_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.openSegment_subset (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y
 in s) : openSegment 𝕜 x y subseteq s
参数：h : Convex 𝕜 s；hx : x in s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `openSegment_subset_segment`：openSegment_subset_segment (x y : E) : openS
egment 𝕜 x y subseteq [x -[𝕜] y]
· 使用定理 `Convex.segment_subset`：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : [x -[𝕜] y] subseteq s
-/
theorem Convex.openSegment_subset (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    openSegment 𝕜 x y ⊆ s :=
  (openSegment_subset_segment 𝕜 x y).trans (h.segment_subset hx hy)
/-
**convex_iff_add_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_iff_add_mem : Convex 𝕜 s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s
 -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 -> a • x + b • y in s
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
theorem convex_iff_add_mem : Convex 𝕜 s ↔
    ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s := by
  simp_rw [convex_iff_segment_subset, segment_subset_iff]

/-- Alternative definition of set convexity, in terms of pointwise set operations. -/
/-
**convex_iff_pointwise_add_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_iff_pointwise_add_subset : Convex 𝕜 s ↔ forall ⦃a b : 𝕜⦄, 0 <= a ->
 0 <= b -> a + b = 1 -> a • s + b • s subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.add_mem_add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α} {a b : α}
, a ∈ s → b ∈ t → a + b ∈ s + t

--- 原说明 ---
Alternative definition of set convexity, in terms of pointwise set operations.
-/
theorem convex_iff_pointwise_add_subset :
    Convex 𝕜 s ↔ ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • s + b • s ⊆ s :=
  Iff.intro
    (by
      rintro hA a b ha hb hab w ⟨au, ⟨u, hu, rfl⟩, bv, ⟨v, hv, rfl⟩, rfl⟩
      exact hA hu hv ha hb hab)
    fun h _ hx _ hy _ _ ha hb hab => (h ha hb hab) (Set.add_mem_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩)

alias ⟨Convex.set_combo_subset, _⟩ := convex_iff_pointwise_add_subset
/-
**convex_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_empty : Convex 𝕜 (∅ : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem convex_empty : Convex 𝕜 (∅ : Set E) := fun _ => False.elim
/-
**convex_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_univ : Convex 𝕜 (Set.univ : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `starConvex_univ`：starConvex_univ (x : E) : StarConvex 𝕜 x univ
-/
theorem convex_univ : Convex 𝕜 (Set.univ : Set E) := fun _ _ => starConvex_univ _
/-
**Convex.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s
 inter t)
参数：hs : Convex 𝕜 s；ht : Convex 𝕜 t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarConvex.inter`：StarConvex.inter (hs : StarConvex 𝕜 x s) (ht : StarCon
vex 𝕜 x t) : StarConvex 𝕜 x (s inter t)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s ∩ t) :=
  fun _ hx => (hs hx.1).inter (ht hx.2)
/-
**convex_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_sInter {S : Set (Set E)} (h : forall s in S, Convex 𝕜 s) : Convex 𝕜
 (⋂₀ S)
参数：Set E；h : forall s in S, Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `starConvex_sInter`：starConvex_sInter {S : Set (Set E)} (h : forall s in 
S, StarConvex 𝕜 x s) : StarConvex 𝕜 x (⋂₀ S)
-/
theorem convex_sInter {S : Set (Set E)} (h : ∀ s ∈ S, Convex 𝕜 s) : Convex 𝕜 (⋂₀ S) := fun _ hx =>
  starConvex_sInter fun _ hs => h _ hs <| hx _ hs
/-
**convex_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_iInter {ι : Sort*} {s : ι -> Set E} (h : forall i, Convex 𝕜 (s i)) 
: Convex 𝕜 (⋂ i, s i)
参数：h : forall i, Convex 𝕜 (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_sInter`：convex_sInter {S : Set (Set E)} (h : forall s in S, Conve
x 𝕜 s) : Convex 𝕜 (⋂₀ S)
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem convex_iInter {ι : Sort*} {s : ι → Set E} (h : ∀ i, Convex 𝕜 (s i)) :
    Convex 𝕜 (⋂ i, s i) :=
  sInter_range s ▸ convex_sInter <| forall_mem_range.2 h
/-
**convex_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_iInter {ι : Sort*} {s : ι -> Set E} (h : forall i, Convex 𝕜 (s i)) 
: Convex 𝕜 (⋂ i, s i)
参数：h : forall i, Convex 𝕜 (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_sInter`：convex_sInter {S : Set (Set E)} (h : forall s in S, Conve
x 𝕜 s) : Convex 𝕜 (⋂₀ S)
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem convex_iInter₂ {ι : Sort*} {κ : ι → Sort*} {s : (i : ι) → κ i → Set E}
    (h : ∀ i j, Convex 𝕜 (s i j)) : Convex 𝕜 (⋂ (i) (j), s i j) :=
  convex_iInter fun i => convex_iInter <| h i
/-
**Convex.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.prod {s : Set E} {t : Set F} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : 
Convex 𝕜 (s ×ˢ t)
参数：hs : Convex 𝕜 s；ht : Convex 𝕜 t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarConvex.prod`：StarConvex.prod {y : F} {s : Set E} {t : Set F} (hs : S
tarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t) : StarConvex 𝕜 (x, y) (s ×ˢ t)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Convex.prod {s : Set E} {t : Set F} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
    Convex 𝕜 (s ×ˢ t) := fun _ hx => (hs hx.1).prod (ht hx.2)
/-
**convex_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_pi {ι : Type*} {E : ι -> Type*} [forall i, AddCommMonoid (E i)] [fo
rall i, SMul 𝕜 (E i)] {s : Set ι} {t : forall i, Set (E i)} (ht : forall ⦃i⦄, i 
in s -> Convex 𝕜 (t i)) : Convex 𝕜 (s.pi t)
参数：E i；E i；E i；ht : forall ⦃i⦄, i in s -> Convex 𝕜 (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `starConvex_pi`：starConvex_pi {ι : Type*} {E : ι -> Type*} [forall i, Add
CommMonoid (E i)] [forall i, SMul 𝕜 (E i)] {x : forall i, E i} {s : Set ι} {t : 
for…
-/
theorem convex_pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommMonoid (E i)] [∀ i, SMul 𝕜 (E i)]
    {s : Set ι} {t : ∀ i, Set (E i)} (ht : ∀ ⦃i⦄, i ∈ s → Convex 𝕜 (t i)) : Convex 𝕜 (s.pi t) :=
  fun _ hx => starConvex_pi fun _ hi => ht hi <| hx _ hi
/-
**Directed.convex_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Directed.convex_iUnion {ι : Sort*} {s : ι -> Set E} (hdir : Directed (· su
bseteq ·) s) (hc : forall ⦃i : ι⦄, Convex 𝕜 (s i)) : Convex 𝕜 (⋃ i, s i)
参数：hdir : Directed (· subseteq ·) s；hc : forall ⦃i : ι⦄, Convex 𝕜 (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem Directed.convex_iUnion {ι : Sort*} {s : ι → Set E} (hdir : Directed (· ⊆ ·) s)
    (hc : ∀ ⦃i : ι⦄, Convex 𝕜 (s i)) : Convex 𝕜 (⋃ i, s i) := by
  rintro x hx y hy a b ha hb hab
  rw [mem_iUnion] at hx hy ⊢
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact ⟨k, hc (hik hx) (hjk hy) ha hb hab⟩
/-
**DirectedOn.convex_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectedOn.convex_sUnion {c : Set (Set E)} (hdir : DirectedOn (· subseteq 
·) c) (hc : forall ⦃A : Set E⦄, A in c -> Convex 𝕜 A) : Convex 𝕜 (⋃₀ c)
参数：Set E；hdir : DirectedOn (· subseteq ·) c；hc : forall ⦃A : Set E⦄, A in c -> C
onvex 𝕜 A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `Directed.convex_iUnion`：Directed.convex_iUnion {ι : Sort*} {s : ι -> Set
 E} (hdir : Directed (· subseteq ·) s) (hc : forall ⦃i : ι⦄, Convex 𝕜 (s i)) : C
onvex 𝕜 (⋃ i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `directedOn_iff_directed`：directedOn_iff_directed {s} : @DirectedOn α r s
 ↔ Directed r (Subtype.val : s -> α)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem DirectedOn.convex_sUnion {c : Set (Set E)} (hdir : DirectedOn (· ⊆ ·) c)
    (hc : ∀ ⦃A : Set E⦄, A ∈ c → Convex 𝕜 A) : Convex 𝕜 (⋃₀ c) := by
  rw [sUnion_eq_iUnion]
  exact (directedOn_iff_directed.1 hdir).convex_iUnion fun A => hc A.2
/-
**Convex.setOfPred_const_imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.setOfPred_const_imp {P : Prop} (hs : Convex 𝕜 s) : Convex 𝕜 {x | P 
-> x in s}
参数：hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem Convex.setOfPred_const_imp {P : Prop} (hs : Convex 𝕜 s) : Convex 𝕜 {x | P → x ∈ s} := by
  by_cases hP : P <;> simp [hP, hs, convex_univ]

@[deprecated (since := "2026-07-09")] alias Convex.setOf_const_imp := Convex.setOfPred_const_imp

end SMul

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {s : Set E} {x : E}

/-
**convex_iff_openSegment_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_iff_openSegment_subset [ZeroLEOneClass 𝕜] : Convex 𝕜 s ↔ forall ⦃x⦄
, x in s -> forall ⦃y⦄, y in s -> openSegment 𝕜 x y subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `starConvex_iff_openSegment_subset`：starConvex_iff_openSegment_subset [Ze
roLEOneClass 𝕜] (hx : x in s) : StarConvex 𝕜 x s ↔ forall ⦃y⦄, y in s -> openSeg
ment 𝕜 x y subseteq s
-/
theorem convex_iff_openSegment_subset [ZeroLEOneClass 𝕜] :
    Convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → openSegment 𝕜 x y ⊆ s :=
  forall₂_congr fun _ => starConvex_iff_openSegment_subset
/-
**convex_iff_forall_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_iff_forall_pos : Convex 𝕜 s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄, y i
n s -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `starConvex_iff_forall_pos`：starConvex_iff_forall_pos (hx : x in s) : Sta
rConvex 𝕜 x s ↔ forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b 
= 1 -> a • x + …
-/
theorem convex_iff_forall_pos :
    Convex 𝕜 s ↔
      ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s :=
  forall₂_congr fun _ => starConvex_iff_forall_pos
/-
**convex_iff_pairwise_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_iff_pairwise_pos : Convex 𝕜 s ↔ s.Pairwise fun x y => forall ⦃a b :
 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `convex_iff_forall_pos`：convex_iff_forall_pos : Convex 𝕜 s ↔ forall ⦃x⦄, 
x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 ->
 a • x + b …
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
-/
theorem convex_iff_pairwise_pos : Convex 𝕜 s ↔
    s.Pairwise fun x y => ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s := by
  refine convex_iff_forall_pos.trans ⟨fun h x hx y hy _ => h hx hy, ?_⟩
  intro h x hx y hy a b ha hb hab
  obtain rfl | hxy := eq_or_ne x y
  · rwa [Convex.combo_self hab]
  · exact h hx hy hxy ha hb hab
/-
**Convex.starConvex_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.starConvex_iff [ZeroLEOneClass 𝕜] (hs : Convex 𝕜 s) (h : s.Nonempty
) : StarConvex 𝕜 x s ↔ x in s
参数：hs : Convex 𝕜 s；h : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarConvex.mem`：StarConvex.mem [ZeroLEOneClass 𝕜] (hs : StarConvex 𝕜 x s
) (h : s.Nonempty) : x in s
· 使用定理 `Convex.starConvex`：Convex.starConvex (hs : Convex 𝕜 s) (hx : x in s) : S
tarConvex 𝕜 x s
-/
theorem Convex.starConvex_iff [ZeroLEOneClass 𝕜] (hs : Convex 𝕜 s) (h : s.Nonempty) :
    StarConvex 𝕜 x s ↔ x ∈ s :=
  ⟨fun hxs => hxs.mem h, hs.starConvex⟩
/-
**Set.Subsingleton.convex** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E] {s : Set E}, s.Sub
singleton → Convex 𝕜 s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `convex_iff_pairwise_pos`：convex_iff_pairwise_pos : Convex 𝕜 s ↔ s.Pairwi
se fun x y => forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in 
s
· 使用定理 `Set.Subsingleton.pairwise`：∀ {α : Type u_1} {s : Set α}, s.Subsingleton 
→ ∀ (r : α → α → Prop), s.Pairwise r
-/
protected theorem Set.Subsingleton.convex {s : Set E} (h : s.Subsingleton) : Convex 𝕜 s :=
  convex_iff_pairwise_pos.mpr (h.pairwise _)
/-
**convex_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E] (c : E), Convex 𝕜 
{c}
参数：c : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.convex`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semirin
g 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Mod
ule 𝕜 E] {s :…
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
@[simp] theorem convex_singleton (c : E) : Convex 𝕜 ({c} : Set E) :=
  subsingleton_singleton.convex
/-
**convex_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_zero : Convex 𝕜 (0 : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_singleton`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (c :…
-/
theorem convex_zero : Convex 𝕜 (0 : Set E) :=
  convex_singleton _
/-
**convex_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_segment [IsOrderedRing 𝕜] (x y : E) : Convex 𝕜 [x -[𝕜] y]
参数：x y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convex_segment [IsOrderedRing 𝕜] (x y : E) : Convex 𝕜 [x -[𝕜] y] := by
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ a b ha hb hab
  refine
    ⟨a * ap + b * aq, a * bp + b * bq, add_nonneg (mul_nonneg ha hap) (mul_nonneg hb haq),
      add_nonneg (mul_nonneg ha hbp) (mul_nonneg hb hbq), ?_, ?_⟩
  · rw [add_add_add_comm, ← mul_add, ← mul_add, habp, habq, mul_one, mul_one, hab]
  · match_scalars <;> noncomm_ring

/-- See `Convex.semilinear_image` for a version for semilinear maps, but requiring that `𝕜` be a
  linear order, instead of just a partial order. -/
/-
**Convex.linear_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.linear_image (hs : Convex 𝕜 s) (f : E ->ₗ[𝕜] F) : Convex 𝕜 (f '' s)
参数：hs : Convex 𝕜 s；f : E ->ₗ[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…

--- 原说明 ---
See `Convex.semilinear_image` for a version for semilinear maps, but requiring t
hat `𝕜` be a
  linear order, instead of just a partial order.
-/
theorem Convex.linear_image (hs : Convex 𝕜 s) (f : E →ₗ[𝕜] F) : Convex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, hs hx hy ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩
/-
**Convex.is_linear_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.is_linear_image (hs : Convex 𝕜 s) {f : E -> F} (hf : IsLinearMap 𝕜 
f) : Convex 𝕜 (f '' s)
参数：hs : Convex 𝕜 s；hf : IsLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.linear_image`：Convex.linear_image (hs : Convex 𝕜 s) (f : E ->ₗ[𝕜]
 F) : Convex 𝕜 (f '' s)
-/
theorem Convex.is_linear_image (hs : Convex 𝕜 s) {f : E → F} (hf : IsLinearMap 𝕜 f) :
    Convex 𝕜 (f '' s) :=
  hs.linear_image <| hf.mk' f
/-
**Convex.linear_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.linear_preimage {s : Set F} (hs : Convex 𝕜 s) (f : E ->ₗ[𝕜] F) : Co
nvex 𝕜 (f ⁻¹' s)
参数：hs : Convex 𝕜 s；f : E ->ₗ[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
theorem Convex.linear_preimage {s : Set F} (hs : Convex 𝕜 s) (f : E →ₗ[𝕜] F) : Convex 𝕜 (f ⁻¹' s) :=
  fun x hx y hy a b ha hb hab => by
    rw [mem_preimage, f.map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]
    exact hs hx hy ha hb hab
/-
**Convex.is_linear_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.is_linear_preimage {s : Set F} (hs : Convex 𝕜 s) {f : E -> F} (hf :
 IsLinearMap 𝕜 f) : Convex 𝕜 (f ⁻¹' s)
参数：hs : Convex 𝕜 s；hf : IsLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.linear_preimage`：Convex.linear_preimage {s : Set F} (hs : Convex 
𝕜 s) (f : E ->ₗ[𝕜] F) : Convex 𝕜 (f ⁻¹' s)
-/
theorem Convex.is_linear_preimage {s : Set F} (hs : Convex 𝕜 s) {f : E → F} (hf : IsLinearMap 𝕜 f) :
    Convex 𝕜 (f ⁻¹' s) := hs.linear_preimage <| hf.mk' f
/-
**Convex.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.add {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s +
 t)
参数：hs : Convex 𝕜 s；ht : Convex 𝕜 t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.add_image_prod`：∀ {α : Type u_2} [inst : Add α] {s t : Set α}, (fun 
x => x.1 + x.2) '' s ×ˢ t = s + t
· 使用定理 `Convex.is_linear_image`：Convex.is_linear_image (hs : Convex 𝕜 s) {f : E 
-> F} (hf : IsLinearMap 𝕜 f) : Convex 𝕜 (f '' s)
· 使用定理 `Convex.prod`：Convex.prod {s : Set E} {t : Set F} (hs : Convex 𝕜 s) (ht :
 Convex 𝕜 t) : Convex 𝕜 (s ×ˢ t)
· 使用定理 `IsLinearMap.isLinearMap_add`：isLinearMap_add [AddCommMonoid M] [Module R
 M] : IsLinearMap R fun x : M × M => x.1 + x.2
-/
theorem Convex.add {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s + t) := by
  rw [← add_image_prod]
  exact (hs.prod ht).is_linear_image IsLinearMap.isLinearMap_add

variable (𝕜 E)

/-- The convex sets form an additive submonoid under pointwise addition. -/
/-
**convexAddSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：convexAddSubmonoid : AddSubmonoid (Set E) where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.add`：Convex.add {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
 Convex 𝕜 (s + t)
· 使用定理 `convex_zero`：convex_zero : Convex 𝕜 (0 : Set E)

--- 原说明 ---
The convex sets form an additive submonoid under pointwise addition.
-/
noncomputable def convexAddSubmonoid : AddSubmonoid (Set E) where
  carrier := {s : Set E | Convex 𝕜 s}
  zero_mem' := convex_zero
  add_mem' := Convex.add

@[simp, norm_cast]
/-
**coe_convexAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_convexAddSubmonoid : ↑(convexAddSubmonoid 𝕜 E) = {s : Set E | Convex 𝕜
 s}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_convexAddSubmonoid : ↑(convexAddSubmonoid 𝕜 E) = {s : Set E | Convex 𝕜 s} :=
  rfl

variable {𝕜 E}

@[simp]
/-
**mem_convexAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_convexAddSubmonoid {s : Set E} : s in convexAddSubmonoid 𝕜 E ↔ Convex 
𝕜 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_convexAddSubmonoid {s : Set E} : s ∈ convexAddSubmonoid 𝕜 E ↔ Convex 𝕜 s :=
  Iff.rfl
/-
**convex_list_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_list_sum {l : List (Set E)} (h : forall i in l, Convex 𝕜 i) : Conve
x 𝕜 l.sum
参数：Set E；h : forall i in l, Convex 𝕜 i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.list_sum_mem`：∀ {M : Type u_1} [inst : AddMonoid M] (s : Ad
dSubmonoid M) {l : List M}, (∀ x ∈ l, x ∈ s) → l.sum ∈ s
-/
theorem convex_list_sum {l : List (Set E)} (h : ∀ i ∈ l, Convex 𝕜 i) : Convex 𝕜 l.sum :=
  (convexAddSubmonoid 𝕜 E).list_sum_mem h
/-
**convex_multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_multiset_sum {s : Multiset (Set E)} (h : forall i in s, Convex 𝕜 i)
 : Convex 𝕜 s.sum
参数：Set E；h : forall i in s, Convex 𝕜 i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.multiset_sum_mem`：∀ {M : Type u_4} [inst : AddCommMonoid M]
 (S : AddSubmonoid M) (m : Multiset M), (∀ a ∈ m, a ∈ S) → m.sum ∈ S
-/
theorem convex_multiset_sum {s : Multiset (Set E)} (h : ∀ i ∈ s, Convex 𝕜 i) : Convex 𝕜 s.sum :=
  (convexAddSubmonoid 𝕜 E).multiset_sum_mem _ h
/-
**convex_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_sum {ι} {s : Finset ι} (t : ι -> Set E) (h : forall i in s, Convex 
𝕜 (t i)) : Convex 𝕜 (∑ i in s, t i)
参数：t : ι -> Set E；h : forall i in s, Convex 𝕜 (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.sum_mem`：∀ {M : Type u_4} [inst : AddCommMonoid M] (S : Add
Submonoid M) {ι : Type u_5} {t : Finset ι} {f : ι → M},   (∀ c ∈ t, f c ∈ S) → ∑
 c ∈ t, f …
-/
theorem convex_sum {ι} {s : Finset ι} (t : ι → Set E) (h : ∀ i ∈ s, Convex 𝕜 (t i)) :
    Convex 𝕜 (∑ i ∈ s, t i) :=
  (convexAddSubmonoid 𝕜 E).sum_mem h
/-
**Convex.vadd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.vadd (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 (z +ᵥ s)
参数：hs : Convex 𝕜 s；z : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Convex.add`：Convex.add {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
 Convex 𝕜 (s + t)
· 使用定理 `convex_singleton`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (c :…
-/
theorem Convex.vadd (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 (z +ᵥ s) := by
  simp_rw [← image_vadd, vadd_eq_add, ← singleton_add]
  exact (convex_singleton _).add hs
/-
**Convex.translate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.translate (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 ((fun x => z + x) ''
 s)
参数：hs : Convex 𝕜 s；z : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.vadd`：Convex.vadd (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 (z +ᵥ s)
-/
theorem Convex.translate (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 ((fun x => z + x) '' s) :=
  hs.vadd _

/-- The translation of a convex set is also convex. -/
/-
**Convex.translate_preimage_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.translate_preimage_right (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 ((fun
 x => z + x) ⁻¹' s)
参数：hs : Convex 𝕜 s；z : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂

--- 原说明 ---
The translation of a convex set is also convex.
-/
theorem Convex.translate_preimage_right (hs : Convex 𝕜 s) (z : E) :
    Convex 𝕜 ((fun x => z + x) ⁻¹' s) := by
  intro x hx y hy a b ha hb hab
  have h := hs hx hy ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at h

/-- The translation of a convex set is also convex. -/
/-
**Convex.translate_preimage_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.translate_preimage_left (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 ((fun 
x => x + z) ⁻¹' s)
参数：hs : Convex 𝕜 s；z : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Convex.translate_preimage_right`：Convex.translate_preimage_right (hs : C
onvex 𝕜 s) (z : E) : Convex 𝕜 ((fun x => z + x) ⁻¹' s)

--- 原说明 ---
The translation of a convex set is also convex.
-/
theorem Convex.translate_preimage_left (hs : Convex 𝕜 s) (z : E) :
    Convex 𝕜 ((fun x => x + z) ⁻¹' s) := by
  simpa only [add_comm] using hs.translate_preimage_right z

section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β]

/-
**convex_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_Iic (r : β) : Convex 𝕜 (Iic r)
参数：r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
-/
theorem convex_Iic (r : β) : Convex 𝕜 (Iic r) := fun x hx y hy a b ha hb hab =>
  calc
    a • x + b • y ≤ a • r + b • r :=
      add_le_add (smul_le_smul_of_nonneg_left hx ha) (smul_le_smul_of_nonneg_left hy hb)
    _ = r := Convex.combo_self hab _
/-
**convex_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_Ici (r : β) : Convex 𝕜 (Ici r)
参数：r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_Iic`：convex_Iic (r : β) : Convex 𝕜 (Iic r)
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
-/
theorem convex_Ici (r : β) : Convex 𝕜 (Ici r) :=
  convex_Iic (β := βᵒᵈ) r
/-
**convex_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
参数：r s : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Set.Ici_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iic b = Set.Icc a b
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `convex_Iic`：convex_Iic (r : β) : Convex 𝕜 (Iic r)
-/
theorem convex_Icc (r s : β) : Convex 𝕜 (Icc r s) :=
  Ici_inter_Iic.subst ((convex_Ici r).inter <| convex_Iic s)
/-
**convex_halfSpace_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_halfSpace_le {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 
{ w | f w <= r }
参数：h : IsLinearMap 𝕜 f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.is_linear_preimage`：Convex.is_linear_preimage {s : Set F} (hs : C
onvex 𝕜 s) {f : E -> F} (hf : IsLinearMap 𝕜 f) : Convex 𝕜 (f ⁻¹' s)
· 使用定理 `convex_Iic`：convex_Iic (r : β) : Convex 𝕜 (Iic r)
-/
theorem convex_halfSpace_le {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w ≤ r } :=
  (convex_Iic r).is_linear_preimage h
/-
**convex_halfSpace_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_halfSpace_ge {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 
{ w | r <= f w }
参数：h : IsLinearMap 𝕜 f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.is_linear_preimage`：Convex.is_linear_preimage {s : Set F} (hs : C
onvex 𝕜 s) {f : E -> F} (hf : IsLinearMap 𝕜 f) : Convex 𝕜 (f ⁻¹' s)
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
-/
theorem convex_halfSpace_ge {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | r ≤ f w } :=
  (convex_Ici r).is_linear_preimage h
/-
**convex_hyperplane** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_hyperplane {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { 
w | f w = r }
参数：h : IsLinearMap 𝕜 f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
· 使用定理 `convex_halfSpace_le`：convex_halfSpace_le {f : E -> β} (h : IsLinearMap 𝕜
 f) (r : β) : Convex 𝕜 { w | f w <= r }
· 使用定理 `convex_halfSpace_ge`：convex_halfSpace_ge {f : E -> β} (h : IsLinearMap 𝕜
 f) (r : β) : Convex 𝕜 { w | r <= f w }
-/
theorem convex_hyperplane {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w = r } := by
  simp_rw [le_antisymm_iff]
  exact (convex_halfSpace_le h r).inter (convex_halfSpace_ge h r)

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β]
  [Module 𝕜 β] [PosSMulStrictMono 𝕜 β]

/-
**convex_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_Iio (r : β) : Convex 𝕜 (Iio r)
参数：r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_lt_add_of_lt_of_le`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c ≤ d → a 
+ c < b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
-/
theorem convex_Iio (r : β) : Convex 𝕜 (Iio r) := by
  intro x hx y hy a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [zero_smul, zero_add, hab, one_smul]
  rw [mem_Iio] at hx hy
  calc
    a • x + b • y < a • r + b • r := add_lt_add_of_lt_of_le
        (smul_lt_smul_of_pos_left hx ha') (smul_le_smul_of_nonneg_left hy.le hb)
    _ = r := Convex.combo_self hab _
/-
**convex_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_Ioi (r : β) : Convex 𝕜 (Ioi r)
参数：r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_Iio`：convex_Iio (r : β) : Convex 𝕜 (Iio r)
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
-/
theorem convex_Ioi (r : β) : Convex 𝕜 (Ioi r) :=
  convex_Iio (β := βᵒᵈ) r
/-
**convex_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_Ioo (r s : β) : Convex 𝕜 (Ioo r s)
参数：r s : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Set.Ioi_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iio b = Set.Ioo a b
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
· 使用定理 `convex_Ioi`：convex_Ioi (r : β) : Convex 𝕜 (Ioi r)
· 使用定理 `convex_Iio`：convex_Iio (r : β) : Convex 𝕜 (Iio r)
-/
theorem convex_Ioo (r s : β) : Convex 𝕜 (Ioo r s) :=
  Ioi_inter_Iio.subst ((convex_Ioi r).inter <| convex_Iio s)
/-
**convex_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_Ico (r s : β) : Convex 𝕜 (Ico r s)
参数：r s : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Set.Ici_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iio b = Set.Ico a b
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `convex_Iio`：convex_Iio (r : β) : Convex 𝕜 (Iio r)
-/
theorem convex_Ico (r s : β) : Convex 𝕜 (Ico r s) :=
  Ici_inter_Iio.subst ((convex_Ici r).inter <| convex_Iio s)
/-
**convex_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_Ioc (r s : β) : Convex 𝕜 (Ioc r s)
参数：r s : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Set.Ioi_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iic b = Set.Ioc a b
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
· 使用定理 `convex_Ioi`：convex_Ioi (r : β) : Convex 𝕜 (Ioi r)
· 使用定理 `convex_Iic`：convex_Iic (r : β) : Convex 𝕜 (Iic r)
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
-/
theorem convex_Ioc (r s : β) : Convex 𝕜 (Ioc r s) :=
  Ioi_inter_Iic.subst ((convex_Ioi r).inter <| convex_Iic s)
/-
**convex_halfSpace_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_halfSpace_lt {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 
{ w | f w < r }
参数：h : IsLinearMap 𝕜 f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.is_linear_preimage`：Convex.is_linear_preimage {s : Set F} (hs : C
onvex 𝕜 s) {f : E -> F} (hf : IsLinearMap 𝕜 f) : Convex 𝕜 (f ⁻¹' s)
· 使用定理 `convex_Iio`：convex_Iio (r : β) : Convex 𝕜 (Iio r)
-/
theorem convex_halfSpace_lt {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w < r } :=
  (convex_Iio r).is_linear_preimage h
/-
**convex_halfSpace_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_halfSpace_gt {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 
{ w | r < f w }
参数：h : IsLinearMap 𝕜 f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.is_linear_preimage`：Convex.is_linear_preimage {s : Set F} (hs : C
onvex 𝕜 s) {f : E -> F} (hf : IsLinearMap 𝕜 f) : Convex 𝕜 (f ⁻¹' s)
· 使用定理 `convex_Ioi`：convex_Ioi (r : β) : Convex 𝕜 (Ioi r)
-/
theorem convex_halfSpace_gt {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | r < f w } :=
  (convex_Ioi r).is_linear_preimage h
end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β]

/-
**convex_uIcc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_uIcc (r s : β) : Convex 𝕜 (uIcc r s)
参数：r s : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
-/
theorem convex_uIcc (r s : β) : Convex 𝕜 (uIcc r s) :=
  convex_Icc _ _

end LinearOrderedAddCommMonoid

end Module

section IsScalarTower

variable [ZeroLEOneClass 𝕜] [Module 𝕜 E]
variable (R : Type*) [Semiring R] [PartialOrder R] [Module R E]
variable [Module R 𝕜] [IsScalarTower R 𝕜 E]

/-- Lift the convexity of a set up through a scalar tower. -/
/-
**Convex.lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.lift [SMulPosMono R 𝕜] {s : Set E} (hs : Convex 𝕜 s) : Convex R s
参数：hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z

--- 原说明 ---
Lift the convexity of a set up through a scalar tower.
-/
theorem Convex.lift [SMulPosMono R 𝕜] {s : Set E} (hs : Convex 𝕜 s) : Convex R s := by
  intro x hx y hy a b ha hb hab
  suffices (a • (1 : 𝕜)) • x + (b • (1 : 𝕜)) • y ∈ s by simpa using this
  refine hs hx hy ?_ ?_ (by simpa [add_smul] using congr($(hab) • (1 : 𝕜)))
  all_goals exact zero_smul R (1 : 𝕜) ▸ smul_le_smul_of_nonneg_right ‹_› zero_le_one

end IsScalarTower

end AddCommMonoid

section LinearOrderedAddCommMonoid

variable [AddCommMonoid E] [LinearOrder E] [IsOrderedAddMonoid E]
  [PartialOrder β] [Module 𝕜 E] [PosSMulMono 𝕜 E]
  {s : Set E} {f : E → β}

/-
**MonotoneOn.convex_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.convex_le (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) : Con
vex 𝕜 ({ x in s | f x <= r })
参数：hf : MonotoneOn f s；hs : Convex 𝕜 s；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `max_rec'`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α} (p : α → Pro
p), p a → p b → p (max a b)
· 使用定理 `Convex.combo_le_max`：Convex.combo_le_max (x y : E) (ha : 0 <= a) (hb : 0
 <= b) (hab : a + b = 1) : a • x + b • y <= max x y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem MonotoneOn.convex_le (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x ≤ r }) := fun x hx y hy _ _ ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' (· ∈ s) hx.1 hy.1)
      (Convex.combo_le_max x y ha hb hab)).trans
      (max_rec' (f · ≤ r) hx.2 hy.2)⟩
/-
**MonotoneOn.convex_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.convex_lt (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) : Con
vex 𝕜 ({ x in s | f x < r })
参数：hf : MonotoneOn f s；hs : Convex 𝕜 s；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `max_rec'`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α} (p : α → Pro
p), p a → p b → p (max a b)
· 使用定理 `Convex.combo_le_max`：Convex.combo_le_max (x y : E) (ha : 0 <= a) (hb : 0
 <= b) (hab : a + b = 1) : a • x + b • y <= max x y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem MonotoneOn.convex_lt (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x < r }) := fun x hx y hy _ _ ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' (· ∈ s) hx.1 hy.1)
          (Convex.combo_le_max x y ha hb hab)).trans_lt
      (max_rec' (f · < r) hx.2 hy.2)⟩
/-
**MonotoneOn.convex_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.convex_ge (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) : Con
vex 𝕜 ({ x in s | r <= f x })
参数：hf : MonotoneOn f s；hs : Convex 𝕜 s；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.convex_le`：MonotoneOn.convex_le (hf : MonotoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | f x <= r })
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `MonotoneOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (⇑OrderDua
l.toD…
-/
theorem MonotoneOn.convex_ge (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | r ≤ f x }) :=
  MonotoneOn.convex_le (E := Eᵒᵈ) (β := βᵒᵈ) hf.dual (by exact hs) r
/-
**MonotoneOn.convex_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.convex_gt (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) : Con
vex 𝕜 ({ x in s | r < f x })
参数：hf : MonotoneOn f s；hs : Convex 𝕜 s；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.convex_lt`：MonotoneOn.convex_lt (hf : MonotoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | f x < r })
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `MonotoneOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (⇑OrderDua
l.toD…
-/
theorem MonotoneOn.convex_gt (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | r < f x }) :=
  MonotoneOn.convex_lt (E := Eᵒᵈ) (β := βᵒᵈ) hf.dual (by exact hs) r
/-
**AntitoneOn.convex_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.convex_le (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) : Con
vex 𝕜 ({ x in s | f x <= r })
参数：hf : AntitoneOn f s；hs : Convex 𝕜 s；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.convex_ge`：MonotoneOn.convex_ge (hf : MonotoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | r <= f x })
-/
theorem AntitoneOn.convex_le (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x ≤ r }) :=
  MonotoneOn.convex_ge (β := βᵒᵈ) hf hs r
/-
**AntitoneOn.convex_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.convex_lt (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) : Con
vex 𝕜 ({ x in s | f x < r })
参数：hf : AntitoneOn f s；hs : Convex 𝕜 s；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.convex_gt`：MonotoneOn.convex_gt (hf : MonotoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | r < f x })
-/
theorem AntitoneOn.convex_lt (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x < r }) :=
  MonotoneOn.convex_gt (β := βᵒᵈ) hf hs r
/-
**AntitoneOn.convex_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.convex_ge (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) : Con
vex 𝕜 ({ x in s | r <= f x })
参数：hf : AntitoneOn f s；hs : Convex 𝕜 s；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.convex_le`：MonotoneOn.convex_le (hf : MonotoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | f x <= r })
-/
theorem AntitoneOn.convex_ge (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | r ≤ f x }) :=
  MonotoneOn.convex_le (β := βᵒᵈ) hf hs r
/-
**AntitoneOn.convex_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.convex_gt (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) : Con
vex 𝕜 ({ x in s | r < f x })
参数：hf : AntitoneOn f s；hs : Convex 𝕜 s；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.convex_lt`：MonotoneOn.convex_lt (hf : MonotoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | f x < r })
-/
theorem AntitoneOn.convex_gt (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | r < f x }) :=
  MonotoneOn.convex_lt (β := βᵒᵈ) hf hs r
/-
**Monotone.convex_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.convex_le (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x <= r }
参数：hf : Monotone f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Set.sep_univ`：sep_univ : { x in (univ : Set α) | p x } = { x | p x }
· 使用定理 `MonotoneOn.convex_le`：MonotoneOn.convex_le (hf : MonotoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | f x <= r })
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
-/
theorem Monotone.convex_le (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)
/-
**Monotone.convex_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.convex_lt (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x <= r }
参数：hf : Monotone f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Set.sep_univ`：sep_univ : { x in (univ : Set α) | p x } = { x | p x }
· 使用定理 `MonotoneOn.convex_le`：MonotoneOn.convex_le (hf : MonotoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | f x <= r })
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
-/
theorem Monotone.convex_lt (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)
/-
**Monotone.convex_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.convex_ge (hf : Monotone f) (r : β) : Convex 𝕜 { x | r <= f x }
参数：hf : Monotone f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Set.sep_univ`：sep_univ : { x in (univ : Set α) | p x } = { x | p x }
· 使用定理 `MonotoneOn.convex_ge`：MonotoneOn.convex_ge (hf : MonotoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | r <= f x })
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
-/
theorem Monotone.convex_ge (hf : Monotone f) (r : β) : Convex 𝕜 { x | r ≤ f x } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_ge convex_univ r)
/-
**Monotone.convex_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.convex_gt (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x <= r }
参数：hf : Monotone f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Set.sep_univ`：sep_univ : { x in (univ : Set α) | p x } = { x | p x }
· 使用定理 `MonotoneOn.convex_le`：MonotoneOn.convex_le (hf : MonotoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | f x <= r })
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
-/
theorem Monotone.convex_gt (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)
/-
**Antitone.convex_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.convex_le (hf : Antitone f) (r : β) : Convex 𝕜 { x | f x <= r }
参数：hf : Antitone f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Set.sep_univ`：sep_univ : { x in (univ : Set α) | p x } = { x | p x }
· 使用定理 `AntitoneOn.convex_le`：AntitoneOn.convex_le (hf : AntitoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | f x <= r })
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
-/
theorem Antitone.convex_le (hf : Antitone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_le convex_univ r)
/-
**Antitone.convex_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.convex_lt (hf : Antitone f) (r : β) : Convex 𝕜 { x | f x < r }
参数：hf : Antitone f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Set.sep_univ`：sep_univ : { x in (univ : Set α) | p x } = { x | p x }
· 使用定理 `AntitoneOn.convex_lt`：AntitoneOn.convex_lt (hf : AntitoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | f x < r })
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
-/
theorem Antitone.convex_lt (hf : Antitone f) (r : β) : Convex 𝕜 { x | f x < r } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_lt convex_univ r)
/-
**Antitone.convex_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.convex_ge (hf : Antitone f) (r : β) : Convex 𝕜 { x | r <= f x }
参数：hf : Antitone f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Set.sep_univ`：sep_univ : { x in (univ : Set α) | p x } = { x | p x }
· 使用定理 `AntitoneOn.convex_ge`：AntitoneOn.convex_ge (hf : AntitoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | r <= f x })
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
-/
theorem Antitone.convex_ge (hf : Antitone f) (r : β) : Convex 𝕜 { x | r ≤ f x } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_ge convex_univ r)
/-
**Antitone.convex_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.convex_gt (hf : Antitone f) (r : β) : Convex 𝕜 { x | r < f x }
参数：hf : Antitone f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Set.sep_univ`：sep_univ : { x in (univ : Set α) | p x } = { x | p x }
· 使用定理 `AntitoneOn.convex_gt`：AntitoneOn.convex_gt (hf : AntitoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | r < f x })
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
-/
theorem Antitone.convex_gt (hf : Antitone f) (r : β) : Convex 𝕜 { x | r < f x } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_gt convex_univ r)

end LinearOrderedAddCommMonoid

end OrderedSemiring

section OrderedCommSemiring

variable [CommSemiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

/-
**Convex.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.smul (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 (c • s)
参数：hs : Convex 𝕜 s；c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.linear_image`：Convex.linear_image (hs : Convex 𝕜 s) (f : E ->ₗ[𝕜]
 F) : Convex 𝕜 (f '' s)
-/
theorem Convex.smul (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 (c • s) :=
  hs.linear_image (LinearMap.lsmul _ _ c)
/-
**Convex.smul_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.smul_preimage (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 ((fun z => c • z
) ⁻¹' s)
参数：hs : Convex 𝕜 s；c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.linear_preimage`：Convex.linear_preimage {s : Set F} (hs : Convex 
𝕜 s) (f : E ->ₗ[𝕜] F) : Convex 𝕜 (f ⁻¹' s)
-/
theorem Convex.smul_preimage (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 ((fun z => c • z) ⁻¹' s) :=
  hs.linear_preimage (LinearMap.lsmul _ _ c)
/-
**Convex.affinity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.affinity (hs : Convex 𝕜 s) (z : E) (c : 𝕜) : Convex 𝕜 ((fun x => z 
+ c • x) '' s)
参数：hs : Convex 𝕜 s；z : E；c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Convex.vadd`：Convex.vadd (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 (z +ᵥ s)
· 使用定理 `Convex.smul`：Convex.smul (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 (c • s)
-/
theorem Convex.affinity (hs : Convex 𝕜 s) (z : E) (c : 𝕜) :
    Convex 𝕜 ((fun x => z + c • x) '' s) := by
  simpa only [← image_smul, ← image_vadd, image_image] using! (hs.smul c).vadd z

end AddCommMonoid

end OrderedCommSemiring

section StrictOrderedCommSemiring

variable [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-
**convex_openSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_openSegment (a b : E) : Convex 𝕜 (openSegment 𝕜 a b)
参数：a b : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convex_iff_openSegment_subset`：convex_iff_openSegment_subset [ZeroLEOneC
lass 𝕜] : Convex 𝕜 s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> openSegment 𝕜
 x y subseteq s
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `Mathlib.Tactic.LinearCombination.add_eq_eq`：add_eq_eq [Add α] (p₁ : (a₁ 
: α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `_private.Mathlib.Analysis.Convex.Basic.0.convex_openSegment._abel_1_1`：∀
 {𝕜 : Type u_1} [inst : CommSemiring 𝕜] (ap bp aq bq a b : 𝕜),   a * ap + b * aq
 + (a * bp + b * bq) + (a + b + 1) = 1 + (a * ap + a * bp +…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
（共 56 条，此处仅展示前 30 条）
-/
theorem convex_openSegment (a b : E) : Convex 𝕜 (openSegment 𝕜 a b) := by
  rw [convex_iff_openSegment_subset]
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ z ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨a * ap + b * aq, a * bp + b * bq, by positivity, by positivity, ?_, ?_⟩
  · linear_combination (norm := noncomm_ring) a * habp + b * habq + hab
  · module

end StrictOrderedCommSemiring

section OrderedRing

variable [Ring 𝕜] [PartialOrder 𝕜]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s t : Set E}

@[simp]
/-
**convex_vadd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_vadd (a : E) : Convex 𝕜 (a +ᵥ s) ↔ Convex 𝕜 s
参数：a : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_vadd_vadd`：∀ {G : Type u_3} {α : Type u_5} [inst : AddGroup G] [inst
_1 : AddAction G α] (g : G) (a : α), -g +ᵥ g +ᵥ a = a
· 使用定理 `Convex.vadd`：Convex.vadd (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 (z +ᵥ s)
-/
theorem convex_vadd (a : E) : Convex 𝕜 (a +ᵥ s) ↔ Convex 𝕜 s :=
  ⟨fun h ↦ by simpa using h.vadd (-a), fun h ↦ h.vadd _⟩

/-- Affine subspaces are convex. -/
/-
**AffineSubspace.convex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineSubspace.convex (Q : AffineSubspace 𝕜 E) : Convex 𝕜 (Q : Set E)
参数：Q : AffineSubspace 𝕜 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convex.combo_eq_smul_sub_add`：Convex.combo_eq_smul_sub_add [Module R M] 
{x y : M} {a b : R} (h : a + b = 1) : a • x + b • y = b • (y - x) + x
· 使用定理 `AffineSubspace.smul_vsub_vadd_mem'`：∀ {k : Type u_1} {V : Type u_2} {P :
 Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V
]   [inst_3 : AddTorsor …

--- 原说明 ---
Affine subspaces are convex.
-/
theorem AffineSubspace.convex (Q : AffineSubspace 𝕜 E) : Convex 𝕜 (Q : Set E) :=
  fun x hx y hy a b _ _ hab ↦ by simpa [Convex.combo_eq_smul_sub_add hab] using! Q.2 _ hy hx hx

/-- The preimage of a convex set under an affine map is convex. -/
/-
**Convex.affine_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.affine_preimage (f : E ->ᵃ[𝕜] F) {s : Set F} (hs : Convex 𝕜 s) : Co
nvex 𝕜 (f ⁻¹' s)
参数：f : E ->ᵃ[𝕜] F；hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarConvex.affine_preimage`：StarConvex.affine_preimage (f : E ->ᵃ[𝕜] F) 
{s : Set F} (hs : StarConvex 𝕜 (f x) s) : StarConvex 𝕜 x (f ⁻¹' s)

--- 原说明 ---
The preimage of a convex set under an affine map is convex.
-/
theorem Convex.affine_preimage (f : E →ᵃ[𝕜] F) {s : Set F} (hs : Convex 𝕜 s) : Convex 𝕜 (f ⁻¹' s) :=
  fun _ hx => (hs hx).affine_preimage _

/-- The image of a convex set under an affine map is convex. -/
/-
**Convex.affine_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.affine_image (f : E ->ᵃ[𝕜] F) (hs : Convex 𝕜 s) : Convex 𝕜 (f '' s)
参数：f : E ->ᵃ[𝕜] F；hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarConvex.affine_image`：StarConvex.affine_image (f : E ->ᵃ[𝕜] F) {s : S
et E} (hs : StarConvex 𝕜 x s) : StarConvex 𝕜 (f x) (f '' s)

--- 原说明 ---
The image of a convex set under an affine map is convex.
-/
theorem Convex.affine_image (f : E →ᵃ[𝕜] F) (hs : Convex 𝕜 s) : Convex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  exact (hs hx).affine_image _
/-
**Convex.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.neg (hs : Convex 𝕜 s) : Convex 𝕜 (-s)
参数：hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.is_linear_preimage`：Convex.is_linear_preimage {s : Set F} (hs : C
onvex 𝕜 s) {f : E -> F} (hf : IsLinearMap 𝕜 f) : Convex 𝕜 (f ⁻¹' s)
· 使用定理 `IsLinearMap.isLinearMap_neg`：isLinearMap_neg : IsLinearMap R fun z : M =
> -z
-/
theorem Convex.neg (hs : Convex 𝕜 s) : Convex 𝕜 (-s) :=
  hs.is_linear_preimage IsLinearMap.isLinearMap_neg
/-
**Convex.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.sub (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s - t)
参数：hs : Convex 𝕜 s；ht : Convex 𝕜 t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Convex.add`：Convex.add {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
 Convex 𝕜 (s + t)
· 使用定理 `Convex.neg`：Convex.neg (hs : Convex 𝕜 s) : Convex 𝕜 (-s)
-/
theorem Convex.sub (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s - t) := by
  rw [sub_eq_add_neg]
  exact hs.add ht.neg

variable [AddRightMono 𝕜]
/-
**Convex.add_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.add_smul_mem (hs : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : x + y 
in s) {t : 𝕜} (ht : t in Icc (0 : 𝕜) 1) : x + t • y in s
参数：hs : Convex 𝕜 s；hx : x in s；hy : x + y in s；ht : t in Icc (0 : 𝕜) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `_private.Mathlib.Analysis.Convex.Basic.0.Convex.add_smul_mem._abel_1_1`：
∀ {𝕜 : Type u_1} [inst : Ring 𝕜] {t : 𝕜}, 1 = 1 + -t + t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem Convex.add_smul_mem (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : x + y ∈ s) {t : 𝕜}
    (ht : t ∈ Icc (0 : 𝕜) 1) : x + t • y ∈ s := by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by match_scalars <;> noncomm_ring
  rw [h]
  exact hs hx hy (sub_nonneg_of_le ht.2) ht.1 (sub_add_cancel _ _)
/-
**Convex.smul_mem_of_zero_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.smul_mem_of_zero_mem (hs : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) 
in s) (hx : x in s) {t : 𝕜} (ht : t in Icc (0 : 𝕜) 1) : t • x in s
参数：hs : Convex 𝕜 s；zero_mem : (0 : E) in s；hx : x in s；ht : t in Icc (0 : 𝕜) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Convex.add_smul_mem`：Convex.add_smul_mem (hs : Convex 𝕜 s) {x y : E} (hx
 : x in s) (hy : x + y in s) {t : 𝕜} (ht : t in Icc (0 : 𝕜) 1) : x + t • y in s
-/
theorem Convex.smul_mem_of_zero_mem (hs : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) ∈ s) (hx : x ∈ s)
    {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) : t • x ∈ s := by
  simpa using hs.add_smul_mem zero_mem (by simpa using hx) ht

set_option backward.isDefEq.respectTransparency false in
/-
**Convex.mapsTo_lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.mapsTo_lineMap (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in 
s) : MapsTo (AffineMap.lineMap x y) (Icc (0 : 𝕜) 1) s
参数：h : Convex 𝕜 s；hx : x in s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_eq_image_lineMap`：segment_eq_image_lineMap (x y : E) : [x -[𝕜] y
] = AffineMap.lineMap x y '' Icc (0 : 𝕜) 1
· 使用定理 `Convex.segment_subset`：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : [x -[𝕜] y] subseteq s
-/
theorem Convex.mapsTo_lineMap (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    MapsTo (AffineMap.lineMap x y) (Icc (0 : 𝕜) 1) s := by
  simpa only [mapsTo_iff_image_subset, segment_eq_image_lineMap] using h.segment_subset hx hy

set_option backward.isDefEq.respectTransparency false in
/-
**Convex.lineMap_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.lineMap_mem (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s) 
{t : 𝕜} (ht : t in Icc 0 1) : AffineMap.lineMap x y t in s
参数：h : Convex 𝕜 s；hx : x in s；hy : y in s；ht : t in Icc 0 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.mapsTo_lineMap`：Convex.mapsTo_lineMap (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : MapsTo (AffineMap.lineMap x y) (Icc (0 : 𝕜) 1) s
-/
theorem Convex.lineMap_mem (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {t : 𝕜}
    (ht : t ∈ Icc 0 1) : AffineMap.lineMap x y t ∈ s :=
  h.mapsTo_lineMap hx hy ht
/-
**Convex.add_smul_sub_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.add_smul_sub_mem (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y i
n s) {t : 𝕜} (ht : t in Icc (0 : 𝕜) 1) : x + t • (y - x) in s
参数：h : Convex 𝕜 s；hx : x in s；hy : y in s；ht : t in Icc (0 : 𝕜) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Convex.lineMap_mem`：Convex.lineMap_mem (h : Convex 𝕜 s) {x y : E} (hx : 
x in s) (hy : y in s) {t : 𝕜} (ht : t in Icc 0 1) : AffineMap.lineMap x y t in s
-/
theorem Convex.add_smul_sub_mem (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {t : 𝕜}
    (ht : t ∈ Icc (0 : 𝕜) 1) : x + t • (y - x) ∈ s := by
  rw [add_comm]
  exact h.lineMap_mem hx hy ht

end AddCommGroup

end OrderedRing

section LinearOrder

variable [Semiring 𝕜] [AddCommMonoid E]
section SemilinearMap

variable [PartialOrder 𝕜]
variable {𝕜' : Type*} [Semiring 𝕜'] [PartialOrder 𝕜']
variable {σ : 𝕜 →+* 𝕜'} [RingHomSurjective σ]
variable {F' : Type*} [AddCommMonoid F'] [Module 𝕜' F'] [Module 𝕜 E]

/-
**Convex.semilinear_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.semilinear_image {s : Set E} (hs : Convex 𝕜 s) (hσ : forall {s t}, 
σ s <= σ t ↔ s <= t) (f : E ->ₛₗ[σ] F') : Convex 𝕜' (f '' s)
参数：hs : Convex 𝕜 s；hσ : forall {s t}, σ s <= σ t ↔ s <= t；f : E ->ₛₗ[σ] F'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.is_surjective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {inst
 : Semiring R₁} {inst_1 : Semiring R₂} {σ : R₁ →+* R₂}   [self : RingHomSurjecti
ve σ], Function.Surje…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Function.Injective.of_eq_imp_le`：Function.Injective.of_eq_imp_le [Partia
lOrder α] {f : α -> β} (h : forall {x y}, f x = f y -> x <= y) : f.Injective
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `LinearMap.map_smulₛₗ`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃
 : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Convex.semilinear_image {s : Set E} (hs : Convex 𝕜 s) (hσ : ∀ {s t}, σ s ≤ σ t ↔ s ≤ t)
    (f : E →ₛₗ[σ] F') : Convex 𝕜' (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  obtain ⟨r, rfl⟩ : ∃ r : 𝕜, σ r = a := RingHomSurjective.is_surjective ..
  obtain ⟨t, rfl⟩ : ∃ t : 𝕜, σ t = b := RingHomSurjective.is_surjective ..
  refine ⟨r • x + t • y, hs hx hy (by simp_all [(@hσ 0 r).mp]) (by simp_all [(@hσ 0 t).mp])
    ?_, by simp⟩
  apply_fun σ using Function.Injective.of_eq_imp_le (hσ.mp ·.le)
  simpa

end SemilinearMap

variable [LinearOrder 𝕜] [IsOrderedRing 𝕜]

/-
**Convex_subadditive_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex_subadditive_le [SMul 𝕜 E] {f : E -> 𝕜} (hf1 : forall x y, f (x + y)
 <= (f x) + (f y)) (hf2 : forall ⦃c⦄ x, 0 <= c -> f (c • x) <= c * f x) (B : 𝕜) 
: Convex 𝕜 { x | f x <= B }
参数：hf1 : forall x y, f (x + y) <= (f x) + (f y)；hf2 : forall ⦃c⦄ x, 0 <= c -> f 
(c • x) <= c * f x；B : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convex_iff_segment_subset`：convex_iff_segment_subset : Convex 𝕜 s ↔ fora
ll ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> [x -[𝕜] y] subseteq s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsOrderedRing.toIsOrderedModule`：∀ {α : Type u_1} [inst : Semiring α] [i
nst_1 : PartialOrder α] [IsOrderedRing α], IsOrderedModule α α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem Convex_subadditive_le [SMul 𝕜 E] {f : E → 𝕜} (hf1 : ∀ x y, f (x + y) ≤ (f x) + (f y))
    (hf2 : ∀ ⦃c⦄ x, 0 ≤ c → f (c • x) ≤ c * f x) (B : 𝕜) :
    Convex 𝕜 { x | f x ≤ B } := by
  rw [convex_iff_segment_subset]
  rintro x hx y hy z ⟨a, b, ha, hb, hs, rfl⟩
  calc
    _ ≤ a • (f x) + b • (f y) := le_trans (hf1 _ _) (add_le_add (hf2 x ha) (hf2 y hb))
    _ ≤ a • B + b • B := by gcongr <;> assumption
    _ ≤ B := by rw [← add_smul, hs, one_smul]

end LinearOrder

/-
**Convex.midpoint_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.midpoint_mem [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddC
ommGroup E] [Module 𝕜 E] [Invertible (2 : 𝕜)] {s : Set E} {x y : E} (h : Convex 
𝕜 s) (hx : x in s) (hy : y in s) : midpoint 𝕜 x y in s
参数：2 : 𝕜；h : Convex 𝕜 s；hx : x in s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Convex.segment_subset`：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : [x -[𝕜] y] subseteq s
· 使用定理 `midpoint_mem_segment`：midpoint_mem_segment [Invertible (2 : 𝕜)] (x y : E
) : midpoint 𝕜 x y in [x -[𝕜] y]
-/
theorem Convex.midpoint_mem [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Invertible (2 : 𝕜)] {s : Set E} {x y : E}
    (h : Convex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s) : midpoint 𝕜 x y ∈ s :=
  h.segment_subset hx hy <| midpoint_mem_segment x y

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

/-- Alternative definition of set convexity, using division. -/
/-
**convex_iff_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_iff_div : Convex 𝕜 s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> 
forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> 0 < a + b -> (a / (a + b)) • x + (b / (a +
 b)) • y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `starConvex_iff_div`：starConvex_iff_div : StarConvex 𝕜 x s ↔ forall ⦃y⦄, 
y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> 0 < a + b -> (a / (a + b)) • x +
 (b / (a…

--- 原说明 ---
Alternative definition of set convexity, using division.
-/
theorem convex_iff_div :
    Convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
      ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → 0 < a + b → (a / (a + b)) • x + (b / (a + b)) • y ∈ s :=
  forall₂_congr fun _ _ => starConvex_iff_div
/-
**Convex.mem_smul_of_zero_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.mem_smul_of_zero_mem (h : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) i
n s) (hx : x in s) {t : 𝕜} (ht : 1 <= t) : x in t • s
参数：h : Convex 𝕜 s；zero_mem : (0 : E) in s；hx : x in s；ht : 1 <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Convex.smul_mem_of_zero_mem`：Convex.smul_mem_of_zero_mem (hs : Convex 𝕜 
s) {x : E} (zero_mem : (0 : E) in s) (hx : x in s) {t : 𝕜} (ht : t in Icc (0 : 𝕜
) 1) : t • x in s
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `inv_le_one_of_one_le₀`：inv_le_one_of_one_le₀ (ha : 1 <= a) : a⁻¹ <= 1
-/
theorem Convex.mem_smul_of_zero_mem (h : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) ∈ s) (hx : x ∈ s)
    {t : 𝕜} (ht : 1 ≤ t) : x ∈ t • s := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne']
  exact h.smul_mem_of_zero_mem zero_mem hx
    ⟨inv_nonneg.2 (zero_le_one.trans ht), inv_le_one_of_one_le₀ ht⟩
/-
**Convex.exists_mem_add_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.exists_mem_add_smul_eq (h : Convex 𝕜 s) {x y : E} {p q : 𝕜} (hx : x
 in s) (hy : y in s) (hp : 0 <= p) (hq : 0 <= q) : exists z in s, (p + q) • z = 
p • x + q • y
参数：h : Convex 𝕜 s；hx : x in s；hy : y in s；hp : 0 <= p；hq : 0 <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_eq_zero_iff_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [ins
t_1 : PartialOrder α] [AddLeftMono α] [AddRightMono α] {a b : α},   0 ≤ a → 0 ≤ 
b → (a + b = 0 …
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `convex_iff_div`：convex_iff_div : Convex 𝕜 s ↔ forall ⦃x⦄, x in s -> fora
ll ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> 0 < a + b -> (a / (a + b
)) •…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 58 条，此处仅展示前 30 条）
-/
theorem Convex.exists_mem_add_smul_eq (h : Convex 𝕜 s) {x y : E} {p q : 𝕜} (hx : x ∈ s) (hy : y ∈ s)
    (hp : 0 ≤ p) (hq : 0 ≤ q) : ∃ z ∈ s, (p + q) • z = p • x + q • y := by
  rcases _root_.em (p = 0 ∧ q = 0) with (⟨rfl, rfl⟩ | hpq)
  · use x, hx
    simp
  · replace hpq : 0 < p + q :=
      (add_nonneg hp hq).lt_of_ne' (mt (add_eq_zero_iff_of_nonneg hp hq).1 hpq)
    refine ⟨_, convex_iff_div.1 h hx hy hp hq hpq, ?_⟩
    match_scalars <;> field
/-
**Convex.add_smul** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜]   [inst_3 : AddCommGroup E] [inst_4 : _root_.Module 𝕜 E]
 {s : Set E},   Convex 𝕜 s → ∀ {p q : 𝕜}, 0 ≤ p → 0 ≤ q → (p + q) • s = p • s + 
q • s
参数：p + q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Set.add_smul_subset`：add_smul_subset (a b : α) (s : Set β) : (a + b) • s
 subseteq a • s + b • s
· 使用定理 `Convex.exists_mem_add_smul_eq`：Convex.exists_mem_add_smul_eq (h : Convex
 𝕜 s) {x y : E} {p q : 𝕜} (hx : x in s) (hy : y in s) (hp : 0 <= p) (hq : 0 <= q
) : exists z in s, …
-/
protected theorem Convex.add_smul (h_conv : Convex 𝕜 s) {p q : 𝕜} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (p + q) • s = p • s + q • s := (add_smul_subset _ _ _).antisymm <| by
  rintro _ ⟨_, ⟨v₁, h₁, rfl⟩, _, ⟨v₂, h₂, rfl⟩, rfl⟩
  exact h_conv.exists_mem_add_smul_eq h₁ h₂ hp hq
/-
**Convex.add_half_self_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.add_half_self_eq_self (h_conv : Convex 𝕜 s) : (2 : 𝕜)⁻¹ • s + (2 : 
𝕜)⁻¹ • s = s
参数：h_conv : Convex 𝕜 s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Convex.add_smul`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Field 𝕜] [inst_
1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : AddCommGroup E] [inst_4 :
 _roo…
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_raw_eq`：∀ {α : Type u} {n d : ℕ} [inst :
 DivisionSemiring α] {a : α}, Mathlib.Meta.NormNum.IsNNRat a n d → a = NNRat.raw
Cast n d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.of_raw`：∀ (α : Type u_1) [inst : DivisionSe
miring α] (n d : ℕ), ↑d ≠ 0 → Mathlib.Meta.NormNum.IsNNRat (NNRat.rawCast n d) n
 d
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.den_nz`：∀ {α : Type u_1} [inst : DivisionSe
miring α] {a : α} {n d : ℕ}, Mathlib.Meta.NormNum.IsNNRat a n d → ↑d ≠ 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.RingNF.nat_rawCast_1`：nat_rawCast_1 : (Nat.rawCast 1 : R)
 = 1
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
（共 31 条，此处仅展示前 30 条）
-/
theorem Convex.add_half_self_eq_self (h_conv : Convex 𝕜 s) : (2 : 𝕜)⁻¹ • s + (2 : 𝕜)⁻¹ • s = s := by
  rw [← h_conv.add_smul (by norm_num) (by norm_num)]
  ring_nf
  rw [one_smul]

end AddCommGroup

end LinearOrderedField

/-!
#### Convex sets in an ordered space
Relates `Convex` and `OrdConnected`.
-/


section

/-
**Set.OrdConnected.convex_of_chain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.OrdConnected.convex_of_chain [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMon
oid E] [PartialOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E] {s
 : Set E} (hs : s.OrdConnected) (h : IsChain (· <= ·) s) : Convex 𝕜 s
参数：hs : s.OrdConnected；h : IsChain (· <= ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `convex_iff_segment_subset`：convex_iff_segment_subset : Convex 𝕜 s ↔ fora
ll ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> [x -[𝕜] y] subseteq s
· 使用定理 `IsChain.total`：IsChain.total (h : IsChain r s) (hx : x in s) (hy : y in 
s) : x ≺ y ∨ y ≺ x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `segment_subset_Icc`：segment_subset_Icc (h : x <= y) : [x -[𝕜] y] subsete
q Icc x y
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_symm`：segment_symm (x y : E) : [x -[𝕜] y] = [y -[𝕜] x]
-/
theorem Set.OrdConnected.convex_of_chain [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
    [PartialOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E] {s : Set E}
    (hs : s.OrdConnected) (h : IsChain (· ≤ ·) s) : Convex 𝕜 s := by
  refine convex_iff_segment_subset.mpr fun x hx y hy => ?_
  obtain hxy | hyx := h.total hx hy
  · exact (segment_subset_Icc hxy).trans (hs.out hx hy)
  · rw [segment_symm]
    exact (segment_subset_Icc hyx).trans (hs.out hy hx)
/-
**Set.OrdConnected.convex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.OrdConnected.convex [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [L
inearOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E] {s : Set E} 
(hs : s.OrdConnected) : Convex 𝕜 s
参数：hs : s.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.convex_of_chain`：Set.OrdConnected.convex_of_chain [Semi
ring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid 
E] [Module 𝕜 E] [PosSM…
· 使用定理 `isChain_of_trichotomous`：isChain_of_trichotomous [Std.Trichotomous r] (s
 : Set α) : IsChain r s
-/
theorem Set.OrdConnected.convex [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [LinearOrder E]
    [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E] {s : Set E} (hs : s.OrdConnected) :
    Convex 𝕜 s :=
  hs.convex_of_chain <| isChain_of_trichotomous s
/-
**convex_iff_ordConnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_iff_ordConnected [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] 
{s : Set 𝕜} : Convex 𝕜 s ↔ s.OrdConnected
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
· 使用定理 `segment_eq_uIcc`：segment_eq_uIcc (x y : 𝕜) : [x -[𝕜] y] = uIcc x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem convex_iff_ordConnected [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜} :
    Convex 𝕜 s ↔ s.OrdConnected := by
  simp_rw [convex_iff_segment_subset, segment_eq_uIcc, ordConnected_iff_uIcc_subset]

alias ⟨Convex.ordConnected, _⟩ := convex_iff_ordConnected

end

/-! #### Convexity of submodules/subspaces -/


namespace Submodule

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]

/-
**Submodule.convex** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E] (K : Submodule 𝕜 E
), Convex 𝕜 ↑K
参数：K : Submodule 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
protected theorem convex (K : Submodule 𝕜 E) : Convex 𝕜 (↑K : Set E) := by
  repeat' intro
  refine add_mem (smul_mem _ _ ?_) (smul_mem _ _ ?_) <;> assumption
/-
**Submodule.starConvex** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E] (K : Submodule 𝕜 E
), StarConvex 𝕜 0 ↑K
参数：K : Submodule 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.convex`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (K :…
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
-/
protected theorem starConvex (K : Submodule 𝕜 E) : StarConvex 𝕜 (0 : E) K :=
  K.convex K.zero_mem
/-
**Submodule.Convex.semilinear_range** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Convex`
。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E] {𝕜' : Type u_5} [i
nst_4 : Semiring 𝕜'] {σ : 𝕜' →+* 𝕜} [inst_5 : RingHomSurjective σ]   {F' : Type 
u_6} [inst_6 : AddCommMonoid F'] [inst_7 : _root_.Module 𝕜' F'] (f : F' →ₛₗ[σ] E
), Convex 𝕜 ↑f.range
参数：f : F' →ₛₗ[σ] E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.convex`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (K :…
-/
theorem Convex.semilinear_range {𝕜' : Type*} [Semiring 𝕜'] {σ : 𝕜' →+* 𝕜}
    [RingHomSurjective σ] {F' : Type*} [AddCommMonoid F'] [Module 𝕜' F']
    (f : F' →ₛₗ[σ] E) : Convex 𝕜 (LinearMap.range f : Set E) := Submodule.convex ..

end Submodule

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable {M : Type*} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]
variable [PartialOrder R] [PartialOrder A]

/-
**convex_of_nonneg_surjective_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：convex_of_nonneg_surjective_algebraMap [FaithfulSMul R A] {s : Set M} (hal
g : Set.Ici 0 subseteq algebraMap R A '' Set.Ici 0) (hs : Convex R s) : Convex A
 s
参数：halg : Set.Ici 0 subseteq algebraMap R A '' Set.Ici 0；hs : Convex R s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `FaithfulSMul.algebraMap_eq_one_iff`：algebraMap_eq_one_iff {r : R} : alge
braMap R A r = 1 ↔ r = 1
· 使用定理 `algebraMap.coe_add`：coe_add (a b : R) : (↑(a + b : R) : A) = ↑a + ↑b
-/
lemma convex_of_nonneg_surjective_algebraMap [FaithfulSMul R A] {s : Set M}
    (halg : Set.Ici 0 ⊆ algebraMap R A '' Set.Ici 0) (hs : Convex R s) :
    Convex A s := by
  simp only [Convex, StarConvex] at hs ⊢
  intro u hu v hv a b ha hb hab
  obtain ⟨c, hc1, hc2⟩ := halg ha
  obtain ⟨d, hd1, hd2⟩ := halg hb
  convert hs hu hv hc1 hd1 _
  · rw [← hc2, algebraMap_smul]
  · rw [← hd2, algebraMap_smul]
  rw [← hc2, ← hd2, ← algebraMap.coe_add] at hab
  exact (FaithfulSMul.algebraMap_eq_one_iff R A).mp hab

end CommSemiring

