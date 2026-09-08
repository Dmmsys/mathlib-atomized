/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Topology.Neighborhoods

/-!
# Lemmas on cluster and accumulation points

In this file we prove various lemmas on [cluster points](https://en.wikipedia.org/wiki/Limit_point)
(also known as limit points and accumulation points) of a filter and of a sequence.

A filter `F` on `X` has `x` as a cluster point if `ClusterPt x F : 𝓝 x ⊓ F ≠ ⊥`. A map `f : α → X`
clusters at `x` along `F : Filter α` if `MapClusterPt x F f : ClusterPt x (map f F)`.
In particular the notion of cluster point of a sequence `u` is `MapClusterPt x atTop u`.
-/

public section

open Set Filter Topology

universe u v w

variable {X : Type u} [TopologicalSpace X] {Y : Type v} {ι : Sort w} {α β : Type*}
  {x : X} {s s₁ s₂ t : Set X}

@[simp]
/-
**ClusterPt.top** 是 Mathlib 中的一个定理，位于命名空间 `ClusterPt`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {x : X}, ClusterPt x ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
-/
protected lemma ClusterPt.top : ClusterPt x ⊤ := by simp [ClusterPt]
/-
**clusterPt_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：clusterPt_sup {F G : Filter X} : ClusterPt x (F ⊔ G) ↔ ClusterPt x F ∨ Clu
sterPt x G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem clusterPt_sup {F G : Filter X} : ClusterPt x (F ⊔ G) ↔ ClusterPt x F ∨ ClusterPt x G := by
  simp only [ClusterPt, inf_sup_left, sup_neBot]
/-
**ClusterPt.neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ClusterPt.neBot {F : Filter X} (h : ClusterPt x F) : NeBot (𝓝 x ⊓ F)
参数：h : ClusterPt x F。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ClusterPt.neBot {F : Filter X} (h : ClusterPt x F) : NeBot (𝓝 x ⊓ F) :=
  h
/-
**Filter.HasBasis.clusterPt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.clusterPt_iff {ιX ιF} {pX : ιX -> Prop} {sX : ιX -> Set X}
 {pF : ιF -> Prop} {sF : ιF -> Set X} {F : Filter X} (hX : (𝓝 x).HasBasis pX sX)
 (hF : F.HasBasis pF sF) : ClusterPt x F ↔ forall ⦃i⦄, pX i -> forall ⦃j⦄, pF j 
-> (sX i inter sF j).Nonempty
参数：hX : (𝓝 x).HasBasis pX sX；hF : F.HasBasis pF sF。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.inf_basis_neBot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι'
 : Sort u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}  
 {s' : ι' → Set α},   l.H…
-/
theorem Filter.HasBasis.clusterPt_iff {ιX ιF} {pX : ιX → Prop} {sX : ιX → Set X} {pF : ιF → Prop}
    {sF : ιF → Set X} {F : Filter X} (hX : (𝓝 x).HasBasis pX sX) (hF : F.HasBasis pF sF) :
    ClusterPt x F ↔ ∀ ⦃i⦄, pX i → ∀ ⦃j⦄, pF j → (sX i ∩ sF j).Nonempty :=
  hX.inf_basis_neBot_iff hF
/-
**Filter.HasBasis.clusterPt_iff_frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.clusterPt_iff_frequently {ι} {p : ι -> Prop} {s : ι -> Set
 X} {F : Filter X} (hx : (𝓝 x).HasBasis p s) : ClusterPt x F ↔ forall i, p i -> 
existsᶠ x in F, x in s i
参数：hx : (𝓝 x).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.clusterPt_iff`：Filter.HasBasis.clusterPt_iff {ιX ιF} {pX
 : ιX -> Prop} {sX : ιX -> Set X} {pF : ιF -> Prop} {sF : ιF -> Set X} {F : Filt
er X} (hX : (𝓝 x).H…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Filter.HasBasis.clusterPt_iff_frequently {ι} {p : ι → Prop} {s : ι → Set X} {F : Filter X}
    (hx : (𝓝 x).HasBasis p s) : ClusterPt x F ↔ ∀ i, p i → ∃ᶠ x in F, x ∈ s i := by
  simp only [hx.clusterPt_iff F.basis_sets, Filter.frequently_iff, inter_comm (s _),
    Set.Nonempty, id, mem_inter_iff]
/-
**clusterPt_iff_frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：clusterPt_iff_frequently {F : Filter X} : ClusterPt x F ↔ forall s in 𝓝 x,
 existsᶠ y in F, y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.clusterPt_iff_frequently`：Filter.HasBasis.clusterPt_iff_
frequently {ι} {p : ι -> Prop} {s : ι -> Set X} {F : Filter X} (hx : (𝓝 x).HasBa
sis p s) : ClusterPt x F ↔ for…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem clusterPt_iff_frequently {F : Filter X} : ClusterPt x F ↔ ∀ s ∈ 𝓝 x, ∃ᶠ y in F, y ∈ s :=
  (𝓝 x).basis_sets.clusterPt_iff_frequently
/-
**ClusterPt.frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ClusterPt.frequently {F : Filter X} {p : X -> Prop} (hx : ClusterPt x F) (
hp : forallᶠ y in 𝓝 x, p y) : existsᶠ y in F, p y
参数：hx : ClusterPt x F；hp : forallᶠ y in 𝓝 x, p y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `clusterPt_iff_frequently`：clusterPt_iff_frequently {F : Filter X} : Clus
terPt x F ↔ forall s in 𝓝 x, existsᶠ y in F, y in s
-/
theorem ClusterPt.frequently {F : Filter X} {p : X → Prop} (hx : ClusterPt x F)
    (hp : ∀ᶠ y in 𝓝 x, p y) : ∃ᶠ y in F, p y :=
  clusterPt_iff_frequently.mp hx {y | p y} hp
/-
**Filter.HasBasis.clusterPt_iff_frequently'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.clusterPt_iff_frequently' {ι} {p : ι -> Prop} {s : ι -> Se
t X} {F : Filter X} (hx : F.HasBasis p s) : ClusterPt x F ↔ forall i, p i -> exi
stsᶠ x in 𝓝 x, x in s i
参数：hx : F.HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.clusterPt_iff`：Filter.HasBasis.clusterPt_iff {ιX ιF} {pX
 : ιX -> Prop} {sX : ιX -> Set X} {pF : ιF -> Prop} {sF : ιF -> Set X} {F : Filt
er X} (hX : (𝓝 x).H…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem Filter.HasBasis.clusterPt_iff_frequently' {ι} {p : ι → Prop} {s : ι → Set X} {F : Filter X}
    (hx : F.HasBasis p s) : ClusterPt x F ↔ ∀ i, p i → ∃ᶠ x in 𝓝 x, x ∈ s i := by
  simp only [(𝓝 x).basis_sets.clusterPt_iff hx, Filter.frequently_iff]
  exact ⟨fun h a b c d ↦ h d b, fun h a b c d ↦ h c d b⟩
/-
**clusterPt_iff_frequently'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：clusterPt_iff_frequently' {F : Filter X} : ClusterPt x F ↔ forall s in F, 
existsᶠ y in 𝓝 x, y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.clusterPt_iff_frequently'`：Filter.HasBasis.clusterPt_iff
_frequently' {ι} {p : ι -> Prop} {s : ι -> Set X} {F : Filter X} (hx : F.HasBasi
s p s) : ClusterPt x F ↔ forall…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem clusterPt_iff_frequently' {F : Filter X} : ClusterPt x F ↔ ∀ s ∈ F, ∃ᶠ y in 𝓝 x, y ∈ s :=
  F.basis_sets.clusterPt_iff_frequently'
/-
**ClusterPt.frequently'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ClusterPt.frequently' {F : Filter X} {p : X -> Prop} (hx : ClusterPt x F) 
(hp : forallᶠ y in F, p y) : existsᶠ y in 𝓝 x, p y
参数：hx : ClusterPt x F；hp : forallᶠ y in F, p y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `clusterPt_iff_frequently'`：clusterPt_iff_frequently' {F : Filter X} : Cl
usterPt x F ↔ forall s in F, existsᶠ y in 𝓝 x, y in s
-/
theorem ClusterPt.frequently' {F : Filter X} {p : X → Prop} (hx : ClusterPt x F)
    (hp : ∀ᶠ y in F, p y) : ∃ᶠ y in 𝓝 x, p y :=
  clusterPt_iff_frequently'.mp hx {y | p y} hp
/-
**clusterPt_iff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：clusterPt_iff_nonempty {F : Filter X} : ClusterPt x F ↔ forall ⦃U : Set X⦄
, U in 𝓝 x -> forall ⦃V⦄, V in F -> (U inter V).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inf_neBot_iff`：inf_neBot_iff : NeBot (l ⊓ l') ↔ forall ⦃s : Set α
⦄, s in l -> forall ⦃s'⦄, s' in l' -> (s inter s').Nonempty
-/
theorem clusterPt_iff_nonempty {F : Filter X} :
    ClusterPt x F ↔ ∀ ⦃U : Set X⦄, U ∈ 𝓝 x → ∀ ⦃V⦄, V ∈ F → (U ∩ V).Nonempty :=
  inf_neBot_iff
/-
**clusterPt_iff_not_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：clusterPt_iff_not_disjoint {F : Filter X} : ClusterPt x F ↔ ¬Disjoint (𝓝 x
) F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `ClusterPt.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (F 
: Filter X), ClusterPt x F = (nhds x ⊓ F).NeBot
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem clusterPt_iff_not_disjoint {F : Filter X} :
    ClusterPt x F ↔ ¬Disjoint (𝓝 x) F := by
  rw [disjoint_iff, ClusterPt, neBot_iff]
/-
**Filter.HasBasis.clusterPt_iff_forall_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Fi
lter.HasBasis`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {x : X} {ι : Sort u_3} {p : ι →
 Prop} {s : ι → Set X} {F : Filter X},   F.HasBasis p s → (ClusterPt x F ↔ ∀ (i 
: ι), p i → x ∈ closure (s i))
参数：ClusterPt x F ↔ ∀ (i : ι), p i → x ∈ closure (s i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.clusterPt_iff`：Filter.HasBasis.clusterPt_iff {ιX ιF} {pX
 : ιX -> Prop} {sX : ιX -> Set X} {pF : ιF -> Prop} {sF : ιF -> Set X} {F : Filt
er X} (hX : (𝓝 x).H…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
protected theorem Filter.HasBasis.clusterPt_iff_forall_mem_closure {ι} {p : ι → Prop}
    {s : ι → Set X} {F : Filter X} (hF : F.HasBasis p s) :
    ClusterPt x F ↔ ∀ i, p i → x ∈ closure (s i) := by
  simp only [(nhds_basis_opens _).clusterPt_iff hF, mem_closure_iff]
  tauto
/-
**clusterPt_iff_forall_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：clusterPt_iff_forall_mem_closure {F : Filter X} : ClusterPt x F ↔ forall s
 in F, x in closure s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.clusterPt_iff_forall_mem_closure`：∀ {X : Type u} [inst :
 TopologicalSpace X] {x : X} {ι : Sort u_3} {p : ι → Prop} {s : ι → Set X} {F : 
Filter X},   F.HasBasis p s → (Cluster…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem clusterPt_iff_forall_mem_closure {F : Filter X} :
    ClusterPt x F ↔ ∀ s ∈ F, x ∈ closure s :=
  F.basis_sets.clusterPt_iff_forall_mem_closure

alias ⟨ClusterPt.mem_closure_of_mem, _⟩ := clusterPt_iff_forall_mem_closure

/-- `x` is a cluster point of a set `s` if every neighbourhood of `x` meets `s` on a nonempty
set. See also `mem_closure_iff_clusterPt`. -/
/-
**clusterPt_principal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：clusterPt_principal_iff : ClusterPt x (𝓟 s) ↔ forall U in 𝓝 x, (U inter s)
.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inf_principal_neBot_iff`：inf_principal_neBot_iff {s : Set α} : Ne
Bot (l ⊓ 𝓟 s) ↔ forall U in l, (U inter s).Nonempty

--- 原说明 ---
`x` is a cluster point of a set `s` if every neighbourhood of `x` meets `s` on a
 nonempty
set. See also `mem_closure_iff_clusterPt`.
-/
theorem clusterPt_principal_iff :
    ClusterPt x (𝓟 s) ↔ ∀ U ∈ 𝓝 x, (U ∩ s).Nonempty :=
  inf_principal_neBot_iff
/-
**clusterPt_principal_iff_frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：clusterPt_principal_iff_frequently : ClusterPt x (𝓟 s) ↔ existsᶠ y in 𝓝 x,
 y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem clusterPt_principal_iff_frequently :
    ClusterPt x (𝓟 s) ↔ ∃ᶠ y in 𝓝 x, y ∈ s := by
  simp only [clusterPt_principal_iff, frequently_iff, Set.Nonempty, mem_inter_iff]
/-
**ClusterPt.of_le_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ClusterPt.of_le_nhds {f : Filter X} (H : f <= 𝓝 x) [NeBot f] : ClusterPt x
 f
参数：H : f <= 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClusterPt.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (F 
: Filter X), ClusterPt x F = (nhds x ⊓ F).NeBot
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
-/
theorem ClusterPt.of_le_nhds {f : Filter X} (H : f ≤ 𝓝 x) [NeBot f] : ClusterPt x f := by
  rwa [ClusterPt, inf_eq_right.mpr H]
/-
**ClusterPt.of_le_nhds'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ClusterPt.of_le_nhds' {f : Filter X} (H : f <= 𝓝 x) (_hf : NeBot f) : Clus
terPt x f
参数：H : f <= 𝓝 x；_hf : NeBot f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.of_le_nhds`：ClusterPt.of_le_nhds {f : Filter X} (H : f <= 𝓝 x)
 [NeBot f] : ClusterPt x f
-/
theorem ClusterPt.of_le_nhds' {f : Filter X} (H : f ≤ 𝓝 x) (_hf : NeBot f) :
    ClusterPt x f :=
  ClusterPt.of_le_nhds H
/-
**ClusterPt.of_nhds_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ClusterPt.of_nhds_le {f : Filter X} (H : 𝓝 x <= f) : ClusterPt x f
参数：H : 𝓝 x <= f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
-/
theorem ClusterPt.of_nhds_le {f : Filter X} (H : 𝓝 x ≤ f) : ClusterPt x f := by
  simp only [ClusterPt, inf_eq_left.mpr H, nhds_neBot]
/-
**ClusterPt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h : f <= g) : Cluster
Pt x g
参数：H : ClusterPt x f；h : f <= g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
-/
theorem ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h : f ≤ g) : ClusterPt x g :=
  NeBot.mono H <| inf_le_inf_left _ h
/-
**ClusterPt.of_inf_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ClusterPt.of_inf_left {f g : Filter X} (H : ClusterPt x <| f ⊓ g) : Cluste
rPt x f
参数：H : ClusterPt x <| f ⊓ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem ClusterPt.of_inf_left {f g : Filter X} (H : ClusterPt x <| f ⊓ g) : ClusterPt x f :=
  H.mono inf_le_left
/-
**ClusterPt.of_inf_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ClusterPt.of_inf_right {f g : Filter X} (H : ClusterPt x <| f ⊓ g) : Clust
erPt x g
参数：H : ClusterPt x <| f ⊓ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem ClusterPt.of_inf_right {f g : Filter X} (H : ClusterPt x <| f ⊓ g) :
    ClusterPt x g :=
  H.mono inf_le_right

section MapClusterPt

variable {F : Filter α} {u : α → X} {x : X}

/-
**mapClusterPt_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapClusterPt_def : MapClusterPt x F u ↔ ClusterPt x (map u F)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mapClusterPt_def : MapClusterPt x F u ↔ ClusterPt x (map u F) := Iff.rfl
alias ⟨MapClusterPt.clusterPt, _⟩ := mapClusterPt_def
/-
**Filter.EventuallyEq.mapClusterPt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.mapClusterPt_iff {v : α -> X} (h : u =ᶠ[F] v) : MapClu
sterPt x F u ↔ MapClusterPt x F v
参数：h : u =ᶠ[F] v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_congr`：map_congr {m₁ m₂ : α -> β} {f : Filter α} (h : m₁ =ᶠ[f
] m₂) : map m₁ f = map m₂ f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Filter.EventuallyEq.mapClusterPt_iff {v : α → X} (h : u =ᶠ[F] v) :
    MapClusterPt x F u ↔ MapClusterPt x F v := by
  simp only [mapClusterPt_def, map_congr h]

alias ⟨MapClusterPt.congrFun, _⟩ := Filter.EventuallyEq.mapClusterPt_iff
/-
**MapClusterPt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MapClusterPt.mono {G : Filter α} (h : MapClusterPt x F u) (hle : F <= G) :
 MapClusterPt x G u
参数：h : MapClusterPt x F u；hle : F <= G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `MapClusterPt.clusterPt`：∀ {X : Type u} [inst : TopologicalSpace X] {α : 
Type u_1} {F : Filter α} {u : α → X} {x : X},   MapClusterPt x F u → ClusterPt x
 (Filter.map…
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem MapClusterPt.mono {G : Filter α} (h : MapClusterPt x F u) (hle : F ≤ G) :
    MapClusterPt x G u :=
  h.clusterPt.mono (map_mono hle)
/-
**MapClusterPt.tendsto_comp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MapClusterPt.tendsto_comp' [TopologicalSpace Y] {f : X -> Y} {y : Y} (hf :
 Tendsto f (𝓝 x ⊓ map u F) (𝓝 y)) (hu : MapClusterPt x F u) : MapClusterPt y F (
f ∘ u)
参数：hf : Tendsto f (𝓝 x ⊓ map u F) (𝓝 y)；hu : MapClusterPt x F u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.neBot`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x : F
ilter α} {y : Filter β},   Filter.Tendsto f x y → ∀ [hx : x.NeBot], y.NeBot
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem MapClusterPt.tendsto_comp' [TopologicalSpace Y] {f : X → Y} {y : Y}
    (hf : Tendsto f (𝓝 x ⊓ map u F) (𝓝 y)) (hu : MapClusterPt x F u) : MapClusterPt y F (f ∘ u) :=
  (tendsto_inf.2 ⟨hf, tendsto_map.mono_left inf_le_right⟩).neBot (hx := hu)
/-
**MapClusterPt.tendsto_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MapClusterPt.tendsto_comp [TopologicalSpace Y] {f : X -> Y} {y : Y} (hf : 
Tendsto f (𝓝 x) (𝓝 y)) (hu : MapClusterPt x F u) : MapClusterPt y F (f ∘ u)
参数：hf : Tendsto f (𝓝 x) (𝓝 y)；hu : MapClusterPt x F u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MapClusterPt.tendsto_comp'`：MapClusterPt.tendsto_comp' [TopologicalSpace
 Y] {f : X -> Y} {y : Y} (hf : Tendsto f (𝓝 x ⊓ map u F) (𝓝 y)) (hu : MapCluster
Pt x F u) : MapC…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem MapClusterPt.tendsto_comp [TopologicalSpace Y] {f : X → Y} {y : Y}
    (hf : Tendsto f (𝓝 x) (𝓝 y)) (hu : MapClusterPt x F u) : MapClusterPt y F (f ∘ u) :=
  hu.tendsto_comp' (hf.mono_left inf_le_left)
/-
**mapClusterPt_id_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapClusterPt_id_iff [TopologicalSpace α] {a : α} : MapClusterPt a F id ↔ C
lusterPt a F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MapClusterPt.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] {ι : Typ
e u_3} (x : X) (F : Filter ι) (u : ι → X),   MapClusterPt x F u = ClusterPt x (F
ilter.m…
· 使用定理 `Filter.map_id`：map_id : Filter.map id f = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mapClusterPt_id_iff [TopologicalSpace α] {a : α} : MapClusterPt a F id ↔ ClusterPt a F := by
  rw [MapClusterPt, map_id]

alias ⟨_, ClusterPt.mapClusterPt_id⟩ := mapClusterPt_id_iff
/-
**MapClusterPt.continuousAt_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MapClusterPt.continuousAt_comp [TopologicalSpace Y] {f : X -> Y} (hf : Con
tinuousAt f x) (hu : MapClusterPt x F u) : MapClusterPt (f x) F (f ∘ u)
参数：hf : ContinuousAt f x；hu : MapClusterPt x F u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MapClusterPt.tendsto_comp`：MapClusterPt.tendsto_comp [TopologicalSpace Y
] {f : X -> Y} {y : Y} (hf : Tendsto f (𝓝 x) (𝓝 y)) (hu : MapClusterPt x F u) : 
MapClusterPt y …
-/
theorem MapClusterPt.continuousAt_comp [TopologicalSpace Y] {f : X → Y} (hf : ContinuousAt f x)
    (hu : MapClusterPt x F u) : MapClusterPt (f x) F (f ∘ u) :=
  hu.tendsto_comp hf
/-
**ContinuousAt.mapClusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.mapClusterPt [TopologicalSpace α] {a : α} (hf : ContinuousAt 
u a) (hu : ClusterPt a F) : MapClusterPt (u a) F u
参数：hf : ContinuousAt u a；hu : ClusterPt a F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MapClusterPt.continuousAt_comp`：MapClusterPt.continuousAt_comp [Topologi
calSpace Y] {f : X -> Y} (hf : ContinuousAt f x) (hu : MapClusterPt x F u) : Map
ClusterPt (f x) F (f…
· 使用定理 `ClusterPt.mapClusterPt_id`：∀ {α : Type u_1} {F : Filter α} [inst : Topol
ogicalSpace α] {a : α}, ClusterPt a F → MapClusterPt a F id
-/
theorem ContinuousAt.mapClusterPt [TopologicalSpace α] {a : α} (hf : ContinuousAt u a)
    (hu : ClusterPt a F) : MapClusterPt (u a) F u :=
  hu.mapClusterPt_id.continuousAt_comp hf
/-
**Filter.HasBasis.mapClusterPt_iff_frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.mapClusterPt_iff_frequently {ι : Sort*} {p : ι -> Prop} {s
 : ι -> Set X} (hx : (𝓝 x).HasBasis p s) : MapClusterPt x F u ↔ forall i, p i ->
 existsᶠ a in F, u a in s i
参数：hx : (𝓝 x).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.clusterPt_iff_frequently`：Filter.HasBasis.clusterPt_iff_
frequently {ι} {p : ι -> Prop} {s : ι -> Set X} {F : Filter X} (hx : (𝓝 x).HasBa
sis p s) : ClusterPt x F ↔ for…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Filter.HasBasis.mapClusterPt_iff_frequently {ι : Sort*} {p : ι → Prop} {s : ι → Set X}
    (hx : (𝓝 x).HasBasis p s) : MapClusterPt x F u ↔ ∀ i, p i → ∃ᶠ a in F, u a ∈ s i := by
  simp_rw [MapClusterPt, hx.clusterPt_iff_frequently, frequently_map]
/-
**mapClusterPt_iff_frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapClusterPt_iff_frequently : MapClusterPt x F u ↔ forall s in 𝓝 x, exists
ᶠ a in F, u a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mapClusterPt_iff_frequently`：Filter.HasBasis.mapClusterP
t_iff_frequently {ι : Sort*} {p : ι -> Prop} {s : ι -> Set X} (hx : (𝓝 x).HasBas
is p s) : MapClusterPt x F u ↔ fo…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem mapClusterPt_iff_frequently : MapClusterPt x F u ↔ ∀ s ∈ 𝓝 x, ∃ᶠ a in F, u a ∈ s :=
  (𝓝 x).basis_sets.mapClusterPt_iff_frequently
/-
**MapClusterPt.frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MapClusterPt.frequently (h : MapClusterPt x F u) {p : X -> Prop} (hp : for
allᶠ y in 𝓝 x, p y) : existsᶠ a in F, p (u a)
参数：h : MapClusterPt x F u；hp : forallᶠ y in 𝓝 x, p y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.frequently`：ClusterPt.frequently {F : Filter X} {p : X -> Prop
} (hx : ClusterPt x F) (hp : forallᶠ y in 𝓝 x, p y) : existsᶠ y in F, p y
· 使用定理 `MapClusterPt.clusterPt`：∀ {X : Type u} [inst : TopologicalSpace X] {α : 
Type u_1} {F : Filter α} {u : α → X} {x : X},   MapClusterPt x F u → ClusterPt x
 (Filter.map…
-/
theorem MapClusterPt.frequently (h : MapClusterPt x F u) {p : X → Prop} (hp : ∀ᶠ y in 𝓝 x, p y) :
    ∃ᶠ a in F, p (u a) :=
  h.clusterPt.frequently hp
/-
**mapClusterPt_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapClusterPt_comp {φ : α -> β} {u : β -> X} : MapClusterPt x F (u ∘ φ) ↔ M
apClusterPt x (map φ F) u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mapClusterPt_comp {φ : α → β} {u : β → X} :
    MapClusterPt x F (u ∘ φ) ↔ MapClusterPt x (map φ F) u := Iff.rfl
/-
**Filter.Tendsto.mapClusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.mapClusterPt [NeBot F] (h : Tendsto u F (𝓝 x)) : MapCluster
Pt x F u
参数：h : Tendsto u F (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.of_le_nhds`：ClusterPt.of_le_nhds {f : Filter X} (H : f <= 𝓝 x)
 [NeBot f] : ClusterPt x f
-/
theorem Filter.Tendsto.mapClusterPt [NeBot F] (h : Tendsto u F (𝓝 x)) : MapClusterPt x F u :=
  .of_le_nhds h
/-
**MapClusterPt.of_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MapClusterPt.of_comp {φ : β -> α} {p : Filter β} (h : Tendsto φ p F) (H : 
MapClusterPt x p (u ∘ φ)) : MapClusterPt x F u
参数：h : Tendsto φ p F；H : MapClusterPt x p (u ∘ φ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `MapClusterPt.clusterPt`：∀ {X : Type u} [inst : TopologicalSpace X] {α : 
Type u_1} {F : Filter α} {u : α → X} {x : X},   MapClusterPt x F u → ClusterPt x
 (Filter.map…
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem MapClusterPt.of_comp {φ : β → α} {p : Filter β} (h : Tendsto φ p F)
    (H : MapClusterPt x p (u ∘ φ)) : MapClusterPt x F u :=
  H.clusterPt.mono <| map_mono h
/-
**IsClosed.mem_of_mapClusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.mem_of_mapClusterPt {l : X} {s : Set X} {f : α -> X} {b : Filter 
α} (hs : IsClosed s) (hf : MapClusterPt l b f) (h : forallᶠ (x : α) in b, f x in
 s) : l in s
参数：hs : IsClosed s；hf : MapClusterPt l b f；h : forallᶠ (x : α) in b, f x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.mem_of_closed`：Filter.Frequently.mem_of_closed (h : ex
istsᶠ x in 𝓝 x, x in s) (hs : IsClosed s) : x in s
· 使用定理 `ClusterPt.frequently'`：ClusterPt.frequently' {F : Filter X} {p : X -> Pr
op} (hx : ClusterPt x F) (hp : forallᶠ y in F, p y) : existsᶠ y in 𝓝 x, p y
-/
theorem IsClosed.mem_of_mapClusterPt {l : X} {s : Set X} {f : α → X} {b : Filter α}
    (hs : IsClosed s) (hf : MapClusterPt l b f) (h : ∀ᶠ (x : α) in b, f x ∈ s) : l ∈ s :=
  (hf.frequently' h).mem_of_closed hs

/-- A point `a` is a cluster point of the sequence `x` if and only if `a` belongs to the closure
of every tail `x '' {n | i ≤ n}`. -/
/-
**mapClusterPt_atTop_iff_forall_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapClusterPt_atTop_iff_forall_mem_closure {ι : Type*} [Preorder ι] [IsDire
ctedOrder ι] [Nonempty ι] {x : ι -> X} {a : X} : MapClusterPt a atTop x ↔ forall
 i, a in closure (x '' Ici i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.clusterPt_iff_forall_mem_closure`：∀ {X : Type u} [inst :
 TopologicalSpace X] {x : X} {ι : Sort u_3} {p : ι → Prop} {s : ι → Set X} {F : 
Filter X},   F.HasBasis p s → (Cluster…
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A point `a` is a cluster point of the sequence `x` if and only if `a` belongs to
 the closure
of every tail `x '' {n | i ≤ n}`.
-/
theorem mapClusterPt_atTop_iff_forall_mem_closure {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {x : ι → X} {a : X} :
    MapClusterPt a atTop x ↔ ∀ i, a ∈ closure (x '' Ici i) := by
  simp [MapClusterPt, (atTop_basis.map x).clusterPt_iff_forall_mem_closure]

end MapClusterPt

/-
**accPt_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：accPt_sup {x : X} {F G : Filter X} : AccPt x (F ⊔ G) ↔ AccPt x F ∨ AccPt x
 G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem accPt_sup {x : X} {F G : Filter X} :
    AccPt x (F ⊔ G) ↔ AccPt x F ∨ AccPt x G := by
  simp only [AccPt, inf_sup_left, sup_neBot]
/-
**accPt_iff_clusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：accPt_iff_clusterPt {x : X} {F : Filter X} : AccPt x F ↔ ClusterPt x (𝓟 {x
}ᶜ ⊓ F)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AccPt.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (F : Fi
lter X), AccPt x F = (nhdsWithin x {x}ᶜ ⊓ F).NeBot
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `ClusterPt.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (F 
: Filter X), ClusterPt x F = (nhds x ⊓ F).NeBot
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem accPt_iff_clusterPt {x : X} {F : Filter X} : AccPt x F ↔ ClusterPt x (𝓟 {x}ᶜ ⊓ F) := by
  rw [AccPt, nhdsWithin, ClusterPt, inf_assoc]

/-- `x` is an accumulation point of a set `C` iff it is a cluster point of `C ∖ {x}`. -/
/-
**accPt_principal_iff_clusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：accPt_principal_iff_clusterPt {x : X} {C : Set X} : AccPt x (𝓟 C) ↔ Cluste
rPt x (𝓟 (C \ { x }))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `accPt_iff_clusterPt`：accPt_iff_clusterPt {x : X} {F : Filter X} : AccPt 
x F ↔ ClusterPt x (𝓟 {x}ᶜ ⊓ F)
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`x` is an accumulation point of a set `C` iff it is a cluster point of `C ∖ {x}`
.
-/
theorem accPt_principal_iff_clusterPt {x : X} {C : Set X} :
    AccPt x (𝓟 C) ↔ ClusterPt x (𝓟 (C \ { x })) := by
  rw [accPt_iff_clusterPt, inf_principal, inter_comm, sdiff_eq]

/-- `x` is an accumulation point of a set `C` iff every neighborhood
of `x` contains a point of `C` other than `x`. -/
/-
**accPt_iff_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：accPt_iff_nhds {x : X} {C : Set X} : AccPt x (𝓟 C) ↔ forall U in 𝓝 x, exis
ts y in U inter C, y != x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`x` is an accumulation point of a set `C` iff every neighborhood
of `x` contains a point of `C` other than `x`.
-/
theorem accPt_iff_nhds {x : X} {C : Set X} : AccPt x (𝓟 C) ↔ ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x := by
  simp [accPt_principal_iff_clusterPt, clusterPt_principal_iff, Set.Nonempty,
    and_assoc]

/-- `x` is an accumulation point of a set `C` iff
there are points near `x` in `C` and different from `x`. -/
/-
**accPt_iff_frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：accPt_iff_frequently {x : X} {C : Set X} : AccPt x (𝓟 C) ↔ existsᶠ y in 𝓝 
x, y != x ∧ y in C
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

--- 原说明 ---
`x` is an accumulation point of a set `C` iff
there are points near `x` in `C` and different from `x`.
-/
theorem accPt_iff_frequently {x : X} {C : Set X} : AccPt x (𝓟 C) ↔ ∃ᶠ y in 𝓝 x, y ≠ x ∧ y ∈ C := by
  simp [accPt_principal_iff_clusterPt, clusterPt_principal_iff_frequently, and_comm]

/--
Variant of `accPt_iff_frequently`: A point `x` is an accumulation point of a set `C` iff points in
punctured neighborhoods are frequently contained in `C`.
-/
/-
**accPt_iff_frequently_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：accPt_iff_frequently_nhdsNE {X : Type*} [TopologicalSpace X] {x : X} {C : 
Set X} : AccPt x (𝓟 C) ↔ existsᶠ (y : X) in 𝓝[!=] x, y in C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.frequently_inf_principal`：frequently_inf_principal {f : Filter α}
 {s : Set α} {p : α -> Prop} : (existsᶠ x in f ⊓ 𝓟 s, p x) ↔ existsᶠ x in f, x i
n s ∧ p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `accPt_iff_frequently`：accPt_iff_frequently {x : X} {C : Set X} : AccPt x
 (𝓟 C) ↔ existsᶠ y in 𝓝 x, y != x ∧ y in C
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.iff_iff_and_or_not_and_not`：∀ {a b : Prop} [Decidable b], (a ↔
 b) ↔ a ∧ b ∨ ¬a ∧ ¬b

--- 原说明 ---
Variant of `accPt_iff_frequently`: A point `x` is an accumulation point of a set
 `C` iff points in
punctured neighborhoods are frequently contained in `C`.
-/
theorem accPt_iff_frequently_nhdsNE {X : Type*} [TopologicalSpace X] {x : X} {C : Set X} :
    AccPt x (𝓟 C) ↔ ∃ᶠ (y : X) in 𝓝[≠] x, y ∈ C := by
  have : (∃ᶠ z in 𝓝[≠] x, z ∈ C) ↔ ∃ᶠ z in 𝓝 x, z ∈ C ∧ z ∈ ({x} : Set X)ᶜ :=
    frequently_inf_principal.trans <| by simp only [and_comm]
  rw [accPt_iff_frequently, this]
  congr! 2
  tauto
/-
**accPt_principal_iff_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：accPt_principal_iff_nhdsWithin : AccPt x (𝓟 s) ↔ (𝓝[s \ {x}] x).NeBot
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `accPt_principal_iff_clusterPt`：accPt_principal_iff_clusterPt {x : X} {C 
: Set X} : AccPt x (𝓟 C) ↔ ClusterPt x (𝓟 (C \ { x }))
· 使用定理 `ClusterPt.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (F 
: Filter X), ClusterPt x F = (nhds x ⊓ F).NeBot
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem accPt_principal_iff_nhdsWithin : AccPt x (𝓟 s) ↔ (𝓝[s \ {x}] x).NeBot := by
  rw [accPt_principal_iff_clusterPt, ClusterPt, nhdsWithin]

/-- If `x` is an accumulation point of `F` and `F ≤ G`, then
`x` is an accumulation point of `G`. -/
/-
**AccPt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AccPt.mono {F G : Filter X} (h : AccPt x F) (hFG : F <= G) : AccPt x G
参数：h : AccPt x F；hFG : F <= G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a

--- 原说明 ---
If `x` is an accumulation point of `F` and `F ≤ G`, then
`x` is an accumulation point of `G`.
-/
theorem AccPt.mono {F G : Filter X} (h : AccPt x F) (hFG : F ≤ G) : AccPt x G :=
  NeBot.mono h (inf_le_inf_left _ hFG)
/-
**AccPt.clusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AccPt.clusterPt {x : X} {F : Filter X} (h : AccPt x F) : ClusterPt x F
参数：h : AccPt x F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `accPt_iff_clusterPt`：accPt_iff_clusterPt {x : X} {F : Filter X} : AccPt 
x F ↔ ClusterPt x (𝓟 {x}ᶜ ⊓ F)
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem AccPt.clusterPt {x : X} {F : Filter X} (h : AccPt x F) : ClusterPt x F :=
  (accPt_iff_clusterPt.mp h).mono inf_le_right
/-
**clusterPt_principal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：clusterPt_principal {x : X} {C : Set X} : ClusterPt x (𝓟 C) ↔ x in C ∨ Acc
Pt x (𝓟 C)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `accPt_principal_iff_clusterPt`：accPt_principal_iff_clusterPt {x : X} {C 
: Set X} : AccPt x (𝓟 C) ↔ ClusterPt x (𝓟 (C \ { x }))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `clusterPt_principal_iff`：clusterPt_principal_iff : ClusterPt x (𝓟 s) ↔ f
orall U in 𝓝 x, (U inter s).Nonempty
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `AccPt.clusterPt`：AccPt.clusterPt {x : X} {F : Filter X} (h : AccPt x F) 
: ClusterPt x F
-/
theorem clusterPt_principal {x : X} {C : Set X} :
    ClusterPt x (𝓟 C) ↔ x ∈ C ∨ AccPt x (𝓟 C) := by
  constructor
  · intro h
    by_contra! hc
    rw [accPt_principal_iff_clusterPt] at hc
    simp_all only [not_false_eq_true, sdiff_singleton_eq_self, not_true_eq_false, hc.1]
  · rintro (h | h)
    · exact clusterPt_principal_iff.mpr fun _ mem ↦ ⟨x, ⟨mem_of_mem_nhds mem, h⟩⟩
    · exact h.clusterPt

/-- The set of cluster points of a filter is closed. In particular, the set of limit points
of a sequence is closed. -/
/-
**isClosed_setOfPred_clusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_setOfPred_clusterPt {f : Filter X} : IsClosed { x | ClusterPt x f
 }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `isClosed_biInter`：isClosed_biInter {s : Set α} {f : α -> Set X} (h : for
all i in s, IsClosed (f i)) : IsClosed (⋂ i in s, f i)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)

--- 原说明 ---
The set of cluster points of a filter is closed. In particular, the set of limit
 points
of a sequence is closed.
-/
theorem isClosed_setOfPred_clusterPt {f : Filter X} : IsClosed { x | ClusterPt x f } := by
  simp only [clusterPt_iff_forall_mem_closure, ofPred_forall]
  exact isClosed_biInter fun _ _ ↦ isClosed_closure

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_clusterPt := isClosed_setOfPred_clusterPt
/-
**mem_closure_iff_clusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_iff_clusterPt : x in closure s ↔ ClusterPt x (𝓟 s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mem_closure_iff_frequently`：mem_closure_iff_frequently : x in closure s 
↔ existsᶠ x in 𝓝 x, x in s
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `clusterPt_principal_iff_frequently`：clusterPt_principal_iff_frequently :
 ClusterPt x (𝓟 s) ↔ existsᶠ y in 𝓝 x, y in s
-/
theorem mem_closure_iff_clusterPt : x ∈ closure s ↔ ClusterPt x (𝓟 s) :=
  mem_closure_iff_frequently.trans clusterPt_principal_iff_frequently.symm

alias ⟨_, ClusterPt.mem_closure⟩ := mem_closure_iff_clusterPt
/-
**mem_closure_iff_nhds_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_iff_nhds_ne_bot : x in closure s ↔ 𝓝 x ⊓ 𝓟 s != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
-/
theorem mem_closure_iff_nhds_ne_bot : x ∈ closure s ↔ 𝓝 x ⊓ 𝓟 s ≠ ⊥ :=
  mem_closure_iff_clusterPt.trans neBot_iff
/-
**mem_closure_iff_nhdsWithin_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_iff_nhdsWithin_neBot : x in closure s ↔ NeBot (𝓝[s] x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
-/
theorem mem_closure_iff_nhdsWithin_neBot : x ∈ closure s ↔ NeBot (𝓝[s] x) :=
  mem_closure_iff_clusterPt
/-
**notMem_closure_iff_nhdsWithin_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：notMem_closure_iff_nhdsWithin_eq_bot : x ∉ closure s ↔ 𝓝[s] x = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `Filter.not_neBot`：not_neBot {f : Filter α} : ¬f.NeBot ↔ f = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma notMem_closure_iff_nhdsWithin_eq_bot : x ∉ closure s ↔ 𝓝[s] x = ⊥ := by
  rw [mem_closure_iff_nhdsWithin_neBot, not_neBot]
/-
**mem_interior_iff_not_clusterPt_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_interior_iff_not_clusterPt_compl : x in interior s ↔ ¬ClusterPt x (𝓟 s
ᶜ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_interior_iff_not_clusterPt_compl : x ∈ interior s ↔ ¬ClusterPt x (𝓟 sᶜ) := by
  rw [← mem_closure_iff_clusterPt, closure_compl, mem_compl_iff, not_not]

/-- If `x` is not an isolated point of a topological space, then `{x}ᶜ` is dense in the whole
space. -/
/-
**dense_compl_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_compl_singleton (x : X) [NeBot (𝓝[!=] x)] : Dense ({x}ᶜ : Set X)
参数：x : X；𝓝[!=] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
If `x` is not an isolated point of a topological space, then `{x}ᶜ` is dense in 
the whole
space.
-/
theorem dense_compl_singleton (x : X) [NeBot (𝓝[≠] x)] : Dense ({x}ᶜ : Set X) := by
  intro y
  rcases eq_or_ne y x with (rfl | hne)
  · rwa [mem_closure_iff_nhdsWithin_neBot]
  · exact subset_closure hne

/-- If `x` is not an isolated point of a topological space, then the closure of `{x}ᶜ` is the whole
space. -/
/-
**closure_compl_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_compl_singleton (x : X) [NeBot (𝓝[!=] x)] : closure {x}ᶜ = (univ :
 Set X)
参数：x : X；𝓝[!=] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `dense_compl_singleton`：dense_compl_singleton (x : X) [NeBot (𝓝[!=] x)] :
 Dense ({x}ᶜ : Set X)

--- 原说明 ---
If `x` is not an isolated point of a topological space, then the closure of `{x}
ᶜ` is the whole
space.
-/
theorem closure_compl_singleton (x : X) [NeBot (𝓝[≠] x)] : closure {x}ᶜ = (univ : Set X) :=
  (dense_compl_singleton x).closure_eq

/-- If `x` is not an isolated point of a topological space, then the interior of `{x}` is empty. -/
@[simp]
/-
**interior_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_singleton (x : X) [NeBot (𝓝[!=] x)] : interior {x} = (∅ : Set X)
参数：x : X；𝓝[!=] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `interior_eq_empty_iff_dense_compl`：interior_eq_empty_iff_dense_compl : i
nterior s = ∅ ↔ Dense sᶜ
· 使用定理 `dense_compl_singleton`：dense_compl_singleton (x : X) [NeBot (𝓝[!=] x)] :
 Dense ({x}ᶜ : Set X)

--- 原说明 ---
If `x` is not an isolated point of a topological space, then the interior of `{x
}` is empty.
-/
theorem interior_singleton (x : X) [NeBot (𝓝[≠] x)] : interior {x} = (∅ : Set X) :=
  interior_eq_empty_iff_dense_compl.2 (dense_compl_singleton x)
/-
**not_isOpen_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isOpen_singleton (x : X) [NeBot (𝓝[!=] x)] : ¬IsOpen ({x} : Set X)
参数：x : X；𝓝[!=] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `dense_compl_singleton_iff_not_open`：dense_compl_singleton_iff_not_open :
 Dense ({x}ᶜ : Set X) ↔ ¬IsOpen ({x} : Set X)
· 使用定理 `dense_compl_singleton`：dense_compl_singleton (x : X) [NeBot (𝓝[!=] x)] :
 Dense ({x}ᶜ : Set X)
-/
theorem not_isOpen_singleton (x : X) [NeBot (𝓝[≠] x)] : ¬IsOpen ({x} : Set X) :=
  dense_compl_singleton_iff_not_open.1 (dense_compl_singleton x)
/-
**closure_eq_cluster_pts** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_eq_cluster_pts : closure s = { a | ClusterPt a (𝓟 s) }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
-/
theorem closure_eq_cluster_pts : closure s = { a | ClusterPt a (𝓟 s) } :=
  Set.ext fun _ => mem_closure_iff_clusterPt
/-
**mem_closure_iff_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_iff_nhds : x in closure s ↔ forall t in 𝓝 x, (t inter s).Nonem
pty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
· 使用定理 `clusterPt_principal_iff`：clusterPt_principal_iff : ClusterPt x (𝓟 s) ↔ f
orall U in 𝓝 x, (U inter s).Nonempty
-/
theorem mem_closure_iff_nhds : x ∈ closure s ↔ ∀ t ∈ 𝓝 x, (t ∩ s).Nonempty :=
  mem_closure_iff_clusterPt.trans clusterPt_principal_iff
/-
**mem_closure_iff_nhds'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_iff_nhds' : x in closure s ↔ forall t in 𝓝 x, exists y : s, ↑y
 in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_closure_iff_nhds' : x ∈ closure s ↔ ∀ t ∈ 𝓝 x, ∃ y : s, ↑y ∈ t := by
  simp only [mem_closure_iff_nhds, Set.inter_nonempty_iff_exists_right, SetCoe.exists, exists_prop]
/-
**mem_closure_iff_comap_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_iff_comap_neBot : x in closure s ↔ NeBot (comap ((↑) : s -> X)
 (𝓝 x))
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_closure_iff_comap_neBot :
    x ∈ closure s ↔ NeBot (comap ((↑) : s → X) (𝓝 x)) := by
  simp_rw [mem_closure_iff_nhds, comap_neBot_iff, Set.inter_nonempty_iff_exists_right,
    SetCoe.exists, exists_prop]
/-
**mem_closure_iff_nhds_basis'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_iff_nhds_basis' {p : ι -> Prop} {s : ι -> Set X} (h : (𝓝 x).Ha
sBasis p s) : x in closure t ↔ forall i, p i -> (s i inter t).Nonempty
参数：h : (𝓝 x).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
· 使用定理 `Filter.HasBasis.clusterPt_iff`：Filter.HasBasis.clusterPt_iff {ιX ιF} {pX
 : ιX -> Prop} {sX : ιX -> Set X} {pF : ιF -> Prop} {sF : ιF -> Set X} {F : Filt
er X} (hX : (𝓝 x).H…
· 使用定理 `Filter.hasBasis_principal`：hasBasis_principal (t : Set α) : (𝓟 t).HasBas
is (fun _ : Unit => True) fun _ => t
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_closure_iff_nhds_basis' {p : ι → Prop} {s : ι → Set X} (h : (𝓝 x).HasBasis p s) :
    x ∈ closure t ↔ ∀ i, p i → (s i ∩ t).Nonempty :=
  mem_closure_iff_clusterPt.trans <|
    (h.clusterPt_iff (hasBasis_principal _)).trans <| by simp only [forall_const]
/-
**mem_closure_iff_nhds_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_iff_nhds_basis {p : ι -> Prop} {s : ι -> Set X} (h : (𝓝 x).Has
Basis p s) : x in closure t ↔ forall i, p i -> exists y in t, y in s i
参数：h : (𝓝 x).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mem_closure_iff_nhds_basis'`：mem_closure_iff_nhds_basis' {p : ι -> Prop}
 {s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : x in closure t ↔ forall i, p i -> (
s i inter t).None…
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_closure_iff_nhds_basis {p : ι → Prop} {s : ι → Set X} (h : (𝓝 x).HasBasis p s) :
    x ∈ closure t ↔ ∀ i, p i → ∃ y ∈ t, y ∈ s i :=
  (mem_closure_iff_nhds_basis' h).trans <| by
    simp only [Set.Nonempty, mem_inter_iff, and_comm]
/-
**clusterPt_iff_lift'_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {x : X} {F : Filter X}, Cluster
Pt x F ↔ pure x ≤ F.lift' closure
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Filter.hasBasis_pure`：hasBasis_pure (x : α) : (pure x : Filter α).HasBas
is (fun _ : Unit => True) fun _ => {x}
· 使用定理 `Filter.HasBasis.lift'_closure`：∀ {X : Type u} [inst : TopologicalSpace X
] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBasis p s →
 (l.lift' closure).…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem clusterPt_iff_lift'_closure {F : Filter X} :
    ClusterPt x F ↔ pure x ≤ (F.lift' closure) := by
  simp_rw [clusterPt_iff_forall_mem_closure,
    (hasBasis_pure _).le_basis_iff F.basis_sets.lift'_closure, id, singleton_subset_iff, true_and,
    exists_const]
/-
**clusterPt_iff_lift'_closure'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {x : X} {F : Filter X}, Cluster
Pt x F ↔ (F.lift' closure ⊓ pure x).NeBot
参数：F.lift' closure ⊓ pure x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `clusterPt_iff_lift'_closure`：∀ {X : Type u} [inst : TopologicalSpace X] 
{x : X} {F : Filter X}, ClusterPt x F ↔ pure x ≤ F.lift' closure
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem clusterPt_iff_lift'_closure' {F : Filter X} :
    ClusterPt x F ↔ (F.lift' closure ⊓ pure x).NeBot := by
  rw [clusterPt_iff_lift'_closure, inf_comm]
  constructor
  · intro h
    simp [h, pure_neBot]
  · intro h U hU
    simp_rw [← forall_mem_nonempty_iff_neBot, mem_inf_iff] at h
    simpa using h ({x} ∩ U) ⟨{x}, by simp, U, hU, rfl⟩

@[simp]
/-
**clusterPt_lift'_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {x : X} {F : Filter X}, Cluster
Pt x (F.lift' closure) ↔ ClusterPt x F
参数：F.lift' closure。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.lift'_lift'_assoc`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3}
 {f : Filter α} {g : Set α → Set β} {h : Set β → Set γ},   Monotone g → Monotone
 h → (f.lift' …
· 使用定理 `monotone_closure`：monotone_closure (X : Type*) [TopologicalSpace X] : Mo
notone (@closure X _)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem clusterPt_lift'_closure_iff {F : Filter X} :
    ClusterPt x (F.lift' closure) ↔ ClusterPt x F := by
  simp [clusterPt_iff_lift'_closure, lift'_lift'_assoc (monotone_closure X) (monotone_closure X)]
/-
**isClosed_iff_clusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_iff_clusterPt : IsClosed s ↔ forall a, ClusterPt a (𝓟 s) -> a in 
s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `closure_subset_iff_isClosed`：closure_subset_iff_isClosed : closure s sub
seteq s ↔ IsClosed s
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
theorem isClosed_iff_clusterPt : IsClosed s ↔ ∀ a, ClusterPt a (𝓟 s) → a ∈ s :=
  calc
    IsClosed s ↔ closure s ⊆ s := closure_subset_iff_isClosed.symm
    _ ↔ ∀ a, ClusterPt a (𝓟 s) → a ∈ s := by simp only [subset_def, mem_closure_iff_clusterPt]
/-
**isClosed_iff_accPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_iff_accPt : IsClosed s ↔ forall a, AccPt a (𝓟 s) -> a in s
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
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosed_iff_accPt : IsClosed s ↔ ∀ a, AccPt a (𝓟 s) → a ∈ s := by
  simp [isClosed_iff_clusterPt, clusterPt_principal, or_imp]
/-
**isClosed_iff_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_iff_nhds : IsClosed s ↔ forall x, (forall U in 𝓝 x, (U inter s).N
onempty) -> x in s
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
theorem isClosed_iff_nhds :
    IsClosed s ↔ ∀ x, (∀ U ∈ 𝓝 x, (U ∩ s).Nonempty) → x ∈ s := by
  simp_rw [isClosed_iff_clusterPt, ClusterPt, inf_principal_neBot_iff]
/-
**isClosed_iff_forall_filter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_iff_forall_filter : IsClosed s ↔ forall x, forall F : Filter X, F
.NeBot -> F <= 𝓟 s -> F <= 𝓝 x -> x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
lemma isClosed_iff_forall_filter :
    IsClosed s ↔ ∀ x, ∀ F : Filter X, F.NeBot → F ≤ 𝓟 s → F ≤ 𝓝 x → x ∈ s := by
  simp_rw [isClosed_iff_clusterPt]
  exact ⟨fun hs x F F_ne FS Fx ↦ hs _ <| NeBot.mono F_ne (le_inf Fx FS),
         fun hs x hx ↦ hs x (𝓝 x ⊓ 𝓟 s) hx inf_le_right inf_le_left⟩
/-
**mem_closure_of_mem_closure_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_of_mem_closure_union (h : x in closure (s₁ union s₂)) (h₁ : s₁
ᶜ in 𝓝 x) : x in closure s₂
参数：h : x in closure (s₁ union s₂)；h₁ : s₁ᶜ in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_nhds_ne_bot`：mem_closure_iff_nhds_ne_bot : x in closure 
s ↔ 𝓝 x ⊓ 𝓟 s != ⊥
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.inf_principal_eq_bot`：inf_principal_eq_bot {f : Filter α} {s : Se
t α} : f ⊓ 𝓟 s = ⊥ ↔ sᶜ in f
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.sup_principal`：sup_principal {s t : Set α} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s uni
on t)
-/
theorem mem_closure_of_mem_closure_union (h : x ∈ closure (s₁ ∪ s₂))
    (h₁ : s₁ᶜ ∈ 𝓝 x) : x ∈ closure s₂ := by
  rw [mem_closure_iff_nhds_ne_bot] at *
  rwa [← sup_principal, inf_sup_left, inf_principal_eq_bot.mpr h₁, bot_sup_eq] at h
