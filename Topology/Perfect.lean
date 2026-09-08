/-
Copyright (c) 2022 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
module

public import Mathlib.Topology.Separation.Regular

/-!
# Perfect Sets

In this file we define perfect subsets of a topological space, and prove some basic properties,
including a version of the Cantor-Bendixson Theorem.

## Main Definitions

* `Preperfect C`: A set `C` is preperfect if every point of `C` is an accumulation point
  of `C`. Equivalently, if it has no isolated points in the induced topology.
  This property is also called dense-in-itself.
* `Perfect C`: A set `C` is perfect, meaning it is closed and every point of it
  is an accumulation point of itself.
* `PerfectSpace X`: A topological space `X` is perfect if its universe is a perfect set.

## Main Statements

* `preperfect_iff_perfect_closure`: In a T1 space, a set is preperfect iff its closure is perfect.
* `Perfect.splitting`: A perfect nonempty set contains two disjoint perfect nonempty subsets.
  The main inductive step in the construction of an embedding from the Cantor space to a
  perfect nonempty complete metric space.
* `exists_countable_union_perfect_of_isClosed`: One version of the **Cantor-Bendixson Theorem**:
  A closed set in a second countable space can be written as the union of a countable set and a
  perfect set.

## Implementation Notes

We do not require perfect sets to be nonempty.

## See also

`Mathlib/Topology/MetricSpace/Perfect.lean`, for properties of perfect sets in metric spaces,
namely Polish spaces.

## References

* [kechris1995] (Chapters 6-7)

## Tags

accumulation point, perfect set, dense-in-itself, cantor-bendixson.

-/

@[expose] public section


open Topology Filter Set TopologicalSpace

section Basic

variable {α : Type*} [TopologicalSpace α] {C : Set α}

/-- If `x` is an accumulation point of a set `C` and `U` is a neighborhood of `x`,
then `x` is an accumulation point of `U ∩ C`. -/
/-
**AccPt.nhds_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AccPt.nhds_inter {x : α} {U : Set α} (h_acc : AccPt x (𝓟 C)) (hU : U in 𝓝 
x) : AccPt x (𝓟 (U inter C))
参数：h_acc : AccPt x (𝓟 C)；hU : U in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `AccPt.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (F : Fi
lter X), AccPt x F = (nhdsWithin x {x}ᶜ ⊓ F).NeBot
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a

--- 原说明 ---
If `x` is an accumulation point of a set `C` and `U` is a neighborhood of `x`,
then `x` is an accumulation point of `U ∩ C`.
-/
theorem AccPt.nhds_inter {x : α} {U : Set α} (h_acc : AccPt x (𝓟 C)) (hU : U ∈ 𝓝 x) :
    AccPt x (𝓟 (U ∩ C)) := by
  have : 𝓝[≠] x ≤ 𝓟 U := by
    rw [le_principal_iff]
    exact mem_nhdsWithin_of_mem_nhds hU
  rw [AccPt, ← inf_principal, ← inf_assoc, inf_of_le_left this]
  exact h_acc

/-- A set `C` is preperfect if all of its points are accumulation points of itself.
If `α` is a T1 space, this is equivalent to the closure of `C` being perfect,
see `preperfect_iff_perfect_closure`. This property is also called dense-in-itself. -/
/-
**Preperfect** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Preperfect (C : Set α) : Prop
参数：C : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `C` is preperfect if all of its points are accumulation points of itself.
If `α` is a T1 space, this is equivalent to the closure of `C` being perfect,
see `preperfect_iff_perfect_closure`. This property is also called dense-in-itse
lf.
-/
def Preperfect (C : Set α) : Prop :=
  ∀ x ∈ C, AccPt x (𝓟 C)

/-- A set `C` is called perfect if it is closed and all of its
points are accumulation points of itself.
Note that we do not require `C` to be nonempty. -/
@[mk_iff perfect_def]
/-
**Perfect** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → [TopologicalSpace α] → Set α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `C` is called perfect if it is closed and all of its
points are accumulation points of itself.
Note that we do not require `C` to be nonempty.
-/
structure Perfect (C : Set α) : Prop where
  closed : IsClosed C
  acc : Preperfect C
/-
**preperfect_iff_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preperfect_iff_nhds : Preperfect C ↔ forall x in C, forall U in 𝓝 x, exist
s y in U inter C, y != x
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
theorem preperfect_iff_nhds : Preperfect C ↔ ∀ x ∈ C, ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x := by
  simp only [Preperfect, accPt_iff_nhds]

section PerfectSpace

variable (α)

/--
A topological space `X` is said to be perfect if its universe is a perfect set.
Equivalently, this means that `𝓝[≠] x ≠ ⊥` for every point `x : X`.
-/
@[mk_iff perfectSpace_def]
/-
**PerfectSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space `X` is said to be perfect if its universe is a perfect set.
Equivalently, this means that `𝓝[≠] x ≠ ⊥` for every point `x : X`.
-/
class PerfectSpace : Prop where
  univ_preperfect : Preperfect (Set.univ : Set α)
/-
**PerfectSpace.univ_perfect** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PerfectSpace.univ_perfect [PerfectSpace α] : Perfect (Set.univ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `PerfectSpace.univ_preperfect`：∀ {α : Type u_1} {inst : TopologicalSpace 
α} [self : PerfectSpace α], Preperfect Set.univ
-/
theorem PerfectSpace.univ_perfect [PerfectSpace α] : Perfect (Set.univ : Set α) :=
  ⟨isClosed_univ, PerfectSpace.univ_preperfect⟩

end PerfectSpace

section Preperfect

/-- The intersection of a preperfect set and an open set is preperfect. -/
/-
**Preperfect.open_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Preperfect.open_inter {U : Set α} (hC : Preperfect C) (hU : IsOpen U) : Pr
eperfect (U inter C)
参数：hC : Preperfect C；hU : IsOpen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AccPt.nhds_inter`：AccPt.nhds_inter {x : α} {U : Set α} (h_acc : AccPt x 
(𝓟 C)) (hU : U in 𝓝 x) : AccPt x (𝓟 (U inter C))
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
The intersection of a preperfect set and an open set is preperfect.
-/
theorem Preperfect.open_inter {U : Set α} (hC : Preperfect C) (hU : IsOpen U) :
    Preperfect (U ∩ C) := by
  rintro x ⟨xU, xC⟩
  apply (hC _ xC).nhds_inter
  exact hU.mem_nhds xU

/-- The closure of a preperfect set is perfect.
For a converse, see `preperfect_iff_perfect_closure`. -/
/-
**Preperfect.perfect_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Preperfect.perfect_closure (hC : Preperfect C) : Perfect (closure C)
参数：hC : Preperfect C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `AccPt.mono`：AccPt.mono {F G : Filter X} (h : AccPt x F) (hFG : F <= G) :
 AccPt x G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AccPt.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (F : Fi
lter X), AccPt x F = (nhdsWithin x {x}ᶜ ⊓ F).NeBot
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `closure_eq_cluster_pts`：closure_eq_cluster_pts : closure s = { a | Clust
erPt a (𝓟 s) }

--- 原说明 ---
The closure of a preperfect set is perfect.
For a converse, see `preperfect_iff_perfect_closure`.
-/
theorem Preperfect.perfect_closure (hC : Preperfect C) : Perfect (closure C) := by
  constructor; · exact isClosed_closure
  intro x hx
  by_cases h : x ∈ C <;> apply AccPt.mono _ (principal_mono.mpr subset_closure)
  · exact hC _ h
  have : {x}ᶜ ∩ C = C := by simp [h]
  rw [AccPt, nhdsWithin, inf_assoc, inf_principal, this]
  rw [closure_eq_cluster_pts] at hx
  exact hx

/-
Open subsects in perfect spaces are preperfect.
-/
/-
**IsOpen.preperfect** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.preperfect [PerfectSpace α] {U : Set α} (hU : IsOpen U) : Preperfec
t U
参数：hU : IsOpen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Preperfect.open_inter`：Preperfect.open_inter {U : Set α} (hC : Preperfec
t C) (hU : IsOpen U) : Preperfect (U inter C)
· 使用定理 `PerfectSpace.univ_preperfect`：∀ {α : Type u_1} {inst : TopologicalSpace 
α} [self : PerfectSpace α], Preperfect Set.univ

--- 原说明 ---
Open subsects in perfect spaces are preperfect.
-/
theorem IsOpen.preperfect [PerfectSpace α] {U : Set α} (hU : IsOpen U) :
    Preperfect U := by
  simpa using PerfectSpace.univ_preperfect.open_inter hU

/-
Closures of open subsects in perfect spaces are preperfect, hence perfect.
-/
/-
**IsOpen.perfect_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.perfect_closure [PerfectSpace α] {U : Set α} (hU : IsOpen U) : Perf
ect (closure U)
参数：hU : IsOpen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Preperfect.perfect_closure`：Preperfect.perfect_closure (hC : Preperfect 
C) : Perfect (closure C)
· 使用定理 `IsOpen.preperfect`：IsOpen.preperfect [PerfectSpace α] {U : Set α} (hU : 
IsOpen U) : Preperfect U

--- 原说明 ---
Closures of open subsects in perfect spaces are preperfect, hence perfect.
-/
theorem IsOpen.perfect_closure [PerfectSpace α] {U : Set α} (hU : IsOpen U) :
    Perfect (closure U) :=
  hU.preperfect.perfect_closure

/-- In a T1 space, being preperfect is equivalent to having perfect closure. -/
/-
**preperfect_iff_perfect_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preperfect_iff_perfect_closure [T1Space α] : Preperfect C ↔ Perfect (closu
re C)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Preperfect.perfect_closure`：Preperfect.perfect_closure (hC : Preperfect 
C) : Perfect (closure C)
· 使用定理 `Perfect.acc`：∀ {α : Type u_1} [inst : TopologicalSpace α] {C : Set α}, P
erfect C → Preperfect C
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `accPt_iff_frequently`：accPt_iff_frequently {x : X} {C : Set X} : AccPt x
 (𝓟 C) ↔ existsᶠ y in 𝓝 x, y != x ∧ y in C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ne.nhdsWithin_compl_singleton`：Ne.nhdsWithin_compl_singleton [T1Space X]
 {x y : X} (h : x != y) : 𝓝[{y}ᶜ] x = 𝓝 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `frequently_frequently_nhds`：frequently_frequently_nhds {p : X -> Prop} :
 (existsᶠ x' in 𝓝 x, existsᶠ x'' in 𝓝 x', p x'') ↔ existsᶠ x in 𝓝 x, p x
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x

--- 原说明 ---
In a T1 space, being preperfect is equivalent to having perfect closure.
-/
theorem preperfect_iff_perfect_closure [T1Space α] : Preperfect C ↔ Perfect (closure C) := by
  constructor <;> intro h
  · exact h.perfect_closure
  intro x xC
  have H : AccPt x (𝓟 (closure C)) := h.acc _ (subset_closure xC)
  rw [accPt_iff_frequently] at *
  have : ∀ y, y ≠ x ∧ y ∈ closure C → ∃ᶠ z in 𝓝 y, z ≠ x ∧ z ∈ C := by
    rintro y ⟨hyx, yC⟩
    simp only [← mem_compl_singleton_iff, and_comm, ← frequently_nhdsWithin_iff,
      hyx.nhdsWithin_compl_singleton, ← mem_closure_iff_frequently]
    exact yC
  rw [← frequently_frequently_nhds]
  exact H.mono this
/-
**Perfect.closure_nhds_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Perfect.closure_nhds_inter {U : Set α} (hC : Perfect C) (x : α) (xC : x in
 C) (xU : x in U) (Uop : IsOpen U) : Perfect (closure (U inter C)) ∧ (closure (U
 inter C)).Nonempty
参数：hC : Perfect C；x : α；xC : x in C；xU : x in U；Uop : IsOpen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Preperfect.perfect_closure`：Preperfect.perfect_closure (hC : Preperfect 
C) : Perfect (closure C)
· 使用定理 `Preperfect.open_inter`：Preperfect.open_inter {U : Set α} (hC : Preperfec
t C) (hU : IsOpen U) : Preperfect (U inter C)
· 使用定理 `Perfect.acc`：∀ {α : Type u_1} [inst : TopologicalSpace α] {C : Set α}, P
erfect C → Preperfect C
· 使用定理 `Set.Nonempty.closure`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Se
t X}, s.Nonempty → (closure s).Nonempty
-/
theorem Perfect.closure_nhds_inter {U : Set α} (hC : Perfect C) (x : α) (xC : x ∈ C) (xU : x ∈ U)
    (Uop : IsOpen U) : Perfect (closure (U ∩ C)) ∧ (closure (U ∩ C)).Nonempty := by
  constructor
  · apply Preperfect.perfect_closure
    exact hC.acc.open_inter Uop
  apply Nonempty.closure
  exact ⟨x, ⟨xU, xC⟩⟩

/-- Given a perfect nonempty set in a T2.5 space, we can find two disjoint perfect subsets.
This is the main inductive step in the proof of the Cantor-Bendixson Theorem. -/
/-
**Perfect.splitting** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Perfect.splitting [T25Space α] (hC : Perfect C) (hnonempty : C.Nonempty) :
 exists C₀ C₁ : Set α, (Perfect C₀ ∧ C₀.Nonempty ∧ C₀ subseteq C) ∧ (Perfect C₁ 
∧ C₁.Nonempty ∧ C₁ subseteq C) ∧ Disjoint C₀ C₁
参数：hC : Perfect C；hnonempty : C.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfect.acc`：∀ {α : Type u_1} [inst : TopologicalSpace α] {C : Set α}, P
erfect C → Preperfect C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `accPt_iff_nhds`：accPt_iff_nhds {x : X} {C : Set X} : AccPt x (𝓟 C) ↔ for
all U in 𝓝 x, exists y in U inter C, y != x
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `exists_open_nhds_disjoint_closure`：exists_open_nhds_disjoint_closure [T2
5Space X] {x y : X} (h : x != y) : exists u : Set X, x in u ∧ IsOpen u ∧ exists 
v : Set X, y in v ∧ IsO…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `Perfect.closure_nhds_inter`：Perfect.closure_nhds_inter {U : Set α} (hC :
 Perfect C) (x : α) (xC : x in C) (xU : x in U) (Uop : IsOpen U) : Perfect (clos
ure (U inter C))…
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `Perfect.closed`：∀ {α : Type u_1} [inst : TopologicalSpace α] {C : Set α}
, Perfect C → IsClosed C
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s

--- 原说明 ---
Given a perfect nonempty set in a T2.5 space, we can find two disjoint perfect s
ubsets.
This is the main inductive step in the proof of the Cantor-Bendixson Theorem.
-/
theorem Perfect.splitting [T25Space α] (hC : Perfect C) (hnonempty : C.Nonempty) :
    ∃ C₀ C₁ : Set α,
    (Perfect C₀ ∧ C₀.Nonempty ∧ C₀ ⊆ C) ∧ (Perfect C₁ ∧ C₁.Nonempty ∧ C₁ ⊆ C) ∧ Disjoint C₀ C₁ := by
  obtain ⟨y, yC⟩ := hnonempty
  obtain ⟨x, xC, hxy⟩ : ∃ x ∈ C, x ≠ y := by
    have := hC.acc _ yC
    rw [accPt_iff_nhds] at this
    rcases this univ univ_mem with ⟨x, xC, hxy⟩
    exact ⟨x, xC.2, hxy⟩
  obtain ⟨U, xU, Uop, V, yV, Vop, hUV⟩ := exists_open_nhds_disjoint_closure hxy
  use closure (U ∩ C), closure (V ∩ C)
  constructor <;> rw [← and_assoc]
  · refine ⟨hC.closure_nhds_inter x xC xU Uop, ?_⟩
    rw [hC.closed.closure_subset_iff]
    exact inter_subset_right
  constructor
  · refine ⟨hC.closure_nhds_inter y yC yV Vop, ?_⟩
    rw [hC.closed.closure_subset_iff]
    exact inter_subset_right
  apply Disjoint.mono _ _ hUV <;> apply closure_mono <;> exact inter_subset_left
/-
**IsPreconnected.preperfect_of_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsPreconnected.preperfect_of_nontrivial [T1Space α] {U : Set α} (hu : U.No
ntrivial) (h : IsPreconnected U) : Preperfect U
参数：hu : U.Nontrivial；h : IsPreconnected U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `accPt_principal_iff_clusterPt`：accPt_principal_iff_clusterPt {x : X} {C 
: Set X} : AccPt x (𝓟 C) ↔ ClusterPt x (𝓟 (C \ { x }))
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
· 使用定理 `Set.singleton_inter_nonempty`：singleton_inter_nonempty : ({a} inter s).N
onempty ↔ a in s
· 使用定理 `Set.Nonempty.right`：∀ {α : Type u} {s t : Set α}, (s ∩ t).Nonempty → t.N
onempty
· 使用定理 `isPreconnected_closed_iff`：isPreconnected_closed_iff {s : Set α} : IsPre
connected s ↔ forall t t', IsClosed t -> IsClosed t' -> s subseteq t union t' ->
 (s inter t).No…
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_singleton_nonempty`：inter_singleton_nonempty : (s inter {a}).N
onempty ↔ a in s
· 使用定理 `Set.Nontrivial.exists_ne`：∀ {α : Type u} {s : Set α}, s.Nontrivial → ∀ (
z : α), ∃ x ∈ s, x ≠ z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma IsPreconnected.preperfect_of_nontrivial [T1Space α] {U : Set α} (hu : U.Nontrivial)
    (h : IsPreconnected U) : Preperfect U := by
  intro x hx
  rw [isPreconnected_closed_iff] at h
  specialize h {x} (closure (U \ {x})) isClosed_singleton isClosed_closure ?_ ?_ ?_
  · trans {x} ∪ (U \ {x})
    · simp
    apply Set.union_subset_union_right
    exact subset_closure
  · exact Set.inter_singleton_nonempty.mpr hx
  · obtain ⟨y, hy⟩ := Set.Nontrivial.exists_ne hu x
    use y
    simp only [Set.mem_inter_iff, hy, true_and]
    apply subset_closure
    simp [hy]
  · apply Set.Nonempty.right at h
    rw [Set.singleton_inter_nonempty, mem_closure_iff_clusterPt,
      ← accPt_principal_iff_clusterPt] at h
    exact h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T1Space α] [ConnectedSpace α] [Nontrivial α] : PerfectSpace α := by
  constructor
  apply isPreconnected_univ.preperfect_of_nontrivial
  rw [Set.nontrivial_univ_iff]
  infer_instance

end Preperfect

section Kernel

/-- The **Cantor-Bendixson Theorem**: Any closed subset of a second countable space
can be written as the union of a countable set and a perfect set. -/
/-
**exists_countable_union_perfect_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_countable_union_perfect_of_isClosed [SecondCountableTopology α] (hc
losed : IsClosed C) : exists V D : Set α, V.Countable ∧ Perfect D ∧ C = V union 
D
参数：hclosed : IsClosed C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.exists_countable_basis`：exists_countable_basis [SecondC
ountableTopology α] : exists b : Set (Set α), b.Countable ∧ ∅ ∉ b ∧ IsTopologica
lBasis b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Countable.biUnion`：∀ {α : Type u} {β : Type v} {s : Set α} {t : (a :
 α) → a ∈ s → Set β},   s.Countable → (∀ (a : α) (ha : a ∈ s), (t a ha).Countabl
e) → (⋃ a, …
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Set.sep_subset`：sep_subset (s : Set α) (p : α -> Prop) : { x in s | p x 
} subseteq s
· 使用定理 `Set.sep_subset_ofPred`：sep_subset_ofPred (s : Set α) (p : α -> Prop) : {
 x in s | p x } subseteq { x | p x }
· 使用定理 `IsClosed.sdiff`：IsClosed.sdiff (h₁ : IsClosed s) (h₂ : IsOpen t) : IsClo
sed (s \ t)
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen`：∀ {α : Type u} [t : Topologi
calSpace α] {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTopologicalBasis
 b → s ∈ b → IsOpen s
· 使用定理 `preperfect_iff_nhds`：preperfect_iff_nhds : Preperfect C ↔ forall x in C,
 forall U in 𝓝 x, exists y in U inter C, y != x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.mem_nhds_iff`：∀ {α : Type u} [t : To
pologicalSpace α] {a : α} {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTo
pologicalBasis b → (s ∈ nhds a ↔ ∃ t ∈…
· 使用定理 `Set.mem_union_right`：mem_union_right {x : α} {b : Set α} (a : Set α) : x
 in b -> x in a union b
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `Set.Countable.union`：∀ {α : Type u} {s t : Set α}, s.Countable → t.Count
able → (s ∪ t).Countable
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.countable_singleton`：∀ {α : Type u} (a : α), {a}.Countable
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_union_sdiff`：inter_union_sdiff (s t : Set α) : s inter t union
 s \ t = s

--- 原说明 ---
The **Cantor-Bendixson Theorem**: Any closed subset of a second countable space
can be written as the union of a countable set and a perfect set.
-/
theorem exists_countable_union_perfect_of_isClosed [SecondCountableTopology α]
    (hclosed : IsClosed C) : ∃ V D : Set α, V.Countable ∧ Perfect D ∧ C = V ∪ D := by
  obtain ⟨b, bct, _, bbasis⟩ := TopologicalSpace.exists_countable_basis α
  let v := { U ∈ b | (U ∩ C).Countable }
  let V := ⋃ U ∈ v, U
  let D := C \ V
  have Vct : (V ∩ C).Countable := by
    simp only [V, iUnion_inter]
    apply Countable.biUnion
    · exact bct.mono (sep_subset _ _)
    · exact sep_subset_ofPred _ _
  refine ⟨V ∩ C, D, Vct, ⟨?_, ?_⟩, ?_⟩
  · refine hclosed.sdiff (isOpen_biUnion fun _ ↦ ?_)
    exact fun ⟨Ub, _⟩ ↦ IsTopologicalBasis.isOpen bbasis Ub
  · rw [preperfect_iff_nhds]
    intro x xD E xE
    have : ¬(E ∩ D).Countable := by
      intro h
      obtain ⟨U, hUb, xU, hU⟩ : ∃ U ∈ b, x ∈ U ∧ U ⊆ E :=
        (IsTopologicalBasis.mem_nhds_iff bbasis).mp xE
      have hU_cnt : (U ∩ C).Countable := by
        apply @Countable.mono _ _ (E ∩ D ∪ V ∩ C)
        · rintro y ⟨yU, yC⟩
          by_cases h : y ∈ V
          · exact mem_union_right _ (mem_inter h yC)
          · exact mem_union_left _ (mem_inter (hU yU) ⟨yC, h⟩)
        exact Countable.union h Vct
      have : U ∈ v := ⟨hUb, hU_cnt⟩
      apply xD.2
      exact mem_biUnion this xU
    by_contra! h
    exact absurd (Countable.mono h (Set.countable_singleton _)) this
  · rw [inter_comm, inter_union_sdiff]

/-- Any uncountable closed set in a second countable space contains a nonempty perfect subset. -/
/-
**exists_perfect_nonempty_of_isClosed_of_not_countable** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：exists_perfect_nonempty_of_isClosed_of_not_countable [SecondCountableTopol
ogy α] (hclosed : IsClosed C) (hunc : ¬C.Countable) : exists D : Set α, Perfect 
D ∧ D.Nonempty ∧ D subseteq C
参数：hclosed : IsClosed C；hunc : ¬C.Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_countable_union_perfect_of_isClosed`：exists_countable_union_perfe
ct_of_isClosed [SecondCountableTopology α] (hclosed : IsClosed C) : exists V D :
 Set α, V.Countable ∧ Perfect D …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t

--- 原说明 ---
Any uncountable closed set in a second countable space contains a nonempty perfe
ct subset.
-/
theorem exists_perfect_nonempty_of_isClosed_of_not_countable [SecondCountableTopology α]
    (hclosed : IsClosed C) (hunc : ¬C.Countable) : ∃ D : Set α, Perfect D ∧ D.Nonempty ∧ D ⊆ C := by
  rcases exists_countable_union_perfect_of_isClosed hclosed with ⟨V, D, Vct, Dperf, VD⟩
  refine ⟨D, ⟨Dperf, ?_⟩⟩
  constructor
  · rw [nonempty_iff_ne_empty]
    by_contra h
    rw [h, union_empty] at VD
    rw [VD] at hunc
    contradiction
  rw [VD]
  exact subset_union_right

end Kernel

end Basic

section PerfectSpace

variable {X : Type*} [TopologicalSpace X]

/-
**perfectSpace_iff_forall_not_isolated** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：perfectSpace_iff_forall_not_isolated : PerfectSpace X ↔ forall x : X, Filt
er.NeBot (𝓝[!=] x)
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
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem perfectSpace_iff_forall_not_isolated : PerfectSpace X ↔ ∀ x : X, Filter.NeBot (𝓝[≠] x) := by
  simp [perfectSpace_def, Preperfect, AccPt]
/-
**PerfectSpace.not_isolated** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PerfectSpace.not_isolated [PerfectSpace X] (x : X) : Filter.NeBot (𝓝[!=] x
)
参数：x : X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `perfectSpace_iff_forall_not_isolated`：perfectSpace_iff_forall_not_isolat
ed : PerfectSpace X ↔ forall x : X, Filter.NeBot (𝓝[!=] x)
-/
instance PerfectSpace.not_isolated [PerfectSpace X] (x : X) : Filter.NeBot (𝓝[≠] x) :=
  perfectSpace_iff_forall_not_isolated.mp ‹_› x

end PerfectSpace

