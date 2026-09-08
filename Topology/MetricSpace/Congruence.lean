/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Newell Jensen
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Dilation

/-!
# Congruences

This file defines `Congruent`, i.e., the equivalence between indexed families of points in a metric
space where all corresponding pairwise distances are the same. The motivating example are
triangles in the plane.

## Implementation notes

After considering two possible approaches to defining congruence — either based on equal pairwise
distances or the existence of an isometric equivalence — we have opted for the broader concept of
equal pairwise distances. This notion is commonly employed in the literature across various metric
spaces that lack an isometric equivalence.

For more details see the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Euclidean.20Geometry).

## Notation

* `v₁ ≅ v₂`: for `Congruent v₁ v₂`.
-/

@[expose] public section

variable {ι ι' : Type*} {P₁ P₂ P₃ P₄ : Type*} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}

section PseudoEMetricSpace

variable [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂]
variable [PseudoEMetricSpace P₃] [PseudoEMetricSpace P₄]

/-- A congruence between indexed sets of vertices v₁ and v₂.
Use `open scoped Congruent` to access the `v₁ ≅ v₂` notation. -/
/-
**Congruent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Congruent (v₁ : ι -> P₁) (v₂ : ι -> P₂) : Prop
参数：v₁ : ι -> P₁；v₂ : ι -> P₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A congruence between indexed sets of vertices v₁ and v₂.
Use `open scoped Congruent` to access the `v₁ ≅ v₂` notation.
-/
def Congruent (v₁ : ι → P₁) (v₂ : ι → P₂) : Prop :=
  ∀ i₁ i₂, edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂)

@[inherit_doc]
scoped[Congruent] infixl:25 " ≅ " => Congruent

/-- Congruence holds if and only if all extended distances are the same. -/
/-
**congruent_iff_edist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：congruent_iff_edist_eq : Congruent v₁ v₂ ↔ forall i₁ i₂, edist (v₁ i₁) (v₁
 i₂) = edist (v₂ i₁) (v₂ i₂)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Congruence holds if and only if all extended distances are the same.
-/
lemma congruent_iff_edist_eq :
    Congruent v₁ v₂ ↔ ∀ i₁ i₂, edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂) :=
  Iff.rfl

/-- Congruence holds if and only if all extended distances between points with different
indices are the same. -/
/-
**congruent_iff_pairwise_edist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：congruent_iff_pairwise_edist_eq : Congruent v₁ v₂ ↔ Pairwise fun i₁ i₂ => 
edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Congruence holds if and only if all extended distances between points with diffe
rent
indices are the same.
-/
lemma congruent_iff_pairwise_edist_eq :
    Congruent v₁ v₂ ↔ Pairwise fun i₁ i₂ ↦ edist (v₁ i₁) (v₁ i₂) = edist (v₂ i₁) (v₂ i₂) := by
  refine ⟨fun h ↦ fun _ _ _ ↦ h _ _, fun h ↦ fun i₁ i₂ ↦ ?_⟩
  by_cases hi : i₁ = i₂
  · simp [hi]
  · exact h hi

namespace Congruent

/-- A congruence preserves extended distance. Forward direction of `congruent_iff_edist_eq`. -/
alias ⟨edist_eq, _⟩ := congruent_iff_edist_eq

/-- Congruence follows from preserved extended distance. Backward direction of
`congruent_iff_edist_eq`. -/
alias ⟨_, of_edist_eq⟩ := congruent_iff_edist_eq

/-- A congruence pairwise preserves extended distance. Forward direction of
`congruent_iff_pairwise_edist_eq`. -/
alias ⟨pairwise_edist_eq, _⟩ := congruent_iff_pairwise_edist_eq

/-- Congruence follows from pairwise preserved extended distance. Backward direction of
`congruent_iff_pairwise_edist_eq`. -/
alias ⟨_, of_pairwise_edist_eq⟩ := congruent_iff_pairwise_edist_eq

/-
**Congruent.refl** 是 Mathlib 中的一个定理，位于命名空间 `Congruent`。
形式化陈述：∀ {ι : Type u_1} {P₁ : Type u_3} [inst : PseudoEMetricSpace P₁] (v₁ : ι → 
P₁), Congruent v₁ v₁
参数：v₁ : ι → P₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[refl] protected lemma refl (v₁ : ι → P₁) : v₁ ≅ v₁ := fun _ _ ↦ rfl
/-
**Congruent.symm** 是 Mathlib 中的一个定理，位于命名空间 `Congruent`。
形式化陈述：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {v₁ : ι → P₁} {v₂ : ι → P
₂} [inst : PseudoEMetricSpace P₁]   [inst_1 : PseudoEMetricSpace P₂], Congruent 
v₁ v₂ → Congruent v₂ v₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[symm] protected lemma symm (h : v₁ ≅ v₂) : v₂ ≅ v₁ := fun i₁ i₂ ↦ (h i₁ i₂).symm
/-
**Congruent._root_.congruent_comm** 是 Mathlib 中的一个引理，位于命名空间 `Congruent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.congruent_comm : v₁ ≅ v₂ ↔ v₂ ≅ v₁ :=
  ⟨Congruent.symm, Congruent.symm⟩
/-
**Congruent.trans** 是 Mathlib 中的一个定理，位于命名空间 `Congruent`。
形式化陈述：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {P₃ : Type u_5} {v₁ : ι →
 P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}   [inst : PseudoEMetricSpace P₁] [inst_1 : Pseu
doEMetricSpace P₂] [inst_2 : PseudoEMetricSpace P₃],   Congruent v₁ v₂ → Congrue
nt v₂ v₃ → Congruent v₁ v₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[trans] protected lemma trans (h₁₂ : v₁ ≅ v₂) (h₂₃ : v₂ ≅ v₃) : v₁ ≅ v₃ :=
  fun i₁ i₂ ↦ (h₁₂ i₁ i₂).trans (h₂₃ i₁ i₂)

/-- Change the index set ι to an index ι' that maps to ι. -/
/-
**Congruent.index_map** 是 Mathlib 中的一个引理，位于命名空间 `Congruent`。
形式化陈述：index_map (h : v₁ ≅ v₂) (f : ι' -> ι) : (v₁ ∘ f) ≅ (v₂ ∘ f)
参数：h : v₁ ≅ v₂；f : ι' -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Congruent.edist_eq`：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {v₁
 : ι → P₁} {v₂ : ι → P₂} [inst : PseudoEMetricSpace P₁]   [inst_1 : PseudoEMetri
cSpace P…

--- 原说明 ---
Change the index set ι to an index ι' that maps to ι.
-/
lemma index_map (h : v₁ ≅ v₂) (f : ι' → ι) : (v₁ ∘ f) ≅ (v₂ ∘ f) :=
  fun i₁ i₂ ↦ edist_eq h (f i₁) (f i₂)

/-- Change between equivalent index sets ι and ι'. -/
/-
**Congruent.index_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Congruent`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {P₁ : Type u_3} {P₂ : Type u_4} [inst : P
seudoEMetricSpace P₁]   [inst_1 : PseudoEMetricSpace P₂] {E : Type u_7} [inst_2 
: EquivLike E ι' ι] (f : E) (v₁ : ι → P₁) (v₂ : ι → P₂),   Congruent (v₁ ∘ ⇑f) (
v₂ ∘ ⇑f) ↔ Congruent v₁ v₂
参数：f : E；v₁ : ι → P₁；v₂ : ι → P₂；v₁ ∘ ⇑f；v₂ ∘ ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.apply_coe_symm_apply`：∀ {α : Sort u} {β : Sort v} {F : Sort u_
1} [inst : EquivLike F α β] (e : F) (x : β), e ((↑e).symm x) = x
· 使用定理 `Congruent.edist_eq`：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {v₁
 : ι → P₁} {v₂ : ι → P₂} [inst : PseudoEMetricSpace P₁]   [inst_1 : PseudoEMetri
cSpace P…
· 使用引理 `Congruent.index_map`：index_map (h : v₁ ≅ v₂) (f : ι' -> ι) : (v₁ ∘ f) ≅ 
(v₂ ∘ f)

--- 原说明 ---
Change between equivalent index sets ι and ι'.
-/
@[simp] lemma index_equiv {E : Type*} [EquivLike E ι' ι] (f : E) (v₁ : ι → P₁) (v₂ : ι → P₂) :
    v₁ ∘ f ≅ v₂ ∘ f ↔ v₁ ≅ v₂ := by
  refine ⟨fun h i₁ i₂ ↦ ?_, fun h ↦ index_map h f⟩
  simpa [(EquivLike.toEquiv f).right_inv i₁, (EquivLike.toEquiv f).right_inv i₂]
    using edist_eq h ((EquivLike.toEquiv f).symm i₁) ((EquivLike.toEquiv f).symm i₂)

/-- Families with at most a single point are always congruent. -/
@[nontriviality, simp]
/-
**Congruent.of_subsingleton_index** 是 Mathlib 中的一个引理，位于命名空间 `Congruent`。
形式化陈述：of_subsingleton_index [Subsingleton ι] : v₁ ≅ v₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Families with at most a single point are always congruent.
-/
lemma of_subsingleton_index [Subsingleton ι] : v₁ ≅ v₂ :=
  fun i j => by simp [Subsingleton.elim i j]
/-
**Congruent.comp_left** 是 Mathlib 中的一个引理，位于命名空间 `Congruent`。
形式化陈述：comp_left {f : P₁ -> P₃} (hf : Isometry f) (h : v₁ ≅ v₂) : f ∘ v₁ ≅ v₂
参数：hf : Isometry f；h : v₁ ≅ v₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Congruent.trans`：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {P₃ : 
Type u_5} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}   [inst : PseudoEMetricSpace
 P₁] …
-/
lemma comp_left {f : P₁ → P₃} (hf : Isometry f) (h : v₁ ≅ v₂) : f ∘ v₁ ≅ v₂ :=
  .trans (fun _ _ ↦ hf _ _) h
/-
**Congruent.comp_right** 是 Mathlib 中的一个引理，位于命名空间 `Congruent`。
形式化陈述：comp_right {f : P₂ -> P₃} (hf : Isometry f) (h : v₁ ≅ v₂) : v₁ ≅ f ∘ v₂
参数：hf : Isometry f；h : v₁ ≅ v₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Congruent.trans`：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {P₃ : 
Type u_5} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}   [inst : PseudoEMetricSpace
 P₁] …
· 使用定理 `Congruent.symm`：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {v₁ : ι
 → P₁} {v₂ : ι → P₂} [inst : PseudoEMetricSpace P₁]   [inst_1 : PseudoEMetricSpa
ce P…
-/
lemma comp_right {f : P₂ → P₃} (hf : Isometry f) (h : v₁ ≅ v₂) : v₁ ≅ f ∘ v₂ :=
  .trans h (.symm <| fun _ _ ↦ hf _ _)

@[simp]
/-
**Congruent.comp_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `Congruent`。
形式化陈述：comp_left_iff {f : P₁ -> P₃} (hf : Isometry f) : f ∘ v₁ ≅ v₂ ↔ v₁ ≅ v₂
参数：hf : Isometry f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Congruent.trans`：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {P₃ : 
Type u_5} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}   [inst : PseudoEMetricSpace
 P₁] …
· 使用引理 `Congruent.comp_right`：comp_right {f : P₂ -> P₃} (hf : Isometry f) (h : v
₁ ≅ v₂) : v₁ ≅ f ∘ v₂
· 使用定理 `Congruent.refl`：∀ {ι : Type u_1} {P₁ : Type u_3} [inst : PseudoEMetricSp
ace P₁] (v₁ : ι → P₁), Congruent v₁ v₁
· 使用引理 `Congruent.comp_left`：comp_left {f : P₁ -> P₃} (hf : Isometry f) (h : v₁ 
≅ v₂) : f ∘ v₁ ≅ v₂
-/
lemma comp_left_iff {f : P₁ → P₃} (hf : Isometry f) : f ∘ v₁ ≅ v₂ ↔ v₁ ≅ v₂ :=
  ⟨.trans <| .comp_right hf (.refl _), .comp_left hf⟩

@[simp]
/-
**Congruent.comp_right_iff** 是 Mathlib 中的一个引理，位于命名空间 `Congruent`。
形式化陈述：comp_right_iff {f : P₂ -> P₃} (hf : Isometry f) : v₁ ≅ f ∘ v₂ ↔ v₁ ≅ v₂
参数：hf : Isometry f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congruent_comm`：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {v₁ : ι
 → P₁} {v₂ : ι → P₂} [inst : PseudoEMetricSpace P₁]   [inst_1 : PseudoEMetricSpa
ce P…
· 使用引理 `Congruent.comp_left_iff`：comp_left_iff {f : P₁ -> P₃} (hf : Isometry f) 
: f ∘ v₁ ≅ v₂ ↔ v₁ ≅ v₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma comp_right_iff {f : P₂ → P₃} (hf : Isometry f) : v₁ ≅ f ∘ v₂ ↔ v₁ ≅ v₂ := by
  rw [congruent_comm, comp_left_iff hf, congruent_comm]

/-- Two sets of vertices remain congruent under a dilation if the dilations have equal ratios. -/
/-
**Congruent.comp_dilation** 是 Mathlib 中的一个引理，位于命名空间 `Congruent`。
形式化陈述：comp_dilation {F₁ F₂} [FunLike F₁ P₁ P₃] [DilationClass F₁ P₁ P₃] [FunLike
 F₂ P₂ P₄] [DilationClass F₂ P₂ P₄] {f₁ : F₁} {f₂ : F₂} (h : v₁ ≅ v₂) (hf : Dila
tion.ratio f₁ = Dilation.ratio f₂) : f₁ ∘ v₁ ≅ f₂ ∘ v₂
参数：h : v₁ ≅ v₂；hf : Dilation.ratio f₁ = Dilation.ratio f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dilation.edist_eq`：edist_eq [DilationClass F α β] (f : F) (x y : α) : ed
ist (f x) (f y) = ratio f * edist x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two sets of vertices remain congruent under a dilation if the dilations have equ
al ratios.
-/
lemma comp_dilation {F₁ F₂}
    [FunLike F₁ P₁ P₃] [DilationClass F₁ P₁ P₃] [FunLike F₂ P₂ P₄] [DilationClass F₂ P₂ P₄]
    {f₁ : F₁} {f₂ : F₂} (h : v₁ ≅ v₂) (hf : Dilation.ratio f₁ = Dilation.ratio f₂) :
    f₁ ∘ v₁ ≅ f₂ ∘ v₂ :=
  fun i j => by simp [hf, h i j]

end Congruent

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace P₁] [PseudoMetricSpace P₂]

/-- Congruence holds if and only if all non-negative distances are the same. -/
/-
**congruent_iff_nndist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：congruent_iff_nndist_eq : Congruent v₁ v₂ ↔ forall i₁ i₂, nndist (v₁ i₁) (
v₁ i₂) = nndist (v₂ i₁) (v₂ i₂)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Congruence holds if and only if all non-negative distances are the same.
-/
lemma congruent_iff_nndist_eq :
    Congruent v₁ v₂ ↔ ∀ i₁ i₂, nndist (v₁ i₁) (v₁ i₂) = nndist (v₂ i₁) (v₂ i₂) :=
  forall₂_congr (fun _ _ ↦ by rw [edist_nndist, edist_nndist]; norm_cast)

/-- Congruence holds if and only if all non-negative distances between points with different
indices are the same. -/
/-
**congruent_iff_pairwise_nndist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：congruent_iff_pairwise_nndist_eq : Congruent v₁ v₂ ↔ Pairwise fun i₁ i₂ =>
 nndist (v₁ i₁) (v₁ i₂) = nndist (v₂ i₁) (v₂ i₂)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Congruence holds if and only if all non-negative distances between points with d
ifferent
indices are the same.
-/
lemma congruent_iff_pairwise_nndist_eq :
    Congruent v₁ v₂ ↔ Pairwise fun i₁ i₂ ↦ nndist (v₁ i₁) (v₁ i₂) = nndist (v₂ i₁) (v₂ i₂) := by
  simp_rw [congruent_iff_pairwise_edist_eq, edist_nndist]
  exact_mod_cast Iff.rfl

/-- Congruence holds if and only if all distances are the same. -/
/-
**congruent_iff_dist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：congruent_iff_dist_eq : Congruent v₁ v₂ ↔ forall i₁ i₂, dist (v₁ i₁) (v₁ i
₂) = dist (v₂ i₁) (v₂ i₂)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `congruent_iff_nndist_eq`：congruent_iff_nndist_eq : Congruent v₁ v₂ ↔ for
all i₁ i₂, nndist (v₁ i₁) (v₁ i₂) = nndist (v₂ i₁) (v₂ i₂)
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_nndist`：dist_nndist (x y : α) : dist x y = nndist x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Congruence holds if and only if all distances are the same.
-/
lemma congruent_iff_dist_eq :
    Congruent v₁ v₂ ↔ ∀ i₁ i₂, dist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂) :=
  congruent_iff_nndist_eq.trans
    (forall₂_congr (fun _ _ ↦ by rw [dist_nndist, dist_nndist]; norm_cast))

/-- Congruence holds if and only if all non-negative distances between points with different
indices are the same. -/
/-
**congruent_iff_pairwise_dist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：congruent_iff_pairwise_dist_eq : Congruent v₁ v₂ ↔ Pairwise fun i₁ i₂ => d
ist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Congruence holds if and only if all non-negative distances between points with d
ifferent
indices are the same.
-/
lemma congruent_iff_pairwise_dist_eq :
    Congruent v₁ v₂ ↔ Pairwise fun i₁ i₂ ↦ dist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂) := by
  simp_rw [congruent_iff_pairwise_nndist_eq, dist_nndist]
  exact_mod_cast Iff.rfl

namespace Congruent

/-- A congruence preserves non-negative distance. Forward direction of `congruent_iff_nndist_eq`. -/
alias ⟨nndist_eq, _⟩ := congruent_iff_nndist_eq

/-- Congruence follows from preserved non-negative distance. Backward direction of
`congruent_iff_nndist_eq`. -/
alias ⟨_, of_nndist_eq⟩ := congruent_iff_nndist_eq

/-- A congruence preserves distance. Forward direction of `congruent_iff_dist_eq`. -/
alias ⟨dist_eq, _⟩ := congruent_iff_dist_eq

/-- Congruence follows from preserved distance. Backward direction of `congruent_iff_dist_eq`. -/
alias ⟨_, of_dist_eq⟩ := congruent_iff_dist_eq

/-- A congruence pairwise preserves non-negative distance. Forward direction of
`congruent_iff_pairwise_nndist_eq`. -/
alias ⟨pairwise_nndist_eq, _⟩ := congruent_iff_pairwise_nndist_eq

/-- Congruence follows from pairwise preserved non-negative distance. Backward direction of
`congruent_iff_pairwise_nndist_eq`. -/
alias ⟨_, of_pairwise_nndist_eq⟩ := congruent_iff_pairwise_nndist_eq

/-- A congruence pairwise preserves distance. Forward direction of
`congruent_iff_pairwise_dist_eq`. -/
alias ⟨pairwise_dist_eq, _⟩ := congruent_iff_pairwise_dist_eq

/-- Congruence follows from pairwise preserved distance. Backward direction of
`congruent_iff_pairwise_dist_eq`. -/
alias ⟨_, of_pairwise_dist_eq⟩ := congruent_iff_pairwise_dist_eq

end Congruent

end PseudoMetricSpace

