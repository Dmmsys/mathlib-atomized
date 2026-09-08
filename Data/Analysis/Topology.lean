/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Analysis.Filter
public import Mathlib.Topology.Bases
public import Mathlib.Topology.LocallyFinite

/-!
# Computational realization of topological spaces (experimental)

This file provides infrastructure to compute with topological spaces.

## Main declarations

* `Ctop`: Realization of a topology basis.
* `Ctop.Realizer`: Realization of a topological space. `Ctop` that generates the given topology.
* `LocallyFinite.Realizer`: Realization of the local finiteness of an indexed family of sets.
* `Compact.Realizer`: Realization of the compactness of a set.
-/

@[expose] public section


open Set

open Filter hiding Realizer

open Topology

/-- A `Ctop α σ` is a realization of a topology (basis) on `α`,
  represented by a type `σ` together with operations for the top element and
  the intersection operation. -/
/-
**Ctop** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_2 → Type (max u_1 u_2)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Ctop α σ` is a realization of a topology (basis) on `α`,
  represented by a type `σ` together with operations for the top element and
  the intersection operation.
-/
structure Ctop (α σ : Type*) where
  f : σ → Set α
  top : α → σ
  top_mem : ∀ x : α, x ∈ f (top x)
  inter : ∀ (a b) (x : α), x ∈ f a ∩ f b → σ
  inter_mem : ∀ a b x h, x ∈ f (inter a b x h)
  inter_sub : ∀ a b x h, f (inter a b x h) ⊆ f a ∩ f b

variable {α : Type*} {β : Type*} {σ : Type*} {τ : Type*}
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Ctop α (Set α)) :=
  ⟨{  f := id
      top := singleton
      top_mem := mem_singleton
      inter := fun s t _ _ ↦ s ∩ t
      inter_mem := fun _s _t _a ↦ id
      inter_sub := fun _s _t _a _ha ↦ Subset.rfl }⟩

namespace Ctop

section

variable (F : Ctop α σ)

/-
**Ctop.** 是 Mathlib 中的一个实例，位于命名空间 `Ctop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (Ctop α σ) fun _ ↦ σ → Set α :=
  ⟨Ctop.f⟩
/-
**Ctop.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ctop`。
形式化陈述：coe_mk (f T h₁ I h₂ h₃ a) : (@Ctop.mk α σ f T h₁ I h₂ h₃) a = f a
参数：f T h₁ I h₂ h₃ a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f T h₁ I h₂ h₃ a) : (@Ctop.mk α σ f T h₁ I h₂ h₃) a = f a := rfl

/-- Map a Ctop to an equivalent representation type. -/
/-
**Ctop.ofEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ctop`。
形式化陈述：ofEquiv (E : σ ≃ τ) : Ctop α σ -> Ctop α τ | ⟨f, T, h₁, I, h₂, h₃⟩ => { f
参数：E : σ ≃ τ。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Map a Ctop to an equivalent representation type.
-/
def ofEquiv (E : σ ≃ τ) : Ctop α σ → Ctop α τ
  | ⟨f, T, h₁, I, h₂, h₃⟩ =>
    { f := fun a ↦ f (E.symm a)
      top := fun x ↦ E (T x)
      top_mem := fun x ↦ by simpa using h₁ x
      inter := fun a b x h ↦ E (I (E.symm a) (E.symm b) x h)
      inter_mem := fun a b x h ↦ by simpa using h₂ (E.symm a) (E.symm b) x h
      inter_sub := fun a b x h ↦ by simpa using h₃ (E.symm a) (E.symm b) x h }

@[simp]
/-
**Ctop.ofEquiv_val** 是 Mathlib 中的一个定理，位于命名空间 `Ctop`。
形式化陈述：ofEquiv_val (E : σ ≃ τ) (F : Ctop α σ) (a : τ) : F.ofEquiv E a = F (E.symm
 a)
参数：E : σ ≃ τ；F : Ctop α σ；a : τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ofEquiv_val (E : σ ≃ τ) (F : Ctop α σ) (a : τ) : F.ofEquiv E a = F (E.symm a) := by
  cases F; rfl

end

/-- Every `Ctop` is a topological space. -/
@[instance_reducible]
/-
**Ctop.toTopsp** 是 Mathlib 中的一个定义，位于命名空间 `Ctop`。
形式化陈述：toTopsp (F : Ctop α σ) : TopologicalSpace α
参数：F : Ctop α σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every `Ctop` is a topological space.
-/
def toTopsp (F : Ctop α σ) : TopologicalSpace α := TopologicalSpace.generateFrom (Set.range F.f)
/-
**Ctop.toTopsp_isTopologicalBasis** 是 Mathlib 中的一个定理，位于命名空间 `Ctop`。
形式化陈述：toTopsp_isTopologicalBasis (F : Ctop α σ) : @TopologicalSpace.IsTopologica
lBasis _ F.toTopsp (Set.range F.f)
参数：F : Ctop α σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ctop.inter_mem`：∀ {α : Type u_1} {σ : Type u_2} (self : Ctop α σ) (a b :
 σ) (x : α) (h : x ∈ self.f a ∩ self.f b),   x ∈ self.f (self.inter a b x h)
· 使用定理 `Ctop.inter_sub`：∀ {α : Type u_1} {σ : Type u_2} (self : Ctop α σ) (a b :
 σ) (x : α) (h : x ∈ self.f a ∩ self.f b),   self.f (self.inter a b x h) ⊆ self.
f a …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Ctop.top_mem`：∀ {α : Type u_1} {σ : Type u_2} (self : Ctop α σ) (x : α),
 x ∈ self.f (self.top x)
-/
theorem toTopsp_isTopologicalBasis (F : Ctop α σ) :
    @TopologicalSpace.IsTopologicalBasis _ F.toTopsp (Set.range F.f) :=
  letI := F.toTopsp
  ⟨fun _u ⟨a, e₁⟩ _v ⟨b, e₂⟩ ↦
    e₁ ▸ e₂ ▸ fun x h ↦ ⟨_, ⟨_, rfl⟩, F.inter_mem a b x h, F.inter_sub a b x h⟩,
    eq_univ_iff_forall.2 fun x ↦ ⟨_, ⟨_, rfl⟩, F.top_mem x⟩, rfl⟩

@[simp]
/-
**Ctop.mem_nhds_toTopsp** 是 Mathlib 中的一个定理，位于命名空间 `Ctop`。
形式化陈述：mem_nhds_toTopsp (F : Ctop α σ) {s : Set α} {a : α} : s in @nhds _ F.toTop
sp a ↔ exists b, a in F b ∧ F b subseteq s
参数：F : Ctop α σ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `TopologicalSpace.IsTopologicalBasis.mem_nhds_iff`：∀ {α : Type u} [t : To
pologicalSpace α] {a : α} {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTo
pologicalBasis b → (s ∈ nhds a ↔ ∃ t ∈…
· 使用定理 `Ctop.toTopsp_isTopologicalBasis`：toTopsp_isTopologicalBasis (F : Ctop α 
σ) : @TopologicalSpace.IsTopologicalBasis _ F.toTopsp (Set.range F.f)
-/
theorem mem_nhds_toTopsp (F : Ctop α σ) {s : Set α} {a : α} :
    s ∈ @nhds _ F.toTopsp a ↔ ∃ b, a ∈ F b ∧ F b ⊆ s :=
  (@TopologicalSpace.IsTopologicalBasis.mem_nhds_iff _ F.toTopsp _ _ _
        F.toTopsp_isTopologicalBasis).trans <|
    ⟨fun ⟨_, ⟨x, rfl⟩, h⟩ ↦ ⟨x, h⟩, fun ⟨x, h⟩ ↦ ⟨_, ⟨x, rfl⟩, h⟩⟩

end Ctop

/-- A `Ctop` realizer for the topological space `T` is a `Ctop`
  which generates `T`. -/
/-
**Ctop.Realizer** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：Ctop.Realizer (α) [T : TopologicalSpace α] where σ : Type* F : Ctop α σ eq
 : F.toTopsp = T  open Ctop  /-- A `Ctop` realizes the topological space it gene
rates. -/ protected def Ctop.toRealizer (F : Ctop α σ) : @Ctop.Realizer _ F.toTo
psp
参数：α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Ctop` realizer for the topological space `T` is a `Ctop`
  which generates `T`.
-/
structure Ctop.Realizer (α) [T : TopologicalSpace α] where
  σ : Type*
  F : Ctop α σ
  eq : F.toTopsp = T

open Ctop

/-- A `Ctop` realizes the topological space it generates. -/
/-
**Ctop.toRealizer** 是 Mathlib 中的一个定义，位于命名空间 `Ctop`。
形式化陈述：{α : Type u_1} → {σ : Type u_3} → (F : Ctop α σ) → Ctop.Realizer α
参数：F : Ctop α σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Ctop` realizes the topological space it generates.
-/
protected def Ctop.toRealizer (F : Ctop α σ) : @Ctop.Realizer _ F.toTopsp :=
  @Ctop.Realizer.mk _ F.toTopsp σ F rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : Ctop α σ) : Inhabited (@Ctop.Realizer _ F.toTopsp) :=
  ⟨F.toRealizer⟩

namespace Ctop.Realizer

/-
**Ctop.Realizer.is_basis** 是 Mathlib 中的一个定理，位于命名空间 `Ctop.Realizer`。
形式化陈述：∀ {α : Type u_1} [T : TopologicalSpace α] (F : Ctop.Realizer α), Topologic
alSpace.IsTopologicalBasis (Set.range F.F.f)
参数：F : Ctop.Realizer α；Set.range F.F.f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ctop.toTopsp_isTopologicalBasis`：toTopsp_isTopologicalBasis (F : Ctop α 
σ) : @TopologicalSpace.IsTopologicalBasis _ F.toTopsp (Set.range F.f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ctop.Realizer.eq`：∀ {α : Type u_6} [T : TopologicalSpace α] (self : Ctop
.Realizer α), self.F.toTopsp = T
-/
protected theorem is_basis [T : TopologicalSpace α] (F : Realizer α) :
    TopologicalSpace.IsTopologicalBasis (Set.range F.F.f) := by
  have := toTopsp_isTopologicalBasis F.F; rwa [F.eq] at this
/-
**Ctop.Realizer.mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Ctop.Realizer`。
形式化陈述：∀ {α : Type u_1} [T : TopologicalSpace α] (F : Ctop.Realizer α) {s : Set α
} {a : α},   s ∈ nhds a ↔ ∃ b, a ∈ F.F.f b ∧ F.F.f b ⊆ s
参数：F : Ctop.Realizer α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ctop.mem_nhds_toTopsp`：mem_nhds_toTopsp (F : Ctop α σ) {s : Set α} {a : 
α} : s in @nhds _ F.toTopsp a ↔ exists b, a in F b ∧ F b subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ctop.Realizer.eq`：∀ {α : Type u_6} [T : TopologicalSpace α] (self : Ctop
.Realizer α), self.F.toTopsp = T
-/
protected theorem mem_nhds [T : TopologicalSpace α] (F : Realizer α) {s : Set α} {a : α} :
    s ∈ 𝓝 a ↔ ∃ b, a ∈ F.F b ∧ F.F b ⊆ s := by
  have := @mem_nhds_toTopsp _ _ F.F s a; rwa [F.eq] at this
/-
**Ctop.Realizer.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ctop.Realizer`。
形式化陈述：isOpen_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} : IsOpen s ↔ 
forall a in s, exists b, a in F.F b ∧ F.F b subseteq s
参数：F : Realizer α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Ctop.Realizer.mem_nhds`：∀ {α : Type u_1} [T : TopologicalSpace α] (F : C
top.Realizer α) {s : Set α} {a : α},   s ∈ nhds a ↔ ∃ b, a ∈ F.F.f b ∧ F.F.f b ⊆
 s
-/
theorem isOpen_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} :
    IsOpen s ↔ ∀ a ∈ s, ∃ b, a ∈ F.F b ∧ F.F b ⊆ s :=
  isOpen_iff_mem_nhds.trans <| forall₂_congr fun _a _h ↦ F.mem_nhds
/-
**Ctop.Realizer.isClosed_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ctop.Realizer`。
形式化陈述：isClosed_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} : IsClosed 
s ↔ forall a, (forall b, a in F.F b -> exists z, z in F.F b inter s) -> a in s
参数：F : Realizer α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Ctop.Realizer.isOpen_iff`：isOpen_iff [TopologicalSpace α] (F : Realizer 
α) {s : Set α} : IsOpen s ↔ forall a in s, exists b, a in F.F b ∧ F.F b subseteq
 s
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosed_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} :
    IsClosed s ↔ ∀ a, (∀ b, a ∈ F.F b → ∃ z, z ∈ F.F b ∩ s) → a ∈ s :=
  isOpen_compl_iff.symm.trans <|
    F.isOpen_iff.trans <|
      forall_congr' fun a ↦
        show (a ∉ s → ∃ b : F.σ, a ∈ F.F b ∧ ∀ z ∈ F.F b, z ∉ s) ↔ _ by
          have := Classical.propDecidable; rw [not_imp_comm]
          simp [not_exists, not_and, not_forall, and_comm]
/-
**Ctop.Realizer.mem_interior_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ctop.Realizer`。
形式化陈述：mem_interior_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} {a : α}
 : a in interior s ↔ exists b, a in F.F b ∧ F.F b subseteq s
参数：F : Realizer α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Ctop.Realizer.mem_nhds`：∀ {α : Type u_1} [T : TopologicalSpace α] (F : C
top.Realizer α) {s : Set α} {a : α},   s ∈ nhds a ↔ ∃ b, a ∈ F.F.f b ∧ F.F.f b ⊆
 s
-/
theorem mem_interior_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} {a : α} :
    a ∈ interior s ↔ ∃ b, a ∈ F.F b ∧ F.F b ⊆ s :=
  mem_interior_iff_mem_nhds.trans F.mem_nhds
/-
**Ctop.Realizer.isOpen** 是 Mathlib 中的一个定理，位于命名空间 `Ctop.Realizer`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] (F : Ctop.Realizer α) (s : F.
σ), IsOpen (F.F.f s)
参数：F : Ctop.Realizer α；s : F.σ；F.F.f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_nhds`：isOpen_iff_nhds : IsOpen s ↔ forall x in s, 𝓝 x <= 𝓟 s
· 使用定理 `Ctop.Realizer.mem_nhds`：∀ {α : Type u_1} [T : TopologicalSpace α] (F : C
top.Realizer α) {s : Set α} {a : α},   s ∈ nhds a ↔ ∃ b, a ∈ F.F.f b ∧ F.F.f b ⊆
 s
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
protected theorem isOpen [TopologicalSpace α] (F : Realizer α) (s : F.σ) : IsOpen (F.F s) :=
  isOpen_iff_nhds.2 fun a m ↦ by simpa using F.mem_nhds.2 ⟨s, m, Subset.refl _⟩
/-
**Ctop.Realizer.ext'** 是 Mathlib 中的一个定理，位于命名空间 `Ctop.Realizer`。
形式化陈述：ext' [T : TopologicalSpace α] {σ : Type*} {F : Ctop α σ} (H : forall a s, 
s in 𝓝 a ↔ exists b, a in F b ∧ F b subseteq s) : F.toTopsp = T
参数：H : forall a s, s in 𝓝 a ↔ exists b, a in F b ∧ F b subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext_nhds`：∀ {X : Type u_2} {t t' : TopologicalSpace X},
 (∀ (x : X), nhds x = nhds x) → t = t'
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ctop.mem_nhds_toTopsp`：mem_nhds_toTopsp (F : Ctop α σ) {s : Set α} {a : 
α} : s in @nhds _ F.toTopsp a ↔ exists b, a in F b ∧ F b subseteq s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ext' [T : TopologicalSpace α] {σ : Type*} {F : Ctop α σ}
    (H : ∀ a s, s ∈ 𝓝 a ↔ ∃ b, a ∈ F b ∧ F b ⊆ s) : F.toTopsp = T := by
  refine TopologicalSpace.ext_nhds fun x ↦ ?_
  ext s
  rw [mem_nhds_toTopsp, H]
/-
**Ctop.Realizer.ext** 是 Mathlib 中的一个定理，位于命名空间 `Ctop.Realizer`。
形式化陈述：ext [T : TopologicalSpace α] {σ : Type*} {F : Ctop α σ} (H₁ : forall a, Is
Open (F a)) (H₂ : forall a s, s in 𝓝 a -> exists b, a in F b ∧ F b subseteq s) :
 F.toTopsp = T
参数：H₁ : forall a, IsOpen (F a)；H₂ : forall a s, s in 𝓝 a -> exists b, a in F b ∧
 F b subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ctop.Realizer.ext'`：ext' [T : TopologicalSpace α] {σ : Type*} {F : Ctop 
α σ} (H : forall a s, s in 𝓝 a ↔ exists b, a in F b ∧ F b subseteq s) : F.toTops
p = T
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
-/
theorem ext [T : TopologicalSpace α] {σ : Type*} {F : Ctop α σ} (H₁ : ∀ a, IsOpen (F a))
    (H₂ : ∀ a s, s ∈ 𝓝 a → ∃ b, a ∈ F b ∧ F b ⊆ s) : F.toTopsp = T :=
  ext' fun a s ↦ ⟨H₂ a s, fun ⟨_b, h₁, h₂⟩ ↦ mem_nhds_iff.2 ⟨_, h₂, H₁ _, h₁⟩⟩

variable [TopologicalSpace α]

/-- The topological space realizer made of the open sets. -/
/-
**Ctop.Realizer.id** 是 Mathlib 中的一个定义，位于命名空间 `Ctop.Realizer`。
形式化陈述：{α : Type u_1} → [inst : TopologicalSpace α] → Ctop.Realizer α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)

--- 原说明 ---
The topological space realizer made of the open sets.
-/
protected def id : Realizer α :=
  ⟨{ x : Set α // IsOpen x },
    { f := Subtype.val
      top := fun _ ↦ ⟨univ, isOpen_univ⟩
      top_mem := mem_univ
      inter := fun ⟨_x, h₁⟩ ⟨_y, h₂⟩ _a _h₃ ↦ ⟨_, h₁.inter h₂⟩
      inter_mem := fun ⟨_x, _h₁⟩ ⟨_y, _h₂⟩ _a ↦ id
      inter_sub := fun ⟨_x, _h₁⟩ ⟨_y, _h₂⟩ _a _h₃ ↦ Subset.refl _ },
    ext Subtype.property fun _x _s h ↦
      let ⟨t, h, o, m⟩ := mem_nhds_iff.1 h
      ⟨⟨t, o⟩, m, h⟩⟩

/-- Replace the representation type of a `Ctop` realizer. -/
/-
**Ctop.Realizer.ofEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ctop.Realizer`。
形式化陈述：ofEquiv (F : Realizer α) (E : F.σ ≃ τ) : Realizer α
参数：F : Realizer α；E : F.σ ≃ τ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replace the representation type of a `Ctop` realizer.
-/
def ofEquiv (F : Realizer α) (E : F.σ ≃ τ) : Realizer α :=
  ⟨τ, F.F.ofEquiv E,
    ext' fun a s ↦
      F.mem_nhds.trans <|
        ⟨fun ⟨s, h⟩ ↦ ⟨E s, by simpa using h⟩, fun ⟨t, h⟩ ↦ ⟨E.symm t, by simpa using h⟩⟩⟩

@[simp]
/-
**Ctop.Realizer.ofEquiv_** 是 Mathlib 中的一个定理，位于命名空间 `Ctop.Realizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofEquiv_σ (F : Realizer α) (E : F.σ ≃ τ) : (F.ofEquiv E).σ = τ := rfl

@[simp]
/-
**Ctop.Realizer.ofEquiv_F** 是 Mathlib 中的一个定理，位于命名空间 `Ctop.Realizer`。
形式化陈述：ofEquiv_F (F : Realizer α) (E : F.σ ≃ τ) (s : τ) : (F.ofEquiv E).F s = F.F
 (E.symm s)
参数：F : Realizer α；E : F.σ ≃ τ；s : τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ctop.ofEquiv_val`：ofEquiv_val (E : σ ≃ τ) (F : Ctop α σ) (a : τ) : F.ofE
quiv E a = F (E.symm a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofEquiv_F (F : Realizer α) (E : F.σ ≃ τ) (s : τ) : (F.ofEquiv E).F s = F.F (E.symm s) := by
  delta ofEquiv; simp

/-- A realizer of the neighborhood of a point. -/
/-
**Ctop.Realizer.nhds** 是 Mathlib 中的一个定义，位于命名空间 `Ctop.Realizer`。
形式化陈述：{α : Type u_1} → [inst : TopologicalSpace α] → Ctop.Realizer α → (a : α) →
 (nhds a).Realizer
参数：a : α；nhds a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A realizer of the neighborhood of a point.
-/
protected def nhds (F : Realizer α) (a : α) : (𝓝 a).Realizer :=
  ⟨{ s : F.σ // a ∈ F.F s },
    { f := fun s ↦ F.F s.1
      pt := ⟨_, F.F.top_mem a⟩
      inf := fun ⟨x, h₁⟩ ⟨y, h₂⟩ ↦ ⟨_, F.F.inter_mem x y a ⟨h₁, h₂⟩⟩
      inf_le_left := fun ⟨x, h₁⟩ ⟨y, h₂⟩ _z h ↦ (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).1
      inf_le_right := fun ⟨x, h₁⟩ ⟨y, h₂⟩ _z h ↦ (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).2 },
    filter_eq <|
      Set.ext fun _x ↦
        ⟨fun ⟨⟨_s, as⟩, h⟩ ↦ mem_nhds_iff.2 ⟨_, h, F.isOpen _, as⟩, fun h ↦
          let ⟨s, h, as⟩ := F.mem_nhds.1 h
          ⟨⟨s, h⟩, as⟩⟩⟩

@[simp]
/-
**Ctop.Realizer.nhds_** 是 Mathlib 中的一个定理，位于命名空间 `Ctop.Realizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nhds_σ (F : Realizer α) (a : α) : (F.nhds a).σ = { s : F.σ // a ∈ F.F s } := rfl

@[simp]
/-
**Ctop.Realizer.nhds_F** 是 Mathlib 中的一个定理，位于命名空间 `Ctop.Realizer`。
形式化陈述：nhds_F (F : Realizer α) (a : α) (s) : (F.nhds a).F s = F.F s.1
参数：F : Realizer α；a : α；s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nhds_F (F : Realizer α) (a : α) (s) : (F.nhds a).F s = F.F s.1 := rfl
/-
**Ctop.Realizer.tendsto_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ctop.Realizer`。
形式化陈述：tendsto_nhds_iff {m : β -> α} {f : Filter β} (F : f.Realizer) (R : Realize
r α) {a : α} : Tendsto m f (𝓝 a) ↔ forall t, a in R.F t -> exists s, forall x in
 F.F s, m x in R.F t
参数：F : f.Realizer；R : Realizer α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.Realizer.tendsto_iff`：tendsto_iff (f : α -> β) {l₁ : Filter α} {l
₂ : Filter β} (L₁ : l₁.Realizer) (L₂ : l₂.Realizer) : Tendsto f l₁ l₂ ↔ forall b
, exists a, foral…
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
theorem tendsto_nhds_iff {m : β → α} {f : Filter β} (F : f.Realizer) (R : Realizer α) {a : α} :
    Tendsto m f (𝓝 a) ↔ ∀ t, a ∈ R.F t → ∃ s, ∀ x ∈ F.F s, m x ∈ R.F t :=
  (F.tendsto_iff _ (R.nhds a)).trans Subtype.forall

end Ctop.Realizer

/-- A `LocallyFinite.Realizer F f` is a realization that `f` is locally finite, namely it is a
choice of open sets from the basis of `F` such that they intersect only finitely many of the values
of `f`. -/
/-
**LocallyFinite.Realizer** 是 Mathlib 中的一个归纳类型，位于命名空间 `LocallyFinite`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → [inst : TopologicalSpace α] → Ctop.Rea
lizer α → (β → Set α) → Type (max (max u_1 u_2) u_5)
参数：β → Set α；max (max u_1 u_2) u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `LocallyFinite.Realizer F f` is a realization that `f` is locally finite, name
ly it is a
choice of open sets from the basis of `F` such that they intersect only finitely
 many of the values
of `f`.
-/
structure LocallyFinite.Realizer [TopologicalSpace α] (F : Ctop.Realizer α) (f : β → Set α) where
  bas : ∀ a, { s // a ∈ F.F s }
  sets : ∀ x : α, Fintype { i | (f i ∩ F.F (bas x)).Nonempty }
/-
**LocallyFinite.Realizer.to_locallyFinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LocallyFinite.Realizer.to_locallyFinite [TopologicalSpace α] {F : Ctop.Rea
lizer α} {f : β -> Set α} (R : LocallyFinite.Realizer F f) : LocallyFinite f
参数：R : LocallyFinite.Realizer F f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ctop.Realizer.mem_nhds`：∀ {α : Type u_1} [T : TopologicalSpace α] (F : C
top.Realizer α) {s : Set α} {a : α},   s ∈ nhds a ↔ ∃ b, a ∈ F.F.f b ∧ F.F.f b ⊆
 s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem LocallyFinite.Realizer.to_locallyFinite [TopologicalSpace α] {F : Ctop.Realizer α}
    {f : β → Set α} (R : LocallyFinite.Realizer F f) : LocallyFinite f := fun a ↦
  ⟨_, F.mem_nhds.2 ⟨(R.bas a).1, (R.bas a).2, Subset.rfl⟩, have := R.sets a; Set.toFinite _⟩
/-
**locallyFinite_iff_exists_realizer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：locallyFinite_iff_exists_realizer [TopologicalSpace α] (F : Ctop.Realizer 
α) {f : β -> Set α} : LocallyFinite f ↔ Nonempty (LocallyFinite.Realizer F f)
参数：F : Ctop.Realizer α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.axiom_of_choice`：∀ {α : Sort u} {β : α → Sort v} {r : (x : α) 
→ β x → Prop}, (∀ (x : α), ∃ y, r x y) → ∃ f, ∀ (x : α), r x (f x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ctop.Realizer.mem_nhds`：∀ {α : Type u_1} [T : TopologicalSpace α] (F : C
top.Realizer α) {s : Set α} {a : α},   s ∈ nhds a ↔ ∃ b, a ∈ F.F.f b ∧ F.F.f b ⊆
 s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LocallyFinite.Realizer.to_locallyFinite`：LocallyFinite.Realizer.to_local
lyFinite [TopologicalSpace α] {F : Ctop.Realizer α} {f : β -> Set α} (R : Locall
yFinite.Realizer F f) : Local…
-/
theorem locallyFinite_iff_exists_realizer [TopologicalSpace α] (F : Ctop.Realizer α)
    {f : β → Set α} : LocallyFinite f ↔ Nonempty (LocallyFinite.Realizer F f) :=
  ⟨fun h ↦
    let ⟨g, h₁⟩ := Classical.axiom_of_choice h
    let ⟨g₂, h₂⟩ :=
      Classical.axiom_of_choice fun x ↦
        show ∃ b : F.σ, x ∈ F.F b ∧ F.F b ⊆ g x from
          let ⟨h, _h'⟩ := h₁ x
          F.mem_nhds.1 h
    ⟨⟨fun x ↦ ⟨g₂ x, (h₂ x).1⟩, fun x ↦
        Finite.fintype <|
          let ⟨_h, h'⟩ := h₁ x
          h'.subset fun _i hi ↦ hi.mono (inter_subset_inter_right _ (h₂ x).2)⟩⟩,
    fun ⟨R⟩ ↦ R.to_locallyFinite⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] [Finite β] (F : Ctop.Realizer α) (f : β → Set α) :
    Nonempty (LocallyFinite.Realizer F f) :=
  (locallyFinite_iff_exists_realizer _).1 <| locallyFinite_of_finite _

/-- A `Compact.Realizer s` is a realization that `s` is compact, namely it is a
choice of finite open covers for each set family covering `s`. -/
/-
**Compact.Realizer** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Compact.Realizer [TopologicalSpace α] (s : Set α)
参数：s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Compact.Realizer s` is a realization that `s` is compact, namely it is a
choice of finite open covers for each set family covering `s`.
-/
def Compact.Realizer [TopologicalSpace α] (s : Set α) :=
  ∀ {f : Filter α} (F : f.Realizer) (x : F.σ), f ≠ ⊥ → F.F x ⊆ s → { a // a ∈ s ∧ 𝓝 a ⊓ f ≠ ⊥ }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] : Inhabited (Compact.Realizer (∅ : Set α)) :=
  ⟨fun {f} F x h hF ↦ by
    suffices f = ⊥ from absurd this h
    rw [← F.eq, eq_bot_iff]
    exact fun s _ ↦ ⟨x, hF.trans s.empty_subset⟩⟩
