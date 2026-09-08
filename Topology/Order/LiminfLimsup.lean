/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Order.Filter.CountableInter
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Order.Monotone

import Mathlib.Data.Fintype.Order
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Lemmas about liminf and limsup in an order topology.

## Main declarations

* `BoundedLENhdsClass`: Typeclass stating that neighborhoods are eventually bounded above.
* `BoundedGENhdsClass`: Typeclass stating that neighborhoods are eventually bounded below.

## Implementation notes

The same lemmas are true in `ℝ`, `ℝ × ℝ`, `ι → ℝ`, `EuclideanSpace ι ℝ`. To avoid code
duplication, we provide an ad hoc axiomatisation of the properties we need.
-/

public section

open Filter TopologicalSpace
open scoped Topology

universe u v

variable {ι α β R S : Type*} {π : ι → Type*}

/-- Ad hoc typeclass stating that neighborhoods are eventually bounded above. -/
/-
**BoundedLENhdsClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_7) → [Preorder α] → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ad hoc typeclass stating that neighborhoods are eventually bounded above.
-/
class BoundedLENhdsClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· ≤ ·)

/-- Ad hoc typeclass stating that neighborhoods are eventually bounded below. -/
/-
**BoundedGENhdsClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_7) → [Preorder α] → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ad hoc typeclass stating that neighborhoods are eventually bounded below.
-/
class BoundedGENhdsClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· ≥ ·)

section Preorder
variable [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]

section BoundedLENhdsClass
variable [BoundedLENhdsClass α] [BoundedLENhdsClass β] {f : Filter ι} {u : ι → α} {a : α}

/-
**isBounded_le_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· <= ·)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedLENhdsClass.isBounded_le_nhds`：∀ {α : Type u_7} {inst : Preorder 
α} {inst_1 : TopologicalSpace α} [self : BoundedLENhdsClass α] (a : α),   Filter
.IsBounded (fun x1 x2 => x…
-/
theorem isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· ≤ ·) :=
  BoundedLENhdsClass.isBounded_le_nhds _
/-
**Filter.Tendsto.isBoundedUnder_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.isBoundedUnder_le (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnde
r (· <= ·) u
参数：h : Tendsto u f (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {f g : Filter
 α}, f ≤ g → Filter.IsBounded r g → Filter.IsBounded r f
· 使用定理 `isBounded_le_nhds`：isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· <= ·)
-/
theorem Filter.Tendsto.isBoundedUnder_le (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· ≤ ·) u :=
  (isBounded_le_nhds a).mono h
/-
**Filter.Tendsto.bddAbove_range_of_cofinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.bddAbove_range_of_cofinite [IsDirectedOrder α] (h : Tendsto
 u cofinite (𝓝 a)) : BddAbove (Set.range u)
参数：h : Tendsto u cofinite (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.bddAbove_range_of_cofinite`：∀ {α : Type u_1} {β : 
Type u_2} [inst : Preorder β] [IsDirectedOrder β] {f : α → β},   Filter.IsBounde
dUnder (fun x1 x2 => x1 ≤ x2) Filter.c…
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
-/
theorem Filter.Tendsto.bddAbove_range_of_cofinite [IsDirectedOrder α]
    (h : Tendsto u cofinite (𝓝 a)) : BddAbove (Set.range u) :=
  h.isBoundedUnder_le.bddAbove_range_of_cofinite
/-
**Filter.Tendsto.bddAbove_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.bddAbove_range [IsDirectedOrder α] {u : Nat -> α} (h : Tend
sto u atTop (𝓝 a)) : BddAbove (Set.range u)
参数：h : Tendsto u atTop (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.bddAbove_range`：∀ {β : Type u_2} [inst : Preorder 
β] [IsDirectedOrder β] {f : ℕ → β},   Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x
2) Filter.atTop f → BddAbo…
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
-/
theorem Filter.Tendsto.bddAbove_range [IsDirectedOrder α] {u : ℕ → α}
    (h : Tendsto u atTop (𝓝 a)) : BddAbove (Set.range u) :=
  h.isBoundedUnder_le.bddAbove_range
/-
**isCobounded_ge_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCobounded_ge_nhds (a : α) : (𝓝 a).IsCobounded (· >= ·)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBounded.isCobounded_flip`：∀ {α : Type u_1} {r : α → α → Prop} {
f : Filter α} [IsTrans α r] [f.NeBot],   Filter.IsBounded r f → Filter.IsCobound
ed (flip r) f
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `isBounded_le_nhds`：isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· <= ·)
-/
theorem isCobounded_ge_nhds (a : α) : (𝓝 a).IsCobounded (· ≥ ·) :=
  (isBounded_le_nhds a).isCobounded_flip
/-
**Filter.Tendsto.isCoboundedUnder_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.isCoboundedUnder_ge [NeBot f] (h : Tendsto u f (𝓝 a)) : f.I
sCoboundedUnder (· >= ·) u
参数：h : Tendsto u f (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBounded.isCobounded_flip`：∀ {α : Type u_1} {r : α → α → Prop} {
f : Filter α} [IsTrans α r] [f.NeBot],   Filter.IsBounded r f → Filter.IsCobound
ed (flip r) f
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
-/
theorem Filter.Tendsto.isCoboundedUnder_ge [NeBot f] (h : Tendsto u f (𝓝 a)) :
    f.IsCoboundedUnder (· ≥ ·) u :=
  h.isBoundedUnder_le.isCobounded_flip
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedGENhdsClass αᵒᵈ := ⟨@isBounded_le_nhds α _ _ _⟩
/-
**Prod.instBoundedLENhdsClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instBoundedLENhdsClass : BoundedLENhdsClass (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isBounded_le_nhds`：isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· <= ·)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.Eventually.prod_mk`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {pa : α → Prop},   (∀ᶠ (x : α) in la, pa x) →     ∀ {lb : Filter β} {pb : β →
 Prop}, (∀ᶠ (y …
-/
instance Prod.instBoundedLENhdsClass : BoundedLENhdsClass (α × β) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨a, ha⟩ := isBounded_le_nhds x.1
  obtain ⟨b, hb⟩ := isBounded_le_nhds x.2
  rw [← @Prod.mk.eta _ _ x, nhds_prod_eq]
  exact ⟨(a, b), ha.prod_mk hb⟩
/-
**Pi.instBoundedLENhdsClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instBoundedLENhdsClass [Finite ι] [forall i, Preorder (π i)] [forall i,
 TopologicalSpace (π i)] [forall i, BoundedLENhdsClass (π i)] : BoundedLENhdsCla
ss (forall i, π i)
参数：π i；π i；π i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Filter.eventually_pi`：eventually_pi [Finite ι] (hf : forall i, forallᶠ x
 in f i, p i x) : forallᶠ x : forall i, α i in pi f, forall i, p i (x i)
· 使用定理 `isBounded_le_nhds`：isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· <= ·)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
instance Pi.instBoundedLENhdsClass [Finite ι] [∀ i, Preorder (π i)] [∀ i, TopologicalSpace (π i)]
    [∀ i, BoundedLENhdsClass (π i)] : BoundedLENhdsClass (∀ i, π i) := by
  refine ⟨fun x ↦ ?_⟩
  rw [nhds_pi]
  choose f hf using fun i ↦ isBounded_le_nhds (x i)
  exact ⟨f, eventually_pi hf⟩

end BoundedLENhdsClass

section BoundedGENhdsClass
variable [BoundedGENhdsClass α] [BoundedGENhdsClass β] {f : Filter ι} {u : ι → α} {a : α}

/-
**isBounded_ge_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· >= ·)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedGENhdsClass.isBounded_ge_nhds`：∀ {α : Type u_7} {inst : Preorder 
α} {inst_1 : TopologicalSpace α} [self : BoundedGENhdsClass α] (a : α),   Filter
.IsBounded (fun x1 x2 => x…
-/
theorem isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· ≥ ·) :=
  BoundedGENhdsClass.isBounded_ge_nhds _
/-
**Filter.Tendsto.isBoundedUnder_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.isBoundedUnder_ge (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnde
r (· >= ·) u
参数：h : Tendsto u f (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {f g : Filter
 α}, f ≤ g → Filter.IsBounded r g → Filter.IsBounded r f
· 使用定理 `isBounded_ge_nhds`：isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· >= ·)
-/
theorem Filter.Tendsto.isBoundedUnder_ge (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· ≥ ·) u :=
  (isBounded_ge_nhds a).mono h
/-
**Filter.Tendsto.bddBelow_range_of_cofinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.bddBelow_range_of_cofinite [IsCodirectedOrder α] (h : Tends
to u cofinite (𝓝 a)) : BddBelow (Set.range u)
参数：h : Tendsto u cofinite (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.bddBelow_range_of_cofinite`：∀ {α : Type u_1} {β : 
Type u_2} [inst : Preorder β] [IsCodirectedOrder β] {f : α → β},   Filter.IsBoun
dedUnder (fun x1 x2 => x2 ≤ x1) Filter…
· 使用定理 `Filter.Tendsto.isBoundedUnder_ge`：Filter.Tendsto.isBoundedUnder_ge (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· >= ·) u
-/
theorem Filter.Tendsto.bddBelow_range_of_cofinite [IsCodirectedOrder α]
    (h : Tendsto u cofinite (𝓝 a)) : BddBelow (Set.range u) :=
  h.isBoundedUnder_ge.bddBelow_range_of_cofinite
/-
**Filter.Tendsto.bddBelow_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.bddBelow_range [IsCodirectedOrder α] {u : Nat -> α} (h : Te
ndsto u atTop (𝓝 a)) : BddBelow (Set.range u)
参数：h : Tendsto u atTop (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.bddBelow_range`：∀ {β : Type u_2} [inst : Preorder 
β] [IsCodirectedOrder β] {f : ℕ → β},   Filter.IsBoundedUnder (fun x1 x2 => x2 ≤
 x1) Filter.atTop f → BddB…
· 使用定理 `Filter.Tendsto.isBoundedUnder_ge`：Filter.Tendsto.isBoundedUnder_ge (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· >= ·) u
-/
theorem Filter.Tendsto.bddBelow_range [IsCodirectedOrder α] {u : ℕ → α}
    (h : Tendsto u atTop (𝓝 a)) : BddBelow (Set.range u) :=
  h.isBoundedUnder_ge.bddBelow_range
/-
**isCobounded_le_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCobounded_le_nhds (a : α) : (𝓝 a).IsCobounded (· <= ·)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBounded.isCobounded_flip`：∀ {α : Type u_1} {r : α → α → Prop} {
f : Filter α} [IsTrans α r] [f.NeBot],   Filter.IsBounded r f → Filter.IsCobound
ed (flip r) f
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
· 使用定理 `isBounded_ge_nhds`：isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· >= ·)
-/
theorem isCobounded_le_nhds (a : α) : (𝓝 a).IsCobounded (· ≤ ·) :=
  (isBounded_ge_nhds a).isCobounded_flip
/-
**Filter.Tendsto.isCoboundedUnder_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.isCoboundedUnder_le [NeBot f] (h : Tendsto u f (𝓝 a)) : f.I
sCoboundedUnder (· <= ·) u
参数：h : Tendsto u f (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBounded.isCobounded_flip`：∀ {α : Type u_1} {r : α → α → Prop} {
f : Filter α} [IsTrans α r] [f.NeBot],   Filter.IsBounded r f → Filter.IsCobound
ed (flip r) f
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
· 使用定理 `Filter.Tendsto.isBoundedUnder_ge`：Filter.Tendsto.isBoundedUnder_ge (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· >= ·) u
-/
theorem Filter.Tendsto.isCoboundedUnder_le [NeBot f] (h : Tendsto u f (𝓝 a)) :
    f.IsCoboundedUnder (· ≤ ·) u :=
  h.isBoundedUnder_ge.isCobounded_flip
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedLENhdsClass αᵒᵈ := ⟨@isBounded_ge_nhds α _ _ _⟩
/-
**Prod.instBoundedGENhdsClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instBoundedGENhdsClass : BoundedGENhdsClass (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedLENhdsClass.isBounded_le_nhds`：∀ {α : Type u_7} {inst : Preorder 
α} {inst_1 : TopologicalSpace α} [self : BoundedLENhdsClass α] (a : α),   Filter
.IsBounded (fun x1 x2 => x…
· 使用定理 `instBoundedLENhdsClassOrderDual`：∀ {α : Type u_2} [inst : Preorder α] [i
nst_1 : TopologicalSpace α] [BoundedGENhdsClass α], BoundedLENhdsClass αᵒᵈ
-/
instance Prod.instBoundedGENhdsClass : BoundedGENhdsClass (α × β) :=
  ⟨(Prod.instBoundedLENhdsClass (α := αᵒᵈ) (β := βᵒᵈ)).isBounded_le_nhds⟩
/-
**Pi.instBoundedGENhdsClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instBoundedGENhdsClass [Finite ι] [forall i, Preorder (π i)] [forall i,
 TopologicalSpace (π i)] [forall i, BoundedGENhdsClass (π i)] : BoundedGENhdsCla
ss (forall i, π i)
参数：π i；π i；π i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedLENhdsClass.isBounded_le_nhds`：∀ {α : Type u_7} {inst : Preorder 
α} {inst_1 : TopologicalSpace α} [self : BoundedLENhdsClass α] (a : α),   Filter
.IsBounded (fun x1 x2 => x…
· 使用定理 `instBoundedLENhdsClassOrderDual`：∀ {α : Type u_2} [inst : Preorder α] [i
nst_1 : TopologicalSpace α] [BoundedGENhdsClass α], BoundedLENhdsClass αᵒᵈ
-/
instance Pi.instBoundedGENhdsClass [Finite ι] [∀ i, Preorder (π i)] [∀ i, TopologicalSpace (π i)]
    [∀ i, BoundedGENhdsClass (π i)] : BoundedGENhdsClass (∀ i, π i) :=
  ⟨(Pi.instBoundedLENhdsClass (π := fun i ↦ (π i)ᵒᵈ)).isBounded_le_nhds⟩

end BoundedGENhdsClass

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderTop.to_BoundedLENhdsClass [OrderTop α] : BoundedLENhdsClass α :=
  ⟨fun _a ↦ isBounded_le_of_top⟩

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderBot.to_BoundedGENhdsClass [OrderBot α] : BoundedGENhdsClass α :=
  ⟨fun _a ↦ isBounded_ge_of_bot⟩

end Preorder

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) BoundedLENhdsClass.of_closedIciTopology [LinearOrder α]
    [TopologicalSpace α] [ClosedIciTopology α] : BoundedLENhdsClass α :=
  ⟨fun a ↦ ((isTop_or_exists_gt a).elim fun h ↦ ⟨a, Eventually.of_forall h⟩) <|
    Exists.imp fun _b ↦ eventually_le_nhds⟩

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) BoundedGENhdsClass.of_closedIicTopology [LinearOrder α]
    [TopologicalSpace α] [ClosedIicTopology α] : BoundedGENhdsClass α :=
  inferInstanceAs <| BoundedGENhdsClass αᵒᵈᵒᵈ

section LiminfLimsup

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]

/-- If the liminf and the limsup of a filter coincide, then this filter converges to
their common value, at least if the filter is eventually bounded above and below. -/
/-
**le_nhds_of_limsSup_eq_limsInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_nhds_of_limsSup_eq_limsInf {f : Filter α} {a : α} (hl : f.IsBounded (· 
<= ·)) (hg : f.IsBounded (· >= ·)) (hs : f.limsSup = a) (hi : f.limsInf = a) : f
 <= 𝓝 a
参数：hl : f.IsBounded (· <= ·)；hg : f.IsBounded (· >= ·)；hs : f.limsSup = a；hi : f
.limsInf = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `Filter.gt_mem_sets_of_limsInf_gt`：gt_mem_sets_of_limsInf_gt : f.IsBounde
d (· >= ·) -> b < f.limsInf -> forallᶠ a in f, b < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.lt_mem_sets_of_limsSup_lt`：lt_mem_sets_of_limsSup_lt (h : f.IsBou
nded (· <= ·)) (l : f.limsSup < b) : forallᶠ a in f, a < b

--- 原说明 ---
If the liminf and the limsup of a filter coincide, then this filter converges to
their common value, at least if the filter is eventually bounded above and below
.
-/
theorem le_nhds_of_limsSup_eq_limsInf {f : Filter α} {a : α} (hl : f.IsBounded (· ≤ ·))
    (hg : f.IsBounded (· ≥ ·)) (hs : f.limsSup = a) (hi : f.limsInf = a) : f ≤ 𝓝 a :=
  tendsto_order.2 ⟨fun _ hb ↦ gt_mem_sets_of_limsInf_gt hg <| hi.symm ▸ hb,
    fun _ hb ↦ lt_mem_sets_of_limsSup_lt hl <| hs.symm ▸ hb⟩
/-
**limsSup_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：limsSup_nhds (a : α) : limsSup (𝓝 a) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_eq_of_forall_ge_of_forall_gt_exists_lt`：∀ {α : Type u_1} [inst : C
onditionallyCompleteLattice α] {s : Set α} {b : α},   s.Nonempty → (∀ a ∈ s, b ≤
 a) → (∀ (w : α), b < w → ∃ a ∈ s,…
· 使用定理 `isBounded_le_nhds`：isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· <= ·)
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `dense_or_discrete`：dense_or_discrete [LinearOrder α] (a₁ a₂ : α) : (exis
ts a, a₁ < a ∧ a < a₂) ∨ (forall a, a₁ < a -> a₂ <= a) ∧ forall a < a₂, a <= a₁
· 使用定理 `ge_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x ≤ a
· 使用定理 `Filter.sets_of_superset`：∀ {α : Type u_1} (self : Filter α) {x y : Set α
}, x ∈ self.sets → x ⊆ y → y ∈ self.sets
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
-/
theorem limsSup_nhds (a : α) : limsSup (𝓝 a) = a :=
  csInf_eq_of_forall_ge_of_forall_gt_exists_lt (isBounded_le_nhds a)
    (fun a' (h : { n : α | n ≤ a' } ∈ 𝓝 a) ↦ show a ≤ a' from @mem_of_mem_nhds _ _ a _ h)
    fun b (hba : a < b) ↦
    show ∃ c, { n : α | n ≤ c } ∈ 𝓝 a ∧ c < b from
      match dense_or_discrete a b with
      | Or.inl ⟨c, hac, hcb⟩ => ⟨c, ge_mem_nhds hac, hcb⟩
      | Or.inr ⟨_, h⟩ => ⟨a, (𝓝 a).sets_of_superset (gt_mem_nhds hba) h, hba⟩
/-
**limsInf_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：limsInf_nhds (a : α) : limsInf (𝓝 a) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `limsSup_nhds`：limsSup_nhds (a : α) : limsSup (𝓝 a) = a
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem limsInf_nhds (a : α) : limsInf (𝓝 a) = a :=
  limsSup_nhds (α := αᵒᵈ) a

/-- If a filter is converging, its limsup coincides with its limit. -/
/-
**limsInf_eq_of_le_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：limsInf_eq_of_le_nhds {f : Filter α} {a : α} [NeBot f] (h : f <= 𝓝 a) : f.
limsInf = a
参数：h : f <= 𝓝 a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {f g : Filter
 α}, f ≤ g → Filter.IsBounded r g → Filter.IsBounded r f
· 使用定理 `isBounded_ge_nhds`：isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· >= ·)
· 使用定理 `BoundedGENhdsClass.of_closedIicTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIicTopology α], BoundedGENhdsClass
 α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `isBounded_le_nhds`：isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· <= ·)
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.limsInf_le_limsSup`：limsInf_le_limsSup {f : Filter α} [NeBot f] (
h₁ : f.IsBounded (· <= ·)
· 使用定理 `Filter.limsSup_le_limsSup_of_le`：limsSup_le_limsSup_of_le {f g : Filter 
α} (h : f <= g) (hf : f.IsCobounded (· <= ·)
· 使用定理 `Filter.IsBounded.isCobounded_flip`：∀ {α : Type u_1} {r : α → α → Prop} {
f : Filter α} [IsTrans α r] [f.NeBot],   Filter.IsBounded r f → Filter.IsCobound
ed (flip r) f
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
· 使用定理 `limsSup_nhds`：limsSup_nhds (a : α) : limsSup (𝓝 a) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `limsInf_nhds`：limsInf_nhds (a : α) : limsInf (𝓝 a) = a
· 使用定理 `Filter.limsInf_le_limsInf_of_le`：limsInf_le_limsInf_of_le {f g : Filter 
α} (h : g <= f) (hf : f.IsBounded (· >= ·)
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2

--- 原说明 ---
If a filter is converging, its limsup coincides with its limit.
-/
theorem limsInf_eq_of_le_nhds {f : Filter α} {a : α} [NeBot f] (h : f ≤ 𝓝 a) : f.limsInf = a :=
  have hb_ge : IsBounded (· ≥ ·) f := (isBounded_ge_nhds a).mono h
  have hb_le : IsBounded (· ≤ ·) f := (isBounded_le_nhds a).mono h
  le_antisymm
    (calc
      f.limsInf ≤ f.limsSup := limsInf_le_limsSup hb_le hb_ge
      _ ≤ (𝓝 a).limsSup := limsSup_le_limsSup_of_le h hb_ge.isCobounded_flip (isBounded_le_nhds a)
      _ = a := limsSup_nhds a)
    (calc
      a = (𝓝 a).limsInf := (limsInf_nhds a).symm
      _ ≤ f.limsInf := limsInf_le_limsInf_of_le h (isBounded_ge_nhds a) hb_le.isCobounded_flip)

set_option backward.isDefEq.respectTransparency false in
/-- If a filter is converging, its liminf coincides with its limit. -/
/-
**limsSup_eq_of_le_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：limsSup_eq_of_le_nhds {f : Filter α} {a : α} [NeBot f] (h : f <= 𝓝 a) : f.
limsSup = a
参数：h : f <= 𝓝 a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `limsInf_eq_of_le_nhds`：limsInf_eq_of_le_nhds {f : Filter α} {a : α} [NeB
ot f] (h : f <= 𝓝 a) : f.limsInf = a
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ

--- 原说明 ---
If a filter is converging, its liminf coincides with its limit.
-/
theorem limsSup_eq_of_le_nhds {f : Filter α} {a : α} [NeBot f] (h : f ≤ 𝓝 a) : f.limsSup = a :=
  limsInf_eq_of_le_nhds (α := αᵒᵈ) h

/-- If a function has a limit, then its limsup coincides with its limit. -/
/-
**Filter.Tendsto.limsup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.limsup_eq {f : Filter β} {u : β -> α} {a : α} [NeBot f] (h 
: Tendsto u f (𝓝 a)) : limsup u f = a
参数：h : Tendsto u f (𝓝 a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `limsSup_eq_of_le_nhds`：limsSup_eq_of_le_nhds {f : Filter α} {a : α} [NeB
ot f] (h : f <= 𝓝 a) : f.limsSup = a

--- 原说明 ---
If a function has a limit, then its limsup coincides with its limit.
-/
theorem Filter.Tendsto.limsup_eq {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : limsup u f = a :=
  limsSup_eq_of_le_nhds h

/-- If a function has a limit, then its liminf coincides with its limit. -/
/-
**Filter.Tendsto.liminf_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.liminf_eq {f : Filter β} {u : β -> α} {a : α} [NeBot f] (h 
: Tendsto u f (𝓝 a)) : liminf u f = a
参数：h : Tendsto u f (𝓝 a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `limsInf_eq_of_le_nhds`：limsInf_eq_of_le_nhds {f : Filter α} {a : α} [NeB
ot f] (h : f <= 𝓝 a) : f.limsInf = a

--- 原说明 ---
If a function has a limit, then its liminf coincides with its limit.
-/
theorem Filter.Tendsto.liminf_eq {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : liminf u f = a :=
  limsInf_eq_of_le_nhds h

/-- The `limsSup` of a filter `f` is a cluster point of `f`. -/
/-
**ClusterPt.limsSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ClusterPt.limsSup {f : Filter α} [NeBot f] (hc : f.IsCobounded (· <= ·)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.clusterPt_iff_frequently`：Filter.HasBasis.clusterPt_iff_
frequently {ι} {p : ι -> Prop} {s : ι -> Set X} {F : Filter X} (hx : (𝓝 x).HasBa
sis p s) : ClusterPt x F ↔ for…
· 使用定理 `nhds_top_basis`：nhds_top_basis [TopologicalSpace α] [LinearOrder α] [Ord
erTop α] [OrderTopology α] [Nontrivial α] : (𝓝 ⊤).HasBasis (fun a : α => a < ⊤) 
fun …
· 使用定理 `Filter.frequently_lt_of_lt_limsSup`：frequently_lt_of_lt_limsSup {f : Fil
ter α} [ConditionallyCompleteLinearOrder α] {a : α} (hf : f.IsCobounded (· <= ·)
· 使用定理 `nhds_bot_basis`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [inst_2 : OrderBot α] [OrderTopology α]   [Nontrivial α], (nhds ⊥).H
asBa…
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `Filter.lt_mem_sets_of_limsSup_lt`：lt_mem_sets_of_limsSup_lt (h : f.IsBou
nded (· <= ·)) (l : f.limsSup < b) : forallᶠ a in f, a < b
· 使用定理 `nhds_basis_Ioo'`：nhds_basis_Ioo' {a : α} (hl : exists l, l < a) (hu : ex
ists u, a < u) : (𝓝 a).HasBasis (fun b : α × α => b.1 < a ∧ a < b.2) fun b => Io
o b.1…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.eq_top_of_neBot`：eq_top_of_neBot [Subsingleton α] (l : Filter α) 
[NeBot l] : l = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
The `limsSup` of a filter `f` is a cluster point of `f`.
-/
theorem ClusterPt.limsSup {f : Filter α} [NeBot f]
    (hc : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (hb : f.IsBounded (· ≤ ·) := by isBoundedDefault) : ClusterPt f.limsSup f := by
  by_cases! hn : Nontrivial α
  · by_cases! htop : ∀ x, x ≤ f.limsSup
    · let : OrderTop α := { top := f.limsSup, le_top := htop }
      exact nhds_top_basis.clusterPt_iff_frequently |>.mpr fun a => frequently_lt_of_lt_limsSup hc
    · by_cases! hbot : ∀ x, f.limsSup ≤ x
      · let : OrderBot α := { bot := f.limsSup, bot_le := hbot }
        refine nhds_bot_basis.clusterPt_iff_frequently |>.mpr fun a h => ?_
        exact lt_mem_sets_of_limsSup_lt hb h |>.frequently
      · refine (nhds_basis_Ioo' hbot htop).clusterPt_iff_frequently |>.mpr fun a ⟨hl, hg⟩ => ?_
        exact frequently_lt_of_lt_limsSup hc hl |>.and_eventually <| lt_mem_sets_of_limsSup_lt hb hg
  · simp_all [ClusterPt, Filter.eq_top_of_neBot]

set_option backward.isDefEq.respectTransparency false in
/-- The `limsInf` of a filter `f` is a cluster point of `f`. -/
/-
**ClusterPt.limsInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ClusterPt.limsInf {f : Filter α} [NeBot f] (hc : f.IsCobounded (· >= ·)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.limsSup`：ClusterPt.limsSup {f : Filter α} [NeBot f] (hc : f.Is
Cobounded (· <= ·)
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ

--- 原说明 ---
The `limsInf` of a filter `f` is a cluster point of `f`.
-/
theorem ClusterPt.limsInf {f : Filter α} [NeBot f]
    (hc : f.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (hb : f.IsBounded (· ≥ ·) := by isBoundedDefault) : ClusterPt f.limsInf f :=
  ClusterPt.limsSup (α := αᵒᵈ) hc hb

/-- Every cluster point `x` of a filter `f` is less than or equal to `f.limsSup`. -/
/-
**ClusterPt.le_limsSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ClusterPt.le_limsSup {f : Filter α} {x : α} (hx : ClusterPt x f) (hb : f.I
sBounded (· <= ·)
参数：hx : ClusterPt x f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `limsSup_eq_of_le_nhds`：limsSup_eq_of_le_nhds {f : Filter α} {a : α} [NeB
ot f] (h : f <= 𝓝 a) : f.limsSup = a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Filter.limsSup_le_limsSup_of_le`：limsSup_le_limsSup_of_le {f g : Filter 
α} (h : f <= g) (hf : f.IsCobounded (· <= ·)
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Filter.IsBounded.isCobounded_le`：∀ {α : Type u_1} {f : Filter α} [inst :
 Preorder α] [f.NeBot],   Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f → Filter.IsC
obounded (fun x1 x2 =…
· 使用定理 `Filter.IsBounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {f g : Filter
 α}, f ≤ g → Filter.IsBounded r g → Filter.IsBounded r f
· 使用定理 `isBounded_ge_nhds`：isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· >= ·)
· 使用定理 `BoundedGENhdsClass.of_closedIicTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIicTopology α], BoundedGENhdsClass
 α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α

--- 原说明 ---
Every cluster point `x` of a filter `f` is less than or equal to `f.limsSup`.
-/
theorem ClusterPt.le_limsSup {f : Filter α} {x : α} (hx : ClusterPt x f)
    (hb : f.IsBounded (· ≤ ·) := by isBoundedDefault) :
    x ≤ f.limsSup := by
  simp only [ClusterPt] at hx
  have : (𝓝 x ⊓ f).limsSup = x := limsSup_eq_of_le_nhds inf_le_left
  refine this ▸ limsSup_le_limsSup_of_le inf_le_right ?_ hb
  exact (IsBounded.mono inf_le_left (isBounded_ge_nhds x)).isCobounded_le

/-- Every cluster point `x` of a filter `f` is greater than or equal to `f.limsInf`. -/
/-
**ClusterPt.limsInf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ClusterPt.limsInf_le {f : Filter α} {x : α} (hx : ClusterPt x f) (hb : f.I
sBounded (· >= ·)
参数：hx : ClusterPt x f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.le_limsSup`：ClusterPt.le_limsSup {f : Filter α} {x : α} (hx : 
ClusterPt x f) (hb : f.IsBounded (· <= ·)
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ

--- 原说明 ---
Every cluster point `x` of a filter `f` is greater than or equal to `f.limsInf`.
-/
theorem ClusterPt.limsInf_le {f : Filter α} {x : α} (hx : ClusterPt x f)
    (hb : f.IsBounded (· ≥ ·) := by isBoundedDefault) :
    f.limsInf ≤ x :=
  hx.le_limsSup (α := αᵒᵈ)

/-- The `limsSup` of a filter `f` is the greatest cluster point of `f`. -/
/-
**isGreatest_clusterPt_limsSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGreatest_clusterPt_limsSup {f : Filter α} [NeBot f] (hc : f.IsCobounded 
(· <= ·)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.limsSup`：ClusterPt.limsSup {f : Filter α} [NeBot f] (hc : f.Is
Cobounded (· <= ·)
· 使用定理 `ClusterPt.le_limsSup`：ClusterPt.le_limsSup {f : Filter α} {x : α} (hx : 
ClusterPt x f) (hb : f.IsBounded (· <= ·)

--- 原说明 ---
The `limsSup` of a filter `f` is the greatest cluster point of `f`.
-/
theorem isGreatest_clusterPt_limsSup {f : Filter α} [NeBot f]
    (hc : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (hb : f.IsBounded (· ≤ ·) := by isBoundedDefault) :
    IsGreatest {x | ClusterPt x f} f.limsSup :=
  ⟨ClusterPt.limsSup, fun a ha => ha.le_limsSup⟩

set_option backward.isDefEq.respectTransparency false in
/-- The `limsInf` of a filter `f` is the least cluster point of `f`. -/
/-
**isLeast_clusterPt_limsInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLeast_clusterPt_limsInf {f : Filter α} [NeBot f] (hc : f.IsCobounded (· 
>= ·)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isGreatest_clusterPt_limsSup`：isGreatest_clusterPt_limsSup {f : Filter α
} [NeBot f] (hc : f.IsCobounded (· <= ·)
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ

--- 原说明 ---
The `limsInf` of a filter `f` is the least cluster point of `f`.
-/
theorem isLeast_clusterPt_limsInf {f : Filter α} [NeBot f]
    (hc : f.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (hb : f.IsBounded (· ≥ ·) := by isBoundedDefault) :
    IsLeast {x | ClusterPt x f} f.limsInf :=
  isGreatest_clusterPt_limsSup (α := αᵒᵈ)

/-- The `limsup` of a function `u` along a filter `f` is a cluster point of `u` along `f`. -/
/-
**MapClusterPt.limsup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MapClusterPt.limsup {u : β -> α} {f : Filter β} [NeBot f] (hc : IsCobounde
dUnder (· <= ·) f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.limsSup`：ClusterPt.limsSup {f : Filter α} [NeBot f] (hc : f.Is
Cobounded (· <= ·)

--- 原说明 ---
The `limsup` of a function `u` along a filter `f` is a cluster point of `u` alon
g `f`.
-/
theorem MapClusterPt.limsup {u : β → α} {f : Filter β} [NeBot f]
    (hc : IsCoboundedUnder (· ≤ ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    MapClusterPt (f.limsup u) f u :=
  ClusterPt.limsSup

/-- The `liminf` of a function `u` along a filter `f` is a cluster point of `u` along `f`. -/
/-
**MapClusterPt.liminf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MapClusterPt.liminf {u : β -> α} {f : Filter β} [NeBot f] (hc : IsCobounde
dUnder (· >= ·) f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.limsInf`：ClusterPt.limsInf {f : Filter α} [NeBot f] (hc : f.Is
Cobounded (· >= ·)

--- 原说明 ---
The `liminf` of a function `u` along a filter `f` is a cluster point of `u` alon
g `f`.
-/
theorem MapClusterPt.liminf {u : β → α} {f : Filter β} [NeBot f]
    (hc : IsCoboundedUnder (· ≥ ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· ≥ ·) f u := by isBoundedDefault) :
    MapClusterPt (liminf u f) f u :=
  ClusterPt.limsInf

/-- Every cluster point `x` of a function `u` along a filter `f` is less than or equal to
`limsup u f`. -/
/-
**MapClusterPt.le_limsup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MapClusterPt.le_limsup {u : β -> α} {f : Filter β} {x : α} (hx : MapCluste
rPt x f u) (hb : IsBoundedUnder (· <= ·) f u
参数：hx : MapClusterPt x f u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.le_limsSup`：ClusterPt.le_limsSup {f : Filter α} {x : α} (hx : 
ClusterPt x f) (hb : f.IsBounded (· <= ·)

--- 原说明 ---
Every cluster point `x` of a function `u` along a filter `f` is less than or equ
al to
`limsup u f`.
-/
theorem MapClusterPt.le_limsup {u : β → α} {f : Filter β}
    {x : α} (hx : MapClusterPt x f u) (hb : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    x ≤ f.limsup u :=
  hx.le_limsSup

/-- Every cluster point `x` of a function `u` along a filter `f` is greater than or equal to
`liminf u f`. -/
/-
**MapClusterPt.liminf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MapClusterPt.liminf_le {u : β -> α} {f : Filter β} {x : α} (hx : MapCluste
rPt x f u) (hb : IsBoundedUnder (· >= ·) f u
参数：hx : MapClusterPt x f u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.limsInf_le`：ClusterPt.limsInf_le {f : Filter α} {x : α} (hx : 
ClusterPt x f) (hb : f.IsBounded (· >= ·)

--- 原说明 ---
Every cluster point `x` of a function `u` along a filter `f` is greater than or 
equal to
`liminf u f`.
-/
theorem MapClusterPt.liminf_le {u : β → α} {f : Filter β}
    {x : α} (hx : MapClusterPt x f u) (hb : IsBoundedUnder (· ≥ ·) f u := by isBoundedDefault) :
    f.liminf u ≤ x :=
  hx.limsInf_le

/-- The `limsup` of a function `u` along a filter `f` is the greatest cluster point of `u` along
`f`. -/
/-
**isGreatest_mapClusterPt_limsup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGreatest_mapClusterPt_limsup {u : β -> α} {f : Filter β} [NeBot f] (hc :
 IsCoboundedUnder (· <= ·) f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isGreatest_clusterPt_limsSup`：isGreatest_clusterPt_limsSup {f : Filter α
} [NeBot f] (hc : f.IsCobounded (· <= ·)

--- 原说明 ---
The `limsup` of a function `u` along a filter `f` is the greatest cluster point 
of `u` along
`f`.
-/
theorem isGreatest_mapClusterPt_limsup {u : β → α} {f : Filter β} [NeBot f]
    (hc : IsCoboundedUnder (· ≤ ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    IsGreatest {x | MapClusterPt x f u} (limsup u f) :=
  isGreatest_clusterPt_limsSup

/-- The `liminf` of a function `u` along a filter `f` is the least cluster point of `u` along
`f`. -/
/-
**isLeast_mapClusterPt_liminf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLeast_mapClusterPt_liminf {u : β -> α} {f : Filter β} [NeBot f] (hc : Is
CoboundedUnder (· >= ·) f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLeast_clusterPt_limsInf`：isLeast_clusterPt_limsInf {f : Filter α} [NeB
ot f] (hc : f.IsCobounded (· >= ·)

--- 原说明 ---
The `liminf` of a function `u` along a filter `f` is the least cluster point of 
`u` along
`f`.
-/
theorem isLeast_mapClusterPt_liminf {u : β → α} {f : Filter β} [NeBot f]
    (hc : IsCoboundedUnder (· ≥ ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· ≥ ·) f u := by isBoundedDefault) :
    IsLeast {x | MapClusterPt x f u} (liminf u f) :=
  isLeast_clusterPt_limsInf

/-- If the liminf and the limsup of a function coincide, then the limit of the function
exists and has the same value. -/
/-
**tendsto_of_liminf_eq_limsup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_of_liminf_eq_limsup {f : Filter β} {u : β -> α} {a : α} (hinf : li
minf u f = a) (hsup : limsup u f = a) (h : f.IsBoundedUnder (· <= ·) u
参数：hinf : liminf u f = a；hsup : limsup u f = a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_nhds_of_limsSup_eq_limsInf`：le_nhds_of_limsSup_eq_limsInf {f : Filter
 α} {a : α} (hl : f.IsBounded (· <= ·)) (hg : f.IsBounded (· >= ·)) (hs : f.lims
Sup = a) (hi : f.li…

--- 原说明 ---
If the liminf and the limsup of a function coincide, then the limit of the funct
ion
exists and has the same value.
-/
theorem tendsto_of_liminf_eq_limsup {f : Filter β} {u : β → α} {a : α} (hinf : liminf u f = a)
    (hsup : limsup u f = a) (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) : Tendsto u f (𝓝 a) :=
  le_nhds_of_limsSup_eq_limsInf h h' hsup hinf

/-- If a number `a` is less than or equal to the `liminf` of a function `f` at some filter
and is greater than or equal to the `limsup` of `f`, then `f` tends to `a` along this filter. -/
/-
**tendsto_of_le_liminf_of_limsup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_of_le_liminf_of_limsup_le {f : Filter β} {u : β -> α} {a : α} (hin
f : a <= liminf u f) (hsup : limsup u f <= a) (h : f.IsBoundedUnder (· <= ·) u
参数：hinf : a <= liminf u f；hsup : limsup u f <= a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `Filter.tendsto_bot`：tendsto_bot {f : α -> β} {l : Filter β} : Tendsto f 
⊥ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendsto_of_liminf_eq_limsup`：tendsto_of_liminf_eq_limsup {f : Filter β} 
{u : β -> α} {a : α} (hinf : liminf u f = a) (hsup : limsup u f = a) (h : f.IsBo
undedUnder (· <= …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Filter.liminf_le_limsup`：liminf_le_limsup {f : Filter β} [NeBot f] {u : 
β -> α} (h : f.IsBoundedUnder (· <= ·) u

--- 原说明 ---
If a number `a` is less than or equal to the `liminf` of a function `f` at some 
filter
and is greater than or equal to the `limsup` of `f`, then `f` tends to `a` along
 this filter.
-/
theorem tendsto_of_le_liminf_of_limsup_le {f : Filter β} {u : β → α} {a : α} (hinf : a ≤ liminf u f)
    (hsup : limsup u f ≤ a) (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) : Tendsto u f (𝓝 a) := by
  rcases f.eq_or_neBot with rfl | _
  · exact tendsto_bot
  · exact tendsto_of_liminf_eq_limsup (le_antisymm (le_trans (liminf_le_limsup h h') hsup) hinf)
      (le_antisymm hsup (le_trans hinf (liminf_le_limsup h h'))) h h'

/-- Assume that, for any `a < b`, a sequence cannot be infinitely many times below `a` and
above `b`. If it is also ultimately bounded above and below, then it has to converge. This even
works if `a` and `b` are restricted to a dense subset.
-/
/-
**tendsto_of_no_upcrossings** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_of_no_upcrossings [DenselyOrdered α] {f : Filter β} {u : β -> α} {
s : Set α} (hs : Dense s) (H : forall a in s, forall b in s, a < b -> ¬((existsᶠ
 n in f, u n < a) ∧ existsᶠ n in f, b < u n)) (h : f.IsBoundedUnder (· <= ·) u
参数：hs : Dense s；H : forall a in s, forall b in s, a < b -> ¬((existsᶠ n in f, u 
n < a) ∧ existsᶠ n in f, b < u n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `Filter.tendsto_bot`：tendsto_bot {f : α -> β} {l : Filter β} : Tendsto f 
⊥ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendsto_of_le_liminf_of_limsup_le`：tendsto_of_le_liminf_of_limsup_le {f 
: Filter β} {u : β -> α} {a : α} (hinf : a <= liminf u f) (hsup : limsup u f <= 
a) (h : f.IsBoundedUnde…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `dense_iff_inter_open`：dense_iff_inter_open : Dense s ↔ forall U, IsOpen 
U -> U.Nonempty -> (U inter s).Nonempty
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
· 使用定理 `Filter.frequently_lt_of_liminf_lt`：frequently_lt_of_liminf_lt {b : β} (h
u : f.IsCoboundedUnder (· >= ·) u
· 使用定理 `Filter.IsBounded.isCobounded_ge`：∀ {α : Type u_1} {f : Filter α} [inst :
 Preorder α] [f.NeBot],   Filter.IsBounded (fun x1 x2 => x1 ≤ x2) f → Filter.IsC
obounded (fun x1 x2 =…
· 使用定理 `Filter.frequently_lt_of_lt_limsup`：frequently_lt_of_lt_limsup {b : β} (h
u : f.IsCoboundedUnder (· <= ·) u
· 使用定理 `Filter.IsBounded.isCobounded_le`：∀ {α : Type u_1} {f : Filter α} [inst :
 Preorder α] [f.NeBot],   Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f → Filter.IsC
obounded (fun x1 x2 =…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
Assume that, for any `a < b`, a sequence cannot be infinitely many times below `
a` and
above `b`. If it is also ultimately bounded above and below, then it has to conv
erge. This even
works if `a` and `b` are restricted to a dense subset.
-/
theorem tendsto_of_no_upcrossings [DenselyOrdered α] {f : Filter β} {u : β → α} {s : Set α}
    (hs : Dense s) (H : ∀ a ∈ s, ∀ b ∈ s, a < b → ¬((∃ᶠ n in f, u n < a) ∧ ∃ᶠ n in f, b < u n))
    (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    ∃ c : α, Tendsto u f (𝓝 c) := by
  rcases f.eq_or_neBot with rfl | hbot
  · exact ⟨sInf ∅, tendsto_bot⟩
  refine ⟨limsup u f, ?_⟩
  apply tendsto_of_le_liminf_of_limsup_le _ le_rfl h h'
  by_contra! hlt
  obtain ⟨a, ⟨⟨la, au⟩, as⟩⟩ : ∃ a, (f.liminf u < a ∧ a < f.limsup u) ∧ a ∈ s :=
    dense_iff_inter_open.1 hs (Set.Ioo (f.liminf u) (f.limsup u)) isOpen_Ioo
      (Set.nonempty_Ioo.2 hlt)
  obtain ⟨b, ⟨⟨ab, bu⟩, bs⟩⟩ : ∃ b, (a < b ∧ b < f.limsup u) ∧ b ∈ s :=
    dense_iff_inter_open.1 hs (Set.Ioo a (f.limsup u)) isOpen_Ioo (Set.nonempty_Ioo.2 au)
  have A : ∃ᶠ n in f, u n < a := frequently_lt_of_liminf_lt (IsBounded.isCobounded_ge h) la
  have B : ∃ᶠ n in f, b < u n := frequently_lt_of_lt_limsup (IsBounded.isCobounded_le h') bu
  exact H a as b bs ab ⟨A, B⟩

variable [FirstCountableTopology α] {f : Filter α}
/-
**exists_seq_tendsto_limsSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_tendsto_limsSup [NeBot f] [IsCountablyGenerated f] (hc : f.IsCo
bounded (· <= ·)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.exists_seq_tendsto`：∀ {α : Type u} [t : TopologicalSpace α] [F
irstCountableTopology α] {x : α} {f : Filter α} [f.IsCountablyGenerated],   Clus
terPt x f → ∃ ψ, F…
· 使用定理 `ClusterPt.limsSup`：ClusterPt.limsSup {f : Filter α} [NeBot f] (hc : f.Is
Cobounded (· <= ·)
-/
theorem exists_seq_tendsto_limsSup [NeBot f] [IsCountablyGenerated f]
    (hc : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (hb : f.IsBounded (· ≤ ·) := by isBoundedDefault) :
    ∃ x : ℕ → α, Tendsto x atTop (𝓝 f.limsSup) ∧ Tendsto x atTop f :=
  (ClusterPt.limsSup).exists_seq_tendsto
/-
**exists_seq_tendsto_limsInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_tendsto_limsInf [NeBot f] [IsCountablyGenerated f] (hc : f.IsCo
bounded (· >= ·)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClusterPt.exists_seq_tendsto`：∀ {α : Type u} [t : TopologicalSpace α] [F
irstCountableTopology α] {x : α} {f : Filter α} [f.IsCountablyGenerated],   Clus
terPt x f → ∃ ψ, F…
· 使用定理 `ClusterPt.limsInf`：ClusterPt.limsInf {f : Filter α} [NeBot f] (hc : f.Is
Cobounded (· >= ·)
-/
theorem exists_seq_tendsto_limsInf [NeBot f] [IsCountablyGenerated f]
    (hc : f.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (hb : f.IsBounded (· ≥ ·) := by isBoundedDefault) :
    ∃ x : ℕ → α, Tendsto x atTop (𝓝 f.limsInf) ∧ Tendsto x atTop f :=
  (ClusterPt.limsInf).exists_seq_tendsto

variable {f : Filter β}
/-
**exists_seq_tendsto_limsup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_tendsto_limsup [NeBot f] [IsCountablyGenerated f] {u : β -> α} 
(hc : IsCoboundedUnder (· <= ·) f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MapClusterPt.exists_seq_tendsto`：∀ {α : Type u} [t : TopologicalSpace α]
 [FirstCountableTopology α] {ι : Type u_1} {f : Filter ι}   [f.IsCountablyGenera
ted] {x : α} {u : ι →…
· 使用定理 `MapClusterPt.limsup`：MapClusterPt.limsup {u : β -> α} {f : Filter β} [Ne
Bot f] (hc : IsCoboundedUnder (· <= ·) f u
-/
theorem exists_seq_tendsto_limsup [NeBot f] [IsCountablyGenerated f] {u : β → α}
    (hc : IsCoboundedUnder (· ≤ ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    ∃ x : ℕ → β, Tendsto (u ∘ x) atTop (𝓝 (limsup u f)) ∧ Tendsto x atTop f :=
  (MapClusterPt.limsup).exists_seq_tendsto
/-
**exists_seq_tendsto_liminf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_tendsto_liminf [NeBot f] {u : β -> α} [IsCountablyGenerated f] 
(hc : IsCoboundedUnder (· >= ·) f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MapClusterPt.exists_seq_tendsto`：∀ {α : Type u} [t : TopologicalSpace α]
 [FirstCountableTopology α] {ι : Type u_1} {f : Filter ι}   [f.IsCountablyGenera
ted] {x : α} {u : ι →…
· 使用定理 `MapClusterPt.liminf`：MapClusterPt.liminf {u : β -> α} {f : Filter β} [Ne
Bot f] (hc : IsCoboundedUnder (· >= ·) f u
-/
theorem exists_seq_tendsto_liminf [NeBot f] {u : β → α} [IsCountablyGenerated f]
    (hc : IsCoboundedUnder (· ≥ ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· ≥ ·) f u := by isBoundedDefault) :
    ∃ x : ℕ → β, Tendsto (u ∘ x) atTop (𝓝 (liminf u f)) ∧ Tendsto x atTop f :=
  (MapClusterPt.liminf).exists_seq_tendsto

variable [CountableInterFilter f] {u : β → α}
/-
**eventually_le_limsup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_le_limsup (hf : IsBoundedUnder (· <= ·) f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eventually_le_const_iff_forall_gt_eventually_lt_const`：eventually_le_con
st_iff_forall_gt_eventually_lt_const [FirstCountableTopology α] {l : Filter γ} [
CountableInterFilter l] {f : γ -> α} {a : α…
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
-/
theorem eventually_le_limsup (hf : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    ∀ᶠ b in f, u b ≤ f.limsup u := by
  rw [eventually_le_const_iff_forall_gt_eventually_lt_const]
  exact fun _ hc ↦ eventually_lt_of_limsup_lt hc
/-
**eventually_liminf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_liminf_le (hf : IsBoundedUnder (· >= ·) f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_le_limsup`：eventually_le_limsup (hf : IsBoundedUnder (· <= ·)
 f u
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instFirstCountableTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalS
pace α] [h : FirstCountableTopology α], FirstCountableTopology αᵒᵈ
-/
theorem eventually_liminf_le (hf : IsBoundedUnder (· ≥ ·) f u := by isBoundedDefault) :
    ∀ᶠ b in f, f.liminf u ≤ u b :=
  eventually_le_limsup (α := αᵒᵈ) hf

end ConditionallyCompleteLinearOrder

section CompleteLinearOrder

variable [CompleteLinearOrder α] [TopologicalSpace α] [FirstCountableTopology α] [OrderTopology α]
  {f : Filter β} [CountableInterFilter f] {u : β → α}

@[simp]
/-
**limsup_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：limsup_eq_bot : f.limsup u = ⊥ ↔ u =ᶠ[f] ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `eventually_le_limsup`：eventually_le_limsup (hf : IsBoundedUnder (· <= ·)
 f u
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_congr`：limsup_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u 
f = limsu…
· 使用定理 `Filter.limsup_const_bot`：limsup_const_bot {f : Filter β} : limsup (fun _
 : β => (⊥ : α)) f = (⊥ : α)
-/
theorem limsup_eq_bot : f.limsup u = ⊥ ↔ u =ᶠ[f] ⊥ :=
  ⟨fun h =>
    (EventuallyLE.trans eventually_le_limsup <| Eventually.of_forall fun _ => h.le).mono fun _ hx =>
      le_antisymm hx bot_le,
    fun h => by
    rw [limsup_congr h]
    exact limsup_const_bot⟩

@[simp]
/-
**liminf_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：liminf_eq_top : f.liminf u = ⊤ ↔ u =ᶠ[f] ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `limsup_eq_bot`：limsup_eq_bot : f.limsup u = ⊥ ↔ u =ᶠ[f] ⊥
· 使用定理 `instFirstCountableTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalS
pace α] [h : FirstCountableTopology α], FirstCountableTopology αᵒᵈ
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem liminf_eq_top : f.liminf u = ⊤ ↔ u =ᶠ[f] ⊤ :=
  limsup_eq_bot (α := αᵒᵈ)

/-- Let `u : ι → α → β` be a sequence of antitone functions `α → β` indexed by `ι`. Suppose that for
all `i : ι`, `u i` tends to `c` at infinity, and that furthermore the limsup of `i ↦ u i r` along
the cofinite filter tends to the same `c` as `r` tends to infinity.
Then the supremum function `r ↦ ⨆ i, u i r` also tends to `c` at infinity. -/
/-
**tendsto_iSup_of_tendsto_limsup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_iSup_of_tendsto_limsup {α β : Type*} [ConditionallyCompleteLattice
 α] [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {u : ι -> α -
> β} {c : β} (h_all : forall i, Tendsto (u i) atTop (𝓝 c)) (h_limsup : Tendsto (
fun r : α => limsup (fun i => u i r) cofinite) atTop (𝓝 c)) (h_anti : forall i, 
Antitone (u i)) : Tendsto (fun r : α => ⨆ i, u i r) atTop (𝓝 c)
参数：h_all : forall i, Tendsto (u i) atTop (𝓝 c)；h_limsup : Tendsto (fun r : α => 
limsup (fun i => u i r) cofinite) atTop (𝓝 c)；h_anti : forall i, Antitone (u i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `Filter.cofinite_eq_bot`：cofinite_eq_bot [Finite α] : @cofinite α = ⊥
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Filter.limsup_bot`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] (f : β → α), Filter.limsup f ⊥ = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Antitone.le_of_tendsto`：Antitone.le_of_tendsto [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsDirectedOrder β] {f : β -> α} {
a : α} (hf :…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_iSup_iff`：le_iSup_iff {s : ι -> α} : a <= iSup s ↔ forall b, (forall 
i, s i <= b) -> a <= b
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
Let `u : ι → α → β` be a sequence of antitone functions `α → β` indexed by `ι`. 
Suppose that for
all `i : ι`, `u i` tends to `c` at infinity, and that furthermore the limsup of 
`i ↦ u i r` along
the cofinite filter tends to the same `c` as `r` tends to infinity.
Then the supremum function `r ↦ ⨆ i, u i r` also tends to `c` at infinity.
-/
lemma tendsto_iSup_of_tendsto_limsup {α β : Type*} [ConditionallyCompleteLattice α]
    [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {u : ι → α → β} {c : β}
    (h_all : ∀ i, Tendsto (u i) atTop (𝓝 c))
    (h_limsup : Tendsto (fun r : α ↦ limsup (fun i ↦ u i r) cofinite) atTop (𝓝 c))
    (h_anti : ∀ i, Antitone (u i)) :
    Tendsto (fun r : α ↦ ⨆ i, u i r) atTop (𝓝 c) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨n0⟩⟩
  · simpa using! h_limsup
  refine tendsto_order.mpr ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · filter_upwards with r
    have : c ≤ u n0 r := (h_anti n0).le_of_tendsto (h_all n0) r
    exact hb.trans_le (this.trans (le_iSup_iff.mpr fun b a ↦ a n0))
  -- `⊢ ∀ᶠ (b_1 : α) in atTop, ⨆ i, u i b_1 < b` for `b > c`
  let b' := if h : (Set.Ioo c b).Nonempty then h.some else c
  have hb'b : b' < b := by
    simp only [b']
    split_ifs with h
    exacts [h.some_mem.2, hb]
  have : ∀ᶠ r in atTop, limsup (u · r) cofinite ≤ b' := by
    simp only [b']
    split_ifs with h
    · filter_upwards [(tendsto_order.1 h_limsup).2 _ h.some_mem.1] with r hr using hr.le
    · filter_upwards [(tendsto_order.1 h_limsup).2 b hb] with r hr
      contrapose! h
      exact ⟨limsup (u · r) cofinite, h, hr⟩
  obtain ⟨r, hr⟩ : ∃ r, ∀ s ≥ r, limsup (u · s) cofinite ≤ b' := by simpa using! this
  obtain ⟨b'', hb''b, hb''⟩ : ∃ b'' ∈ Set.Ico b' b, ∀ᶠ n in cofinite, u n r ≤ b'' := by
    rcases Set.eq_empty_or_nonempty (Set.Ioo b' b) with h | ⟨b'', hb'b'', hb''b⟩
    · refine ⟨b', ⟨le_rfl, hb'b⟩, ?_⟩
      have h_lt := eventually_lt_of_limsup_lt ((hr r le_rfl).trans_lt hb'b)
      filter_upwards [h_lt] with n hn
      contrapose! h
      exact ⟨u n r, h, hn⟩
    · refine ⟨b'', ⟨hb'b''.le, hb''b⟩ , ?_⟩
      have h_lt := eventually_lt_of_limsup_lt ((hr r le_rfl).trans_lt hb'b'')
      filter_upwards [h_lt] with n hn using hn.le
  have A (n) : ∃ r, ∀ s ≥ r, u n s ≤ b'' := by
    suffices ∀ᶠ r in atTop, u n r ≤ b' by
      simp only [eventually_atTop] at this
      rcases this with ⟨r, hr⟩
      exact ⟨r, fun s hs ↦ (hr s hs).trans hb''b.1⟩
    simp only [b']
    split_ifs with h
    · filter_upwards [(tendsto_order.1 (h_all n)).2 _ h.some_mem.1] with r hr
      exact hr.le
    · filter_upwards [(tendsto_order.1 (h_all n)).2 b hb] with r hr
      contrapose! h
      exact ⟨u n r, h, hr⟩
  choose rs hrs using A
  simp only [eventually_atTop]
  refine ⟨r ⊔ ⨆ n : {n | b'' < u n r}, rs n, fun v hv ↦ ?_⟩
  -- `⊢ ⨆ i, u i v < b`
  apply lt_of_le_of_lt (iSup_le fun n ↦ ?_) hb''b.2
  -- `⊢ u n v ≤ b''` for `v` such that `r ⊔ (⨆ n, rs n) ≤ v`
  by_cases hn : b'' < u n r
  · refine hrs n v ?_
    calc rs n
    _ = rs (⟨n, by simp [hn]⟩ : {n | b'' < u n r}) := rfl
    _ ≤ ⨆ n : {n | b'' < u n r}, rs n := by
      refine le_ciSup (f := fun (x : {n | b'' < u n r}) ↦ rs x) ?_
        (⟨n, by simp [hn]⟩ : {n | b'' < u n r})
      have : Finite {n | b'' < u n r} := by simpa using! hb''
      exact Finite.bddAbove_range _
    _ ≤ r ⊔ ⨆ n : {n | b'' < u n r}, rs n := le_sup_right
    _ ≤ v := hv
  · refine (h_anti n ?_).trans (not_lt.mp hn)
    calc r
    _ ≤ r ⊔ ⨆ n : {n | b'' < u n r}, rs n := le_sup_left
    _ ≤ v := hv

/-- Let `u : ℕ → α → β` be a sequence of antitone functions `α → β` indexed by `ℕ`. Suppose that for
all `n : ℕ`, `u n` tends to `c` at infinity, and that furthermore the limsup of `n ↦ u n r`
tends to the same `c` as `r` tends to infinity.
Then the supremum function `r ↦ ⨆ n, u n r` also tends to `c` at infinity. -/
/-
**Nat.tendsto_iSup_of_tendsto_limsup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.tendsto_iSup_of_tendsto_limsup {α β : Type*} [ConditionallyCompleteLat
tice α] [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {u : Nat 
-> α -> β} {c : β} (h_all : forall n, Tendsto (u n) atTop (𝓝 c)) (h_limsup : Ten
dsto (fun r : α => limsup (fun n => u n r) atTop) atTop (𝓝 c)) (h_anti : forall 
n, Antitone (u n)) : Tendsto (fun r : α => ⨆ n, u n r) atTop (𝓝 c)
参数：h_all : forall n, Tendsto (u n) atTop (𝓝 c)；h_limsup : Tendsto (fun r : α => 
limsup (fun n => u n r) atTop) atTop (𝓝 c)；h_anti : forall n, Antitone (u n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `tendsto_iSup_of_tendsto_limsup`：tendsto_iSup_of_tendsto_limsup {α β : Ty
pe*} [ConditionallyCompleteLattice α] [CompleteLinearOrder β] [TopologicalSpace 
β] [OrderTopology β]…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop

--- 原说明 ---
Let `u : ℕ → α → β` be a sequence of antitone functions `α → β` indexed by `ℕ`. 
Suppose that for
all `n : ℕ`, `u n` tends to `c` at infinity, and that furthermore the limsup of 
`n ↦ u n r`
tends to the same `c` as `r` tends to infinity.
Then the supremum function `r ↦ ⨆ n, u n r` also tends to `c` at infinity.
-/
lemma Nat.tendsto_iSup_of_tendsto_limsup {α β : Type*} [ConditionallyCompleteLattice α]
    [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {u : ℕ → α → β} {c : β}
    (h_all : ∀ n, Tendsto (u n) atTop (𝓝 c))
    (h_limsup : Tendsto (fun r : α ↦ limsup (fun n ↦ u n r) atTop) atTop (𝓝 c))
    (h_anti : ∀ n, Antitone (u n)) :
    Tendsto (fun r : α ↦ ⨆ n, u n r) atTop (𝓝 c) := by
  rw [← cofinite_eq_atTop] at h_limsup
  exact _root_.tendsto_iSup_of_tendsto_limsup h_all h_limsup h_anti

end CompleteLinearOrder

end LiminfLimsup

section Monotone

variable {F : Filter ι} [NeBot F]
  [ConditionallyCompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R]
  [ConditionallyCompleteLinearOrder S] [TopologicalSpace S] [OrderTopology S]

/-- An antitone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsSup` to the `Filter.liminf` of the image if the function is continuous at the `limsSup`
(and the filter is bounded from above and frequently bounded from below). -/
/-
**Antitone.map_limsSup_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.map_limsSup_of_continuousAt {F : Filter R} [NeBot F] {f : R -> S}
 (f_decr : Antitone f) (f_cont : ContinuousAt f F.limsSup) (bdd_above : F.IsBoun
ded (· <= ·)
参数：f_decr : Antitone f；f_cont : ContinuousAt f F.limsSup。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsSup.eq_1`：∀ {α : Type u_1} [inst : ConditionallyCompleteLatti
ce α] (f : Filter α), f.limsSup = sInf {a | ∀ᶠ (n : α) in f, n ≤ a}
· 使用定理 `Antitone.map_csInf_of_continuousAt`：Antitone.map_csInf_of_continuousAt {
f : α -> β} {A : Set α} (Cf : ContinuousAt f (sInf A)) (Af : Antitone f) (A_none
mp : A.Nonempty) (A_bdd …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_lt_of_lt_csSup`：exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b <
 sSup s) : exists a in s, b < a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `lt_csSup_of_lt`：lt_csSup_of_lt (hs : BddAbove s) (ha : a in s) (h : b < 
a) : b < sSup s
· 使用定理 `Antitone.isCoboundedUnder_ge_of_isCobounded`：∀ {R : Type u_5} {S : Type 
u_6} {F : Filter R} [inst : LinearOrder R] [inst_1 : LinearOrder S] {f : R → S},
   Antitone f →     ∀ [F.NeBot], …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.frequently_lt_of_lt_limsSup`：frequently_lt_of_lt_limsSup {f : Fil
ter α} [ConditionallyCompleteLinearOrder α] {a : α} (hf : f.IsCobounded (· <= ·)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Filter.liminf_le_of_frequently_le`：liminf_le_of_frequently_le (hu : exis
tsᶠ i in f, u i <= a) (hu_le : f.IsBoundedUnder (· >= ·) u
· 使用定理 `Filter.IsBounded.isBoundedUnder`：∀ {α : Type u_1} {β : Type u_2} {r : α 
→ α → Prop} {f : Filter α} {q : β → β → Prop} {u : α → β},   (∀ (a₀ a₁ : α), r a
₀ a₁ → q (u a₀) (u a₁…
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `exists_Ioc_subset_of_mem_nhds`：exists_Ioc_subset_of_mem_nhds {a : α} {s 
: Set α} (hs : s in 𝓝 a) (h : exists l, l < a) : exists l < a, Ioc l a subseteq 
s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
An antitone function between (conditionally) complete linear ordered spaces send
s a
`Filter.limsSup` to the `Filter.liminf` of the image if the function is continuo
us at the `limsSup`
(and the filter is bounded from above and frequently bounded from below).
-/
theorem Antitone.map_limsSup_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_decr : Antitone f) (f_cont : ContinuousAt f F.limsSup)
    (bdd_above : F.IsBounded (· ≤ ·) := by isBoundedDefault)
    (cobdd : F.IsCobounded (· ≤ ·) := by isBoundedDefault) :
    f F.limsSup = F.liminf f := by
  apply le_antisymm
  · rw [limsSup, f_decr.map_csInf_of_continuousAt f_cont bdd_above cobdd]
    apply le_of_forall_lt
    intro c hc
    simp only [liminf, limsInf, eventually_map] at hc ⊢
    obtain ⟨d, hd, h'd⟩ :=
      exists_lt_of_lt_csSup (bdd_above.recOn fun x hx ↦ ⟨f x, Set.mem_image_of_mem f hx⟩) hc
    apply lt_csSup_of_lt ?_ ?_ h'd
    · simpa only [BddAbove, upperBounds]
        using! Antitone.isCoboundedUnder_ge_of_isCobounded f_decr cobdd
    · rcases hd with ⟨e, ⟨he, fe_eq_d⟩⟩
      filter_upwards [he] with x hx using (fe_eq_d.symm ▸ f_decr hx)
  · by_cases! h' : ∃ c, c < F.limsSup ∧ Set.Ioo c F.limsSup = ∅
    · rcases h' with ⟨c, c_lt, hc⟩
      have B : ∃ᶠ n in F, F.limsSup ≤ n := by
        apply (frequently_lt_of_lt_limsSup cobdd c_lt).mono
        intro x hx
        by_contra!
        have : (Set.Ioo c F.limsSup).Nonempty := ⟨x, ⟨hx, this⟩⟩
        simp only [hc, Set.not_nonempty_empty] at this
      apply liminf_le_of_frequently_le _ (bdd_above.isBoundedUnder f_decr)
      exact B.mono fun x hx ↦ f_decr hx
    by_contra! H
    have not_bot : ¬ IsBot F.limsSup := fun maybe_bot ↦
      lt_irrefl (F.liminf f) <| lt_of_le_of_lt
        (liminf_le_of_frequently_le (Frequently.of_forall (fun r ↦ f_decr (maybe_bot r)))
          (bdd_above.isBoundedUnder f_decr)) H
    obtain ⟨l, l_lt, h'l⟩ :
        ∃ l < F.limsSup, Set.Ioc l F.limsSup ⊆ { x : R | f x < F.liminf f } := by
      apply exists_Ioc_subset_of_mem_nhds ((tendsto_order.1 f_cont.tendsto).2 _ H)
      simpa [IsBot] using! not_bot
    obtain ⟨m, l_m, m_lt⟩ : (Set.Ioo l F.limsSup).Nonempty := by
      contrapose! h'
      exact ⟨l, l_lt, h'⟩
    have B : F.liminf f ≤ f m := by
      apply liminf_le_of_frequently_le _ _
      · apply (frequently_lt_of_lt_limsSup cobdd m_lt).mono
        exact fun x hx ↦ f_decr hx.le
      · exact IsBounded.isBoundedUnder f_decr bdd_above
    have I : f m < F.liminf f := h'l ⟨l_m, m_lt.le⟩
    exact lt_irrefl _ (B.trans_lt I)

/-- A continuous antitone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsup` to the `Filter.liminf` of the images (if the filter is bounded from above and
frequently bounded from below). -/
/-
**Antitone.map_limsup_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.map_limsup_of_continuousAt {f : R -> S} (f_decr : Antitone f) (a 
: ι -> R) (f_cont : ContinuousAt f (F.limsup a)) (bdd_above : F.IsBoundedUnder (
· <= ·) a
参数：f_decr : Antitone f；a : ι -> R；f_cont : ContinuousAt f (F.limsup a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.map_limsSup_of_continuousAt`：Antitone.map_limsSup_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_decr : Antitone f) (f_cont : Continu
ousAt f F.limsSup) (bdd_ab…

--- 原说明 ---
A continuous antitone function between (conditionally) complete linear ordered s
paces sends a
`Filter.limsup` to the `Filter.liminf` of the images (if the filter is bounded f
rom above and
frequently bounded from below).
-/
theorem Antitone.map_limsup_of_continuousAt {f : R → S} (f_decr : Antitone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.limsup a))
    (bdd_above : F.IsBoundedUnder (· ≤ ·) a := by isBoundedDefault)
    (cobdd : F.IsCoboundedUnder (· ≤ ·) a := by isBoundedDefault) :
    f (F.limsup a) = F.liminf (f ∘ a) :=
  f_decr.map_limsSup_of_continuousAt f_cont bdd_above cobdd

set_option backward.isDefEq.respectTransparency false in
/-- An antitone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsInf` to the `Filter.limsup` of the image if the function is continuous at the `limsInf`
(and the filter is bounded from below and frequently bounded from above). -/
/-
**Antitone.map_limsInf_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.map_limsInf_of_continuousAt {F : Filter R} [NeBot F] {f : R -> S}
 (f_decr : Antitone f) (f_cont : ContinuousAt f F.limsInf) (cobdd : F.IsCobounde
d (· >= ·)
参数：f_decr : Antitone f；f_cont : ContinuousAt f F.limsInf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.map_limsSup_of_continuousAt`：Antitone.map_limsSup_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_decr : Antitone f) (f_cont : Continu
ousAt f F.limsSup) (bdd_ab…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Antitone f → Antitone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…

--- 原说明 ---
An antitone function between (conditionally) complete linear ordered spaces send
s a
`Filter.limsInf` to the `Filter.limsup` of the image if the function is continuo
us at the `limsInf`
(and the filter is bounded from below and frequently bounded from above).
-/
theorem Antitone.map_limsInf_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_decr : Antitone f) (f_cont : ContinuousAt f F.limsInf)
    (cobdd : F.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (bdd_below : F.IsBounded (· ≥ ·) := by isBoundedDefault) : f F.limsInf = F.limsup f :=
  Antitone.map_limsSup_of_continuousAt (R := Rᵒᵈ) (S := Sᵒᵈ) f_decr.dual f_cont bdd_below cobdd

/-- A continuous antitone function between (conditionally) complete linear ordered spaces sends a
`Filter.liminf` to the `Filter.limsup` of the images (if the filter is bounded from below and
frequently bounded from above). -/
/-
**Antitone.map_liminf_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.map_liminf_of_continuousAt {f : R -> S} (f_decr : Antitone f) (a 
: ι -> R) (f_cont : ContinuousAt f (F.liminf a)) (cobdd : F.IsCoboundedUnder (· 
>= ·) a
参数：f_decr : Antitone f；a : ι -> R；f_cont : ContinuousAt f (F.liminf a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.map_limsInf_of_continuousAt`：Antitone.map_limsInf_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_decr : Antitone f) (f_cont : Continu
ousAt f F.limsInf) (cobdd …

--- 原说明 ---
A continuous antitone function between (conditionally) complete linear ordered s
paces sends a
`Filter.liminf` to the `Filter.limsup` of the images (if the filter is bounded f
rom below and
frequently bounded from above).
-/
theorem Antitone.map_liminf_of_continuousAt {f : R → S} (f_decr : Antitone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.liminf a))
    (cobdd : F.IsCoboundedUnder (· ≥ ·) a := by isBoundedDefault)
    (bdd_below : F.IsBoundedUnder (· ≥ ·) a := by isBoundedDefault) :
    f (F.liminf a) = F.limsup (f ∘ a) :=
  f_decr.map_limsInf_of_continuousAt f_cont cobdd bdd_below

/-- A monotone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsSup` to the `Filter.limsup` of the image if the function is continuous at the `limsSup`
(and the filter is bounded from above and frequently bounded from below). -/
/-
**Monotone.map_limsSup_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.map_limsSup_of_continuousAt {F : Filter R} [NeBot F] {f : R -> S}
 (f_incr : Monotone f) (f_cont : ContinuousAt f F.limsSup) (bdd_above : F.IsBoun
ded (· <= ·)
参数：f_incr : Monotone f；f_cont : ContinuousAt f F.limsSup。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.map_limsSup_of_continuousAt`：Antitone.map_limsSup_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_decr : Antitone f) (f_cont : Continu
ousAt f F.limsSup) (bdd_ab…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ

--- 原说明 ---
A monotone function between (conditionally) complete linear ordered spaces sends
 a
`Filter.limsSup` to the `Filter.limsup` of the image if the function is continuo
us at the `limsSup`
(and the filter is bounded from above and frequently bounded from below).
-/
theorem Monotone.map_limsSup_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_incr : Monotone f) (f_cont : ContinuousAt f F.limsSup)
    (bdd_above : F.IsBounded (· ≤ ·) := by isBoundedDefault)
    (cobdd : F.IsCobounded (· ≤ ·) := by isBoundedDefault) : f F.limsSup = F.limsup f :=
  Antitone.map_limsSup_of_continuousAt (S := Sᵒᵈ) f_incr f_cont bdd_above cobdd

/-- A continuous monotone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsup` to the `Filter.limsup` of the images (if the filter is bounded from above and
frequently bounded from below). -/
/-
**Monotone.map_limsup_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.map_limsup_of_continuousAt {f : R -> S} (f_incr : Monotone f) (a 
: ι -> R) (f_cont : ContinuousAt f (F.limsup a)) (bdd_above : F.IsBoundedUnder (
· <= ·) a
参数：f_incr : Monotone f；a : ι -> R；f_cont : ContinuousAt f (F.limsup a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_limsSup_of_continuousAt`：Monotone.map_limsSup_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_incr : Monotone f) (f_cont : Continu
ousAt f F.limsSup) (bdd_ab…

--- 原说明 ---
A continuous monotone function between (conditionally) complete linear ordered s
paces sends a
`Filter.limsup` to the `Filter.limsup` of the images (if the filter is bounded f
rom above and
frequently bounded from below).
-/
theorem Monotone.map_limsup_of_continuousAt {f : R → S} (f_incr : Monotone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.limsup a))
    (bdd_above : F.IsBoundedUnder (· ≤ ·) a := by isBoundedDefault)
    (cobdd : F.IsCoboundedUnder (· ≤ ·) a := by isBoundedDefault) :
    f (F.limsup a) = F.limsup (f ∘ a) :=
  f_incr.map_limsSup_of_continuousAt f_cont bdd_above cobdd

set_option backward.isDefEq.respectTransparency false in
/-- A monotone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsInf` to the `Filter.liminf` of the image if the function is continuous at the `limsInf`
(and the filter is bounded from below and frequently bounded from above). -/
/-
**Monotone.map_limsInf_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.map_limsInf_of_continuousAt {F : Filter R} [NeBot F] {f : R -> S}
 (f_incr : Monotone f) (f_cont : ContinuousAt f F.limsInf) (cobdd : F.IsCobounde
d (· >= ·)
参数：f_incr : Monotone f；f_cont : ContinuousAt f F.limsInf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.map_limsSup_of_continuousAt`：Antitone.map_limsSup_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_decr : Antitone f) (f_cont : Continu
ousAt f F.limsSup) (bdd_ab…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…

--- 原说明 ---
A monotone function between (conditionally) complete linear ordered spaces sends
 a
`Filter.limsInf` to the `Filter.liminf` of the image if the function is continuo
us at the `limsInf`
(and the filter is bounded from below and frequently bounded from above).
-/
theorem Monotone.map_limsInf_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_incr : Monotone f) (f_cont : ContinuousAt f F.limsInf)
    (cobdd : F.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (bdd_below : F.IsBounded (· ≥ ·) := by isBoundedDefault) : f F.limsInf = F.liminf f :=
  Antitone.map_limsSup_of_continuousAt (R := Rᵒᵈ) f_incr.dual f_cont bdd_below cobdd

/-- A continuous monotone function between (conditionally) complete linear ordered spaces sends a
`Filter.liminf` to the `Filter.liminf` of the images (if the filter is bounded from below and
frequently bounded from above). -/
/-
**Monotone.map_liminf_of_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.map_liminf_of_continuousAt {f : R -> S} (f_incr : Monotone f) (a 
: ι -> R) (f_cont : ContinuousAt f (F.liminf a)) (cobdd : F.IsCoboundedUnder (· 
>= ·) a
参数：f_incr : Monotone f；a : ι -> R；f_cont : ContinuousAt f (F.liminf a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_limsInf_of_continuousAt`：Monotone.map_limsInf_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_incr : Monotone f) (f_cont : Continu
ousAt f F.limsInf) (cobdd …

--- 原说明 ---
A continuous monotone function between (conditionally) complete linear ordered s
paces sends a
`Filter.liminf` to the `Filter.liminf` of the images (if the filter is bounded f
rom below and
frequently bounded from above).
-/
theorem Monotone.map_liminf_of_continuousAt {f : R → S} (f_incr : Monotone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.liminf a))
    (cobdd : F.IsCoboundedUnder (· ≥ ·) a := by isBoundedDefault)
    (bdd_below : F.IsBoundedUnder (· ≥ ·) a := by isBoundedDefault) :
    f (F.liminf a) = F.liminf (f ∘ a) :=
  f_incr.map_limsInf_of_continuousAt f_cont cobdd bdd_below

end Monotone

section CompleteLattice

variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
  [CompleteLattice β] {f : α → β}

/-
**Antitone.liminf_nhdsGT_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Antitone.liminf_nhdsGT_eq_iSup₂_of_exists_gt (hf : Antitone f) (a : α) (hb : ∃ b, a < b) :
    (𝓝[>] a).liminf f = ⨆ r > a, f r := by
  rw [(nhdsGT_basis_of_exists_gt hb).liminf_eq_iSup_iInf]
  refine le_antisymm (iSup₂_mono' fun r hr ↦ ?_)
    (iSup₂_mono' fun r hr ↦ ⟨r, hr, le_iInf₂ fun i hi ↦ hf (Set.mem_Ioo.1 hi).2.le⟩)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.1, iInf₂_le b hb⟩
/-
**Antitone.liminf_nhdsGT_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Antitone.liminf_nhdsGT_eq_iSup₂ [NoMaxOrder α] (hf : Antitone f) (a : α) :
    (𝓝[>] a).liminf f = ⨆ r > a, f r :=
  hf.liminf_nhdsGT_eq_iSup₂_of_exists_gt a (exists_gt a)
/-
**Monotone.liminf_nhdsLT_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Monotone.liminf_nhdsLT_eq_iSup₂_of_exists_lt (hf : Monotone f) (a : α) (hb : ∃ b, b < a) :
    (𝓝[<] a).liminf f = ⨆ r < a, f r := by
  rw [(nhdsLT_basis_of_exists_lt hb).liminf_eq_iSup_iInf]
  refine le_antisymm (iSup₂_mono' fun r hr ↦ ?_)
    (iSup₂_mono' fun r hr ↦ ⟨r, hr, le_iInf₂ fun i hi ↦ hf (Set.mem_Ioo.1 hi).1.le⟩)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.2, iInf₂_le b hb⟩
/-
**Monotone.liminf_nhdsLT_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Monotone.liminf_nhdsLT_eq_iSup₂ [NoMinOrder α] (hf : Monotone f) (a : α) :
    (𝓝[<] a).liminf f = ⨆ r < a, f r :=
  hf.liminf_nhdsLT_eq_iSup₂_of_exists_lt a (exists_lt a)
/-
**Monotone.limsup_nhdsGT_eq_iInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Monotone.limsup_nhdsGT_eq_iInf₂_of_exists_gt (hf : Monotone f) (a : α) (hb : ∃ b, a < b) :
    (𝓝[>] a).limsup f = ⨅ r > a, f r := by
  rw [(nhdsGT_basis_of_exists_gt hb).limsup_eq_iInf_iSup]
  refine le_antisymm
    (iInf₂_mono' fun r hr ↦ ⟨r, hr, iSup₂_le fun i hi ↦ hf (Set.mem_Ioo.1 hi).2.le⟩)
    (iInf₂_mono' fun r hr ↦ ?_)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.1, le_iSup₂_of_le b hb le_rfl⟩
/-
**Monotone.limsup_nhdsGT_eq_iInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Monotone.limsup_nhdsGT_eq_iInf₂ [NoMaxOrder α] (hf : Monotone f) (a : α) :
    (𝓝[>] a).limsup f = ⨅ r > a, f r :=
  hf.limsup_nhdsGT_eq_iInf₂_of_exists_gt a (exists_gt a)
/-
**Antitone.limsup_nhdsLT_eq_iInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Antitone.limsup_nhdsLT_eq_iInf₂_of_exists_lt (hf : Antitone f) (a : α) (hb : ∃ b, b < a) :
    (𝓝[<] a).limsup f = ⨅ r < a, f r := by
  rw [(nhdsLT_basis_of_exists_lt hb).limsup_eq_iInf_iSup]
  refine le_antisymm
    (iInf₂_mono' fun r hr ↦ ⟨r, hr, iSup₂_le fun i hi ↦ hf (Set.mem_Ioo.1 hi).1.le⟩)
    (iInf₂_mono' fun r hr ↦ ?_)
  obtain ⟨b, hb⟩ := exists_between hr
  exact ⟨b, hb.2, le_iSup₂_of_le b hb le_rfl⟩
/-
**Antitone.limsup_nhdsLT_eq_iInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Antitone.limsup_nhdsLT_eq_iInf₂ [NoMinOrder α] (hf : Antitone f) (a : α) :
    (𝓝[<] a).limsup f = ⨅ r < a, f r :=
  hf.limsup_nhdsLT_eq_iInf₂_of_exists_lt a (exists_lt a)

end CompleteLattice

