/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Order.OrderClosed

/-!
# Topological lattices

In this file we define mixin classes `ContinuousInf` and `ContinuousSup`. We define the
class `TopologicalLattice` as a topological space and lattice `L` extending `ContinuousInf` and
`ContinuousSup`.

## References

* [Gierz et al, A Compendium of Continuous Lattices][GierzEtAl1980]

## Tags

topological, lattice
-/

public section

open Filter

open Topology

/-- Let `L` be a topological space and let `L×L` be equipped with the product topology and let
`⊓:L×L → L` be an infimum. Then `L` is said to have *(jointly) continuous infimum* if the map
`⊓:L×L → L` is continuous.
-/
/-
**ContinuousInf** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(L : Type u_1) → [TopologicalSpace L] → [Min L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `L` be a topological space and let `L×L` be equipped with the product topolo
gy and let
`⊓:L×L → L` be an infimum. Then `L` is said to have *(jointly) continuous infimu
m* if the map
`⊓:L×L → L` is continuous.
-/
class ContinuousInf (L : Type*) [TopologicalSpace L] [Min L] : Prop where
  /-- The infimum is continuous -/
  continuous_inf : Continuous fun p : L × L => p.1 ⊓ p.2

/-- Let `L` be a topological space and let `L×L` be equipped with the product topology and let
`⊓:L×L → L` be a supremum. Then `L` is said to have *(jointly) continuous supremum* if the map
`⊓:L×L → L` is continuous.
-/
/-
**ContinuousSup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(L : Type u_1) → [TopologicalSpace L] → [Max L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `L` be a topological space and let `L×L` be equipped with the product topolo
gy and let
`⊓:L×L → L` be a supremum. Then `L` is said to have *(jointly) continuous suprem
um* if the map
`⊓:L×L → L` is continuous.
-/
class ContinuousSup (L : Type*) [TopologicalSpace L] [Max L] : Prop where
  /-- The supremum is continuous -/
  continuous_sup : Continuous fun p : L × L => p.1 ⊔ p.2
/-
**OrderDual.continuousSup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.continuousSup (L : Type*) [TopologicalSpace L] [Min L] [h : Cont
inuousInf L] : ContinuousSup Lᵒᵈ where continuous_sup
参数：L : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousInf.continuous_inf`：∀ {L : Type u_1} {inst : TopologicalSpace 
L} {inst_1 : Min L} [self : ContinuousInf L], Continuous fun p => p.1 ⊓ p.2
-/
instance OrderDual.continuousSup (L : Type*) [TopologicalSpace L] [Min L]
    [h : ContinuousInf L] : ContinuousSup Lᵒᵈ where
  continuous_sup := h.continuous_inf
/-
**OrderDual.continuousInf** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.continuousInf (L : Type*) [TopologicalSpace L] [Max L] [h : Cont
inuousSup L] : ContinuousInf Lᵒᵈ where continuous_inf
参数：L : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousSup.continuous_sup`：∀ {L : Type u_1} {inst : TopologicalSpace 
L} {inst_1 : Max L} [self : ContinuousSup L], Continuous fun p => p.1 ⊔ p.2
-/
instance OrderDual.continuousInf (L : Type*) [TopologicalSpace L] [Max L]
    [h : ContinuousSup L] : ContinuousInf Lᵒᵈ where
  continuous_inf := h.continuous_sup

/-- Let `L` be a lattice equipped with a topology such that `L` has continuous infimum and supremum.
Then `L` is said to be a *topological lattice*.
-/
/-
**TopologicalLattice** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(L : Type u_1) → [TopologicalSpace L] → [Lattice L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `L` be a lattice equipped with a topology such that `L` has continuous infim
um and supremum.
Then `L` is said to be a *topological lattice*.
-/
class TopologicalLattice (L : Type*) [TopologicalSpace L] [Lattice L] : Prop
  extends ContinuousInf L, ContinuousSup L
/-
**OrderDual.topologicalLattice** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ (L : Type u_1) [inst : TopologicalSpace L] [inst_1 : Lattice L] [Topolog
icalLattice L], TopologicalLattice Lᵒᵈ
参数：L : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalLattice.toContinuousSup`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousSup L
· 使用定理 `TopologicalLattice.toContinuousInf`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousInf L
-/
instance OrderDual.topologicalLattice (L : Type*) [TopologicalSpace L]
    [Lattice L] [TopologicalLattice L] : TopologicalLattice Lᵒᵈ where

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) LinearOrder.topologicalLattice {L : Type*} [TopologicalSpace L]
    [LinearOrder L] [OrderClosedTopology L] : TopologicalLattice L where
  continuous_inf := continuous_min
  continuous_sup := continuous_max

variable {L X : Type*} [TopologicalSpace L] [TopologicalSpace X]

@[continuity]
/-
**continuous_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_inf [Min L] [ContinuousInf L] : Continuous fun p : L × L => p.1
 ⊓ p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousInf.continuous_inf`：∀ {L : Type u_1} {inst : TopologicalSpace 
L} {inst_1 : Min L} [self : ContinuousInf L], Continuous fun p => p.1 ⊓ p.2
-/
theorem continuous_inf [Min L] [ContinuousInf L] : Continuous fun p : L × L => p.1 ⊓ p.2 :=
  ContinuousInf.continuous_inf

@[continuity, fun_prop]
/-
**Continuous.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.inf [Min L] [ContinuousInf L] {f g : X -> L} (hf : Continuous f
) (hg : Continuous g) : Continuous fun x => f x ⊓ g x
参数：hf : Continuous f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_inf`：continuous_inf [Min L] [ContinuousInf L] : Continuous fu
n p : L × L => p.1 ⊓ p.2
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
-/
theorem Continuous.inf [Min L] [ContinuousInf L] {f g : X → L} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => f x ⊓ g x :=
  continuous_inf.comp (hf.prodMk hg :)

@[continuity]
/-
**continuous_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sup [Max L] [ContinuousSup L] : Continuous fun p : L × L => p.1
 ⊔ p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousSup.continuous_sup`：∀ {L : Type u_1} {inst : TopologicalSpace 
L} {inst_1 : Max L} [self : ContinuousSup L], Continuous fun p => p.1 ⊔ p.2
-/
theorem continuous_sup [Max L] [ContinuousSup L] : Continuous fun p : L × L => p.1 ⊔ p.2 :=
  ContinuousSup.continuous_sup

@[continuity, fun_prop]
/-
**Continuous.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.sup [Max L] [ContinuousSup L] {f g : X -> L} (hf : Continuous f
) (hg : Continuous g) : Continuous fun x => f x ⊔ g x
参数：hf : Continuous f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_sup`：continuous_sup [Max L] [ContinuousSup L] : Continuous fu
n p : L × L => p.1 ⊔ p.2
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
-/
theorem Continuous.sup [Max L] [ContinuousSup L] {f g : X → L} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => f x ⊔ g x :=
  continuous_sup.comp (hf.prodMk hg :)

namespace Filter.Tendsto

section SupInf

variable {α : Type*} {l : Filter α} {f g : α → L} {x y : L}

/-
**Filter.Tendsto.sup_nhds'** 是 Mathlib 中的一个引理，位于命名空间 `Filter.Tendsto`。
形式化陈述：sup_nhds' [Max L] [ContinuousSup L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto
 g l (𝓝 y)) : Tendsto (f ⊔ g) l (𝓝 (x ⊔ y))
参数：hf : Tendsto f l (𝓝 x)；hg : Tendsto g l (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_sup`：continuous_sup [Max L] [ContinuousSup L] : Continuous fu
n p : L × L => p.1 ⊔ p.2
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
lemma sup_nhds' [Max L] [ContinuousSup L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (f ⊔ g) l (𝓝 (x ⊔ y)) :=
  (continuous_sup.tendsto _).comp (hf.prodMk_nhds hg)
/-
**Filter.Tendsto.sup_nhds** 是 Mathlib 中的一个引理，位于命名空间 `Filter.Tendsto`。
形式化陈述：sup_nhds [Max L] [ContinuousSup L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto 
g l (𝓝 y)) : Tendsto (fun i => f i ⊔ g i) l (𝓝 (x ⊔ y))
参数：hf : Tendsto f l (𝓝 x)；hg : Tendsto g l (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Tendsto.sup_nhds'`：sup_nhds' [Max L] [ContinuousSup L] (hf : Tend
sto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (f ⊔ g) l (𝓝 (x ⊔ y))
-/
lemma sup_nhds [Max L] [ContinuousSup L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun i => f i ⊔ g i) l (𝓝 (x ⊔ y)) :=
  hf.sup_nhds' hg
/-
**Filter.Tendsto.inf_nhds'** 是 Mathlib 中的一个引理，位于命名空间 `Filter.Tendsto`。
形式化陈述：inf_nhds' [Min L] [ContinuousInf L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto
 g l (𝓝 y)) : Tendsto (f ⊓ g) l (𝓝 (x ⊓ y))
参数：hf : Tendsto f l (𝓝 x)；hg : Tendsto g l (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_inf`：continuous_inf [Min L] [ContinuousInf L] : Continuous fu
n p : L × L => p.1 ⊓ p.2
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
lemma inf_nhds' [Min L] [ContinuousInf L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (f ⊓ g) l (𝓝 (x ⊓ y)) :=
  (continuous_inf.tendsto _).comp (hf.prodMk_nhds hg)
/-
**Filter.Tendsto.inf_nhds** 是 Mathlib 中的一个引理，位于命名空间 `Filter.Tendsto`。
形式化陈述：inf_nhds [Min L] [ContinuousInf L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto 
g l (𝓝 y)) : Tendsto (fun i => f i ⊓ g i) l (𝓝 (x ⊓ y))
参数：hf : Tendsto f l (𝓝 x)；hg : Tendsto g l (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Tendsto.inf_nhds'`：inf_nhds' [Min L] [ContinuousInf L] (hf : Tend
sto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (f ⊓ g) l (𝓝 (x ⊓ y))
-/
lemma inf_nhds [Min L] [ContinuousInf L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun i => f i ⊓ g i) l (𝓝 (x ⊓ y)) :=
  hf.inf_nhds' hg

end SupInf

open Finset

variable {ι α : Type*} {s : Finset ι} {f : ι → α → L} {l : Filter α} {g : ι → L}

/-
**Filter.Tendsto.finset_sup'_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {L : Type u_1} [inst : TopologicalSpace L] {ι : Type u_3} {α : Type u_4}
 {s : Finset ι} {f : ι → α → L} {l : Filter α}   {g : ι → L} [inst_1 : Semilatti
ceSup L] [ContinuousSup L] (hne : s.Nonempty),   (∀ i ∈ s, Filter.Tendsto (f i) 
l (nhds (g i))) → Filter.Tendsto (s.sup' hne f) l (nhds (s.sup' hne g))
参数：hne : s.Nonempty；∀ i ∈ s, Filter.Tendsto (f i) l (nhds (g i))；s.sup' hne f；nh
ds (s.sup' hne g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Finset α)
.Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] {s : Finset β} (H : s.Nonempty) (f : β → α) {b : β}   {hb : b ∉ s}, (Finset.
cons b…
· 使用引理 `Filter.Tendsto.sup_nhds`：sup_nhds [Max L] [ContinuousSup L] (hf : Tendst
o f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (fun i => f i ⊔ g i) l (𝓝 (x ⊔ y
))
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.forall_mem_cons`：forall_mem_cons (h : a ∉ s) (p : α -> Prop) : (f
orall x, x in cons a s h -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma finset_sup'_nhds [SemilatticeSup L] [ContinuousSup L]
    (hne : s.Nonempty) (hs : ∀ i ∈ s, Tendsto (f i) l (𝓝 (g i))) :
    Tendsto (s.sup' hne f) l (𝓝 (s.sup' hne g)) := by
  induction hne using Finset.Nonempty.cons_induction with
  | singleton => simpa using hs
  | cons a s ha hne ihs =>
    rw [forall_mem_cons] at hs
    simp only [sup'_cons, hne]
    exact hs.1.sup_nhds (ihs hs.2)
/-
**Filter.Tendsto.finset_sup'_nhds_apply** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendst
o`。
形式化陈述：∀ {L : Type u_1} [inst : TopologicalSpace L] {ι : Type u_3} {α : Type u_4}
 {s : Finset ι} {f : ι → α → L} {l : Filter α}   {g : ι → L} [inst_1 : Semilatti
ceSup L] [ContinuousSup L] (hne : s.Nonempty),   (∀ i ∈ s, Filter.Tendsto (f i) 
l (nhds (g i))) →     Filter.Tendsto (fun a => s.sup' hne fun x => f x a) l (nhd
s (s.sup' hne g))
参数：hne : s.Nonempty；∀ i ∈ s, Filter.Tendsto (f i) l (nhds (g i))；fun a => s.sup'
 hne fun x => f x a；nhds (s.sup' hne g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Tendsto.finset_sup'_nhds`：∀ {L : Type u_1} [inst : TopologicalSpa
ce L] {ι : Type u_3} {α : Type u_4} {s : Finset ι} {f : ι → α → L} {l : Filter α
}   {g : ι → L} [inst…
-/
lemma finset_sup'_nhds_apply [SemilatticeSup L] [ContinuousSup L]
    (hne : s.Nonempty) (hs : ∀ i ∈ s, Tendsto (f i) l (𝓝 (g i))) :
    Tendsto (fun a ↦ s.sup' hne (f · a)) l (𝓝 (s.sup' hne g)) := by
  simpa only [← Finset.sup'_apply] using finset_sup'_nhds hne hs
/-
**Filter.Tendsto.finset_inf'_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {L : Type u_1} [inst : TopologicalSpace L] {ι : Type u_3} {α : Type u_4}
 {s : Finset ι} {f : ι → α → L} {l : Filter α}   {g : ι → L} [inst_1 : Semilatti
ceInf L] [ContinuousInf L] (hne : s.Nonempty),   (∀ i ∈ s, Filter.Tendsto (f i) 
l (nhds (g i))) → Filter.Tendsto (s.inf' hne f) l (nhds (s.inf' hne g))
参数：hne : s.Nonempty；∀ i ∈ s, Filter.Tendsto (f i) l (nhds (g i))；s.inf' hne f；nh
ds (s.inf' hne g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.finset_sup'_nhds`：∀ {L : Type u_1} [inst : TopologicalSpa
ce L] {ι : Type u_3} {α : Type u_4} {s : Finset ι} {f : ι → α → L} {l : Filter α
}   {g : ι → L} [inst…
-/
lemma finset_inf'_nhds [SemilatticeInf L] [ContinuousInf L]
    (hne : s.Nonempty) (hs : ∀ i ∈ s, Tendsto (f i) l (𝓝 (g i))) :
    Tendsto (s.inf' hne f) l (𝓝 (s.inf' hne g)) :=
  finset_sup'_nhds (L := Lᵒᵈ) hne hs
/-
**Filter.Tendsto.finset_inf'_nhds_apply** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendst
o`。
形式化陈述：∀ {L : Type u_1} [inst : TopologicalSpace L] {ι : Type u_3} {α : Type u_4}
 {s : Finset ι} {f : ι → α → L} {l : Filter α}   {g : ι → L} [inst_1 : Semilatti
ceInf L] [ContinuousInf L] (hne : s.Nonempty),   (∀ i ∈ s, Filter.Tendsto (f i) 
l (nhds (g i))) →     Filter.Tendsto (fun a => s.inf' hne fun x => f x a) l (nhd
s (s.inf' hne g))
参数：hne : s.Nonempty；∀ i ∈ s, Filter.Tendsto (f i) l (nhds (g i))；fun a => s.inf'
 hne fun x => f x a；nhds (s.inf' hne g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.finset_sup'_nhds_apply`：∀ {L : Type u_1} [inst : Topologi
calSpace L] {ι : Type u_3} {α : Type u_4} {s : Finset ι} {f : ι → α → L} {l : Fi
lter α}   {g : ι → L} [inst…
-/
lemma finset_inf'_nhds_apply [SemilatticeInf L] [ContinuousInf L]
    (hne : s.Nonempty) (hs : ∀ i ∈ s, Tendsto (f i) l (𝓝 (g i))) :
    Tendsto (fun a ↦ s.inf' hne (f · a)) l (𝓝 (s.inf' hne g)) :=
  finset_sup'_nhds_apply (L := Lᵒᵈ) hne hs
/-
**Filter.Tendsto.finset_sup_nhds** 是 Mathlib 中的一个引理，位于命名空间 `Filter.Tendsto`。
形式化陈述：finset_sup_nhds [SemilatticeSup L] [OrderBot L] [ContinuousSup L] (hs : fo
rall i in s, Tendsto (f i) l (𝓝 (g i))) : Tendsto (s.sup f) l (𝓝 (s.sup g))
参数：hs : forall i in s, Tendsto (f i) l (𝓝 (g i))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `Filter.Tendsto.finset_sup'_nhds`：∀ {L : Type u_1} [inst : TopologicalSpa
ce L] {ι : Type u_3} {α : Type u_4} {s : Finset ι} {f : ι → α → L} {l : Filter α
}   {g : ι → L} [inst…
-/
lemma finset_sup_nhds [SemilatticeSup L] [OrderBot L] [ContinuousSup L]
    (hs : ∀ i ∈ s, Tendsto (f i) l (𝓝 (g i))) : Tendsto (s.sup f) l (𝓝 (s.sup g)) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simpa using! tendsto_const_nhds
  · simp only [← sup'_eq_sup hne]
    exact finset_sup'_nhds hne hs
/-
**Filter.Tendsto.finset_sup_nhds_apply** 是 Mathlib 中的一个引理，位于命名空间 `Filter.Tendsto
`。
形式化陈述：finset_sup_nhds_apply [SemilatticeSup L] [OrderBot L] [ContinuousSup L] (h
s : forall i in s, Tendsto (f i) l (𝓝 (g i))) : Tendsto (fun a => s.sup (f · a))
 l (𝓝 (s.sup g))
参数：hs : forall i in s, Tendsto (f i) l (𝓝 (g i))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Filter.Tendsto.finset_sup_nhds`：finset_sup_nhds [SemilatticeSup L] [Orde
rBot L] [ContinuousSup L] (hs : forall i in s, Tendsto (f i) l (𝓝 (g i))) : Tend
sto (s.sup f) l (𝓝 (…
-/
lemma finset_sup_nhds_apply [SemilatticeSup L] [OrderBot L] [ContinuousSup L]
    (hs : ∀ i ∈ s, Tendsto (f i) l (𝓝 (g i))) :
    Tendsto (fun a ↦ s.sup (f · a)) l (𝓝 (s.sup g)) := by
  simpa only [← Finset.sup_apply] using finset_sup_nhds hs
/-
**Filter.Tendsto.finset_inf_nhds** 是 Mathlib 中的一个引理，位于命名空间 `Filter.Tendsto`。
形式化陈述：finset_inf_nhds [SemilatticeInf L] [OrderTop L] [ContinuousInf L] (hs : fo
rall i in s, Tendsto (f i) l (𝓝 (g i))) : Tendsto (s.inf f) l (𝓝 (s.inf g))
参数：hs : forall i in s, Tendsto (f i) l (𝓝 (g i))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Tendsto.finset_sup_nhds`：finset_sup_nhds [SemilatticeSup L] [Orde
rBot L] [ContinuousSup L] (hs : forall i in s, Tendsto (f i) l (𝓝 (g i))) : Tend
sto (s.sup f) l (𝓝 (…
-/
lemma finset_inf_nhds [SemilatticeInf L] [OrderTop L] [ContinuousInf L]
    (hs : ∀ i ∈ s, Tendsto (f i) l (𝓝 (g i))) : Tendsto (s.inf f) l (𝓝 (s.inf g)) :=
  finset_sup_nhds (L := Lᵒᵈ) hs
/-
**Filter.Tendsto.finset_inf_nhds_apply** 是 Mathlib 中的一个引理，位于命名空间 `Filter.Tendsto
`。
形式化陈述：finset_inf_nhds_apply [SemilatticeInf L] [OrderTop L] [ContinuousInf L] (h
s : forall i in s, Tendsto (f i) l (𝓝 (g i))) : Tendsto (fun a => s.inf (f · a))
 l (𝓝 (s.inf g))
参数：hs : forall i in s, Tendsto (f i) l (𝓝 (g i))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Tendsto.finset_sup_nhds_apply`：finset_sup_nhds_apply [Semilattice
Sup L] [OrderBot L] [ContinuousSup L] (hs : forall i in s, Tendsto (f i) l (𝓝 (g
 i))) : Tendsto (fun a => …
-/
lemma finset_inf_nhds_apply [SemilatticeInf L] [OrderTop L] [ContinuousInf L]
    (hs : ∀ i ∈ s, Tendsto (f i) l (𝓝 (g i))) :
    Tendsto (fun a ↦ s.inf (f · a)) l (𝓝 (s.inf g)) :=
  finset_sup_nhds_apply (L := Lᵒᵈ) hs

end Filter.Tendsto

section Sup

variable [Max L] [ContinuousSup L] {f g : X → L} {s : Set X} {x : X}

@[fun_prop]
/-
**ContinuousAt.sup'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousAt.sup' (hf : ContinuousAt f x) (hg : ContinuousAt g x) : Contin
uousAt (f ⊔ g) x
参数：hf : ContinuousAt f x；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Tendsto.sup_nhds'`：sup_nhds' [Max L] [ContinuousSup L] (hf : Tend
sto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (f ⊔ g) l (𝓝 (x ⊔ y))
-/
lemma ContinuousAt.sup' (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (f ⊔ g) x :=
  hf.sup_nhds' hg

@[fun_prop]
/-
**ContinuousAt.sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousAt.sup (hf : ContinuousAt f x) (hg : ContinuousAt g x) : Continu
ousAt (fun a => f a ⊔ g a) x
参数：hf : ContinuousAt f x；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousAt.sup'`：ContinuousAt.sup' (hf : ContinuousAt f x) (hg : Conti
nuousAt g x) : ContinuousAt (f ⊔ g) x
-/
lemma ContinuousAt.sup (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a ↦ f a ⊔ g a) x :=
  hf.sup' hg

@[fun_prop]
/-
**ContinuousWithinAt.sup'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.sup' (hf : ContinuousWithinAt f s x) (hg : ContinuousWi
thinAt g s x) : ContinuousWithinAt (f ⊔ g) s x
参数：hf : ContinuousWithinAt f s x；hg : ContinuousWithinAt g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Tendsto.sup_nhds'`：sup_nhds' [Max L] [ContinuousSup L] (hf : Tend
sto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (f ⊔ g) l (𝓝 (x ⊔ y))
-/
lemma ContinuousWithinAt.sup' (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (f ⊔ g) s x :=
  hf.sup_nhds' hg

@[fun_prop]
/-
**ContinuousWithinAt.sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.sup (hf : ContinuousWithinAt f s x) (hg : ContinuousWit
hinAt g s x) : ContinuousWithinAt (fun a => f a ⊔ g a) s x
参数：hf : ContinuousWithinAt f s x；hg : ContinuousWithinAt g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.sup'`：ContinuousWithinAt.sup' (hf : ContinuousWithinA
t f s x) (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (f ⊔ g) s x
-/
lemma ContinuousWithinAt.sup (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun a ↦ f a ⊔ g a) s x :=
  hf.sup' hg

@[fun_prop]
/-
**ContinuousOn.sup'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.sup' (hf : ContinuousOn f s) (hg : ContinuousOn g s) : Contin
uousOn (f ⊔ g) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.sup'`：ContinuousWithinAt.sup' (hf : ContinuousWithinA
t f s x) (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (f ⊔ g) s x
-/
lemma ContinuousOn.sup' (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (f ⊔ g) s := fun x hx ↦
  (hf x hx).sup' (hg x hx)

@[fun_prop]
/-
**ContinuousOn.sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.sup (hf : ContinuousOn f s) (hg : ContinuousOn g s) : Continu
ousOn (fun a => f a ⊔ g a) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousOn.sup'`：ContinuousOn.sup' (hf : ContinuousOn f s) (hg : Conti
nuousOn g s) : ContinuousOn (f ⊔ g) s
-/
lemma ContinuousOn.sup (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a ↦ f a ⊔ g a) s :=
  hf.sup' hg

@[fun_prop]
/-
**Continuous.sup'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.sup' (hf : Continuous f) (hg : Continuous g) : Continuous (f ⊔ 
g)
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.sup`：Continuous.sup [Max L] [ContinuousSup L] {f g : X -> L} 
(hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x ⊔ g x
-/
lemma Continuous.sup' (hf : Continuous f) (hg : Continuous g) : Continuous (f ⊔ g) := hf.sup hg

end Sup

section Inf

variable [Min L] [ContinuousInf L] {f g : X → L} {s : Set X} {x : X}

@[fun_prop]
/-
**ContinuousAt.inf'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousAt.inf' (hf : ContinuousAt f x) (hg : ContinuousAt g x) : Contin
uousAt (f ⊓ g) x
参数：hf : ContinuousAt f x；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Tendsto.inf_nhds'`：inf_nhds' [Min L] [ContinuousInf L] (hf : Tend
sto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (f ⊓ g) l (𝓝 (x ⊓ y))
-/
lemma ContinuousAt.inf' (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (f ⊓ g) x :=
  hf.inf_nhds' hg

@[fun_prop]
/-
**ContinuousAt.inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousAt.inf (hf : ContinuousAt f x) (hg : ContinuousAt g x) : Continu
ousAt (fun a => f a ⊓ g a) x
参数：hf : ContinuousAt f x；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousAt.inf'`：ContinuousAt.inf' (hf : ContinuousAt f x) (hg : Conti
nuousAt g x) : ContinuousAt (f ⊓ g) x
-/
lemma ContinuousAt.inf (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a ↦ f a ⊓ g a) x :=
  hf.inf' hg

@[fun_prop]
/-
**ContinuousWithinAt.inf'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.inf' (hf : ContinuousWithinAt f s x) (hg : ContinuousWi
thinAt g s x) : ContinuousWithinAt (f ⊓ g) s x
参数：hf : ContinuousWithinAt f s x；hg : ContinuousWithinAt g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Tendsto.inf_nhds'`：inf_nhds' [Min L] [ContinuousInf L] (hf : Tend
sto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (f ⊓ g) l (𝓝 (x ⊓ y))
-/
lemma ContinuousWithinAt.inf' (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (f ⊓ g) s x :=
  hf.inf_nhds' hg

@[fun_prop]
/-
**ContinuousWithinAt.inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.inf (hf : ContinuousWithinAt f s x) (hg : ContinuousWit
hinAt g s x) : ContinuousWithinAt (fun a => f a ⊓ g a) s x
参数：hf : ContinuousWithinAt f s x；hg : ContinuousWithinAt g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.inf'`：ContinuousWithinAt.inf' (hf : ContinuousWithinA
t f s x) (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (f ⊓ g) s x
-/
lemma ContinuousWithinAt.inf (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun a ↦ f a ⊓ g a) s x :=
  hf.inf' hg

@[fun_prop]
/-
**ContinuousOn.inf'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.inf' (hf : ContinuousOn f s) (hg : ContinuousOn g s) : Contin
uousOn (f ⊓ g) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.inf'`：ContinuousWithinAt.inf' (hf : ContinuousWithinA
t f s x) (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (f ⊓ g) s x
-/
lemma ContinuousOn.inf' (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (f ⊓ g) s := fun x hx ↦
  (hf x hx).inf' (hg x hx)

@[fun_prop]
/-
**ContinuousOn.inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.inf (hf : ContinuousOn f s) (hg : ContinuousOn g s) : Continu
ousOn (fun a => f a ⊓ g a) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousOn.inf'`：ContinuousOn.inf' (hf : ContinuousOn f s) (hg : Conti
nuousOn g s) : ContinuousOn (f ⊓ g) s
-/
lemma ContinuousOn.inf (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a ↦ f a ⊓ g a) s :=
  hf.inf' hg

@[fun_prop]
/-
**Continuous.inf'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.inf' (hf : Continuous f) (hg : Continuous g) : Continuous (f ⊓ 
g)
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.inf`：Continuous.inf [Min L] [ContinuousInf L] {f g : X -> L} 
(hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x ⊓ g x
-/
lemma Continuous.inf' (hf : Continuous f) (hg : Continuous g) : Continuous (f ⊓ g) := hf.inf hg

end Inf

section FinsetSup'

variable {ι : Type*} [SemilatticeSup L] [ContinuousSup L] {s : Finset ι}
  {f : ι → X → L} {t : Set X} {x : X}

@[fun_prop]
/-
**ContinuousAt.finset_sup'_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：∀ {L : Type u_1} {X : Type u_2} [inst : TopologicalSpace L] [inst_1 : Topo
logicalSpace X] {ι : Type u_3}   [inst_2 : SemilatticeSup L] [ContinuousSup L] {
s : Finset ι} {f : ι → X → L} {x : X} (hne : s.Nonempty),   (∀ i ∈ s, Continuous
At (f i) x) → ContinuousAt (fun a => s.sup' hne fun x => f x a) x
参数：hne : s.Nonempty；∀ i ∈ s, ContinuousAt (f i) x；fun a => s.sup' hne fun x => f
 x a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.finset_sup'_nhds_apply`：∀ {L : Type u_1} [inst : Topologi
calSpace L] {ι : Type u_3} {α : Type u_4} {s : Finset ι} {f : ι → α → L} {l : Fi
lter α}   {g : ι → L} [inst…
-/
lemma ContinuousAt.finset_sup'_apply (hne : s.Nonempty) (hs : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun a ↦ s.sup' hne (f · a)) x :=
  Tendsto.finset_sup'_nhds_apply hne hs

@[fun_prop]
/-
**ContinuousAt.finset_sup'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousAt.finset_sup'_apply (hne : s.Nonempty) (hs : forall i in s, Con
tinuousAt (f i) x) : ContinuousAt (fun a => s.sup' hne (f · a)) x
参数：hne : s.Nonempty；hs : forall i in s, ContinuousAt (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousAt.finset_sup'_apply`：∀ {L : Type u_1} {X : Type u_2} [inst : 
TopologicalSpace L] [inst_1 : TopologicalSpace X] {ι : Type u_3}   [inst_2 : Sem
ilatticeSup L] [Cont…
-/
lemma ContinuousAt.finset_sup' (hne : s.Nonempty) (hs : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (s.sup' hne f) x := by
  simpa only [← Finset.sup'_apply] using finset_sup'_apply hne hs

@[fun_prop]
/-
**ContinuousWithinAt.finset_sup'_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousWith
inAt`。
形式化陈述：∀ {L : Type u_1} {X : Type u_2} [inst : TopologicalSpace L] [inst_1 : Topo
logicalSpace X] {ι : Type u_3}   [inst_2 : SemilatticeSup L] [ContinuousSup L] {
s : Finset ι} {f : ι → X → L} {t : Set X} {x : X} (hne : s.Nonempty),   (∀ i ∈ s
, ContinuousWithinAt (f i) t x) → ContinuousWithinAt (fun a => s.sup' hne fun x 
=> f x a) t x
参数：hne : s.Nonempty；∀ i ∈ s, ContinuousWithinAt (f i) t x；fun a => s.sup' hne fu
n x => f x a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.finset_sup'_nhds_apply`：∀ {L : Type u_1} [inst : Topologi
calSpace L] {ι : Type u_3} {α : Type u_4} {s : Finset ι} {f : ι → α → L} {l : Fi
lter α}   {g : ι → L} [inst…
-/
lemma ContinuousWithinAt.finset_sup'_apply (hne : s.Nonempty)
    (hs : ∀ i ∈ s, ContinuousWithinAt (f i) t x) :
    ContinuousWithinAt (fun a ↦ s.sup' hne (f · a)) t x :=
  Tendsto.finset_sup'_nhds_apply hne hs

@[fun_prop]
/-
**ContinuousWithinAt.finset_sup'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.finset_sup'_apply (hne : s.Nonempty) (hs : forall i in 
s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (fun a => s.sup' hne (f · 
a)) t x
参数：hne : s.Nonempty；hs : forall i in s, ContinuousWithinAt (f i) t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousWithinAt.finset_sup'_apply`：∀ {L : Type u_1} {X : Type u_2} [i
nst : TopologicalSpace L] [inst_1 : TopologicalSpace X] {ι : Type u_3}   [inst_2
 : SemilatticeSup L] [Cont…
-/
lemma ContinuousWithinAt.finset_sup' (hne : s.Nonempty)
    (hs : ∀ i ∈ s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (s.sup' hne f) t x := by
  simpa only [← Finset.sup'_apply] using finset_sup'_apply hne hs

@[fun_prop]
/-
**ContinuousOn.finset_sup'_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {L : Type u_1} {X : Type u_2} [inst : TopologicalSpace L] [inst_1 : Topo
logicalSpace X] {ι : Type u_3}   [inst_2 : SemilatticeSup L] [ContinuousSup L] {
s : Finset ι} {f : ι → X → L} {t : Set X} (hne : s.Nonempty),   (∀ i ∈ s, Contin
uousOn (f i) t) → ContinuousOn (fun a => s.sup' hne fun x => f x a) t
参数：hne : s.Nonempty；∀ i ∈ s, ContinuousOn (f i) t；fun a => s.sup' hne fun x => f
 x a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.finset_sup'_apply`：∀ {L : Type u_1} {X : Type u_2} [i
nst : TopologicalSpace L] [inst_1 : TopologicalSpace X] {ι : Type u_3}   [inst_2
 : SemilatticeSup L] [Cont…
-/
lemma ContinuousOn.finset_sup'_apply (hne : s.Nonempty) (hs : ∀ i ∈ s, ContinuousOn (f i) t) :
    ContinuousOn (fun a ↦ s.sup' hne (f · a)) t := fun x hx ↦
  ContinuousWithinAt.finset_sup'_apply hne fun i hi ↦ hs i hi x hx

@[fun_prop]
/-
**ContinuousOn.finset_sup'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.finset_sup'_apply (hne : s.Nonempty) (hs : forall i in s, Con
tinuousOn (f i) t) : ContinuousOn (fun a => s.sup' hne (f · a)) t
参数：hne : s.Nonempty；hs : forall i in s, ContinuousOn (f i) t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.finset_sup'`：ContinuousWithinAt.finset_sup'_apply (hn
e : s.Nonempty) (hs : forall i in s, ContinuousWithinAt (f i) t x) : ContinuousW
ithinAt (fun a => s.…
-/
lemma ContinuousOn.finset_sup' (hne : s.Nonempty) (hs : ∀ i ∈ s, ContinuousOn (f i) t) :
    ContinuousOn (s.sup' hne f) t := fun x hx ↦
  ContinuousWithinAt.finset_sup' hne fun i hi ↦ hs i hi x hx

@[fun_prop]
/-
**Continuous.finset_sup'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {L : Type u_1} {X : Type u_2} [inst : TopologicalSpace L] [inst_1 : Topo
logicalSpace X] {ι : Type u_3}   [inst_2 : SemilatticeSup L] [ContinuousSup L] {
s : Finset ι} {f : ι → X → L} (hne : s.Nonempty),   (∀ i ∈ s, Continuous (f i)) 
→ Continuous fun a => s.sup' hne fun x => f x a
参数：hne : s.Nonempty；∀ i ∈ s, Continuous (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.finset_sup'_apply`：∀ {L : Type u_1} {X : Type u_2} [inst : 
TopologicalSpace L] [inst_1 : TopologicalSpace X] {ι : Type u_3}   [inst_2 : Sem
ilatticeSup L] [Cont…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
lemma Continuous.finset_sup'_apply (hne : s.Nonempty) (hs : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun a ↦ s.sup' hne (f · a)) :=
  continuous_iff_continuousAt.2 fun _ ↦ ContinuousAt.finset_sup'_apply _ fun i hi ↦
    (hs i hi).continuousAt

@[fun_prop]
/-
**Continuous.finset_sup'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.finset_sup'_apply (hne : s.Nonempty) (hs : forall i in s, Conti
nuous (f i)) : Continuous (fun a => s.sup' hne (f · a))
参数：hne : s.Nonempty；hs : forall i in s, Continuous (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用引理 `ContinuousAt.finset_sup'`：ContinuousAt.finset_sup'_apply (hne : s.Nonemp
ty) (hs : forall i in s, ContinuousAt (f i) x) : ContinuousAt (fun a => s.sup' h
ne (f · a)) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
lemma Continuous.finset_sup' (hne : s.Nonempty) (hs : ∀ i ∈ s, Continuous (f i)) :
    Continuous (s.sup' hne f) :=
  continuous_iff_continuousAt.2 fun _ ↦ ContinuousAt.finset_sup' _ fun i hi ↦ (hs i hi).continuousAt

end FinsetSup'

section FinsetSup

variable {ι : Type*} [SemilatticeSup L] [OrderBot L] [ContinuousSup L] {s : Finset ι}
  {f : ι → X → L} {t : Set X} {x : X}

@[fun_prop]
/-
**ContinuousAt.finset_sup_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousAt.finset_sup_apply (hs : forall i in s, ContinuousAt (f i) x) :
 ContinuousAt (fun a => s.sup (f · a)) x
参数：hs : forall i in s, ContinuousAt (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Tendsto.finset_sup_nhds_apply`：finset_sup_nhds_apply [Semilattice
Sup L] [OrderBot L] [ContinuousSup L] (hs : forall i in s, Tendsto (f i) l (𝓝 (g
 i))) : Tendsto (fun a => …
-/
lemma ContinuousAt.finset_sup_apply (hs : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun a ↦ s.sup (f · a)) x :=
  Tendsto.finset_sup_nhds_apply hs

@[fun_prop]
/-
**ContinuousAt.finset_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousAt.finset_sup (hs : forall i in s, ContinuousAt (f i) x) : Conti
nuousAt (s.sup f) x
参数：hs : forall i in s, ContinuousAt (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ContinuousAt.finset_sup_apply`：ContinuousAt.finset_sup_apply (hs : foral
l i in s, ContinuousAt (f i) x) : ContinuousAt (fun a => s.sup (f · a)) x
-/
lemma ContinuousAt.finset_sup (hs : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (s.sup f) x := by
  simpa only [← Finset.sup_apply] using finset_sup_apply hs

@[fun_prop]
/-
**ContinuousWithinAt.finset_sup_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.finset_sup_apply (hs : forall i in s, ContinuousWithinA
t (f i) t x) : ContinuousWithinAt (fun a => s.sup (f · a)) t x
参数：hs : forall i in s, ContinuousWithinAt (f i) t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Tendsto.finset_sup_nhds_apply`：finset_sup_nhds_apply [Semilattice
Sup L] [OrderBot L] [ContinuousSup L] (hs : forall i in s, Tendsto (f i) l (𝓝 (g
 i))) : Tendsto (fun a => …
-/
lemma ContinuousWithinAt.finset_sup_apply
    (hs : ∀ i ∈ s, ContinuousWithinAt (f i) t x) :
    ContinuousWithinAt (fun a ↦ s.sup (f · a)) t x :=
  Tendsto.finset_sup_nhds_apply hs

@[fun_prop]
/-
**ContinuousWithinAt.finset_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.finset_sup (hs : forall i in s, ContinuousWithinAt (f i
) t x) : ContinuousWithinAt (s.sup f) t x
参数：hs : forall i in s, ContinuousWithinAt (f i) t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ContinuousWithinAt.finset_sup_apply`：ContinuousWithinAt.finset_sup_apply
 (hs : forall i in s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (fun a 
=> s.sup (f · a)) t x
-/
lemma ContinuousWithinAt.finset_sup
    (hs : ∀ i ∈ s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (s.sup f) t x := by
  simpa only [← Finset.sup_apply] using finset_sup_apply hs

@[fun_prop]
/-
**ContinuousOn.finset_sup_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.finset_sup_apply (hs : forall i in s, ContinuousOn (f i) t) :
 ContinuousOn (fun a => s.sup (f · a)) t
参数：hs : forall i in s, ContinuousOn (f i) t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.finset_sup_apply`：ContinuousWithinAt.finset_sup_apply
 (hs : forall i in s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (fun a 
=> s.sup (f · a)) t x
-/
lemma ContinuousOn.finset_sup_apply (hs : ∀ i ∈ s, ContinuousOn (f i) t) :
    ContinuousOn (fun a ↦ s.sup (f · a)) t := fun x hx ↦
  ContinuousWithinAt.finset_sup_apply fun i hi ↦ hs i hi x hx

@[fun_prop]
/-
**ContinuousOn.finset_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.finset_sup (hs : forall i in s, ContinuousOn (f i) t) : Conti
nuousOn (s.sup f) t
参数：hs : forall i in s, ContinuousOn (f i) t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.finset_sup`：ContinuousWithinAt.finset_sup (hs : foral
l i in s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (s.sup f) t x
-/
lemma ContinuousOn.finset_sup (hs : ∀ i ∈ s, ContinuousOn (f i) t) :
    ContinuousOn (s.sup f) t := fun x hx ↦
  ContinuousWithinAt.finset_sup fun i hi ↦ hs i hi x hx

@[fun_prop]
/-
**Continuous.finset_sup_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.finset_sup_apply (hs : forall i in s, Continuous (f i)) : Conti
nuous (fun a => s.sup (f · a))
参数：hs : forall i in s, Continuous (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用引理 `ContinuousAt.finset_sup_apply`：ContinuousAt.finset_sup_apply (hs : foral
l i in s, ContinuousAt (f i) x) : ContinuousAt (fun a => s.sup (f · a)) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
lemma Continuous.finset_sup_apply (hs : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun a ↦ s.sup (f · a)) :=
  continuous_iff_continuousAt.2 fun _ ↦ ContinuousAt.finset_sup_apply fun i hi ↦
    (hs i hi).continuousAt

@[fun_prop]
/-
**Continuous.finset_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.finset_sup (hs : forall i in s, Continuous (f i)) : Continuous 
(s.sup f)
参数：hs : forall i in s, Continuous (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用引理 `ContinuousAt.finset_sup`：ContinuousAt.finset_sup (hs : forall i in s, Co
ntinuousAt (f i) x) : ContinuousAt (s.sup f) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
lemma Continuous.finset_sup (hs : ∀ i ∈ s, Continuous (f i)) : Continuous (s.sup f) :=
  continuous_iff_continuousAt.2 fun _ ↦ ContinuousAt.finset_sup fun i hi ↦ (hs i hi).continuousAt

end FinsetSup

section FinsetInf'

variable {ι : Type*} [SemilatticeInf L] [ContinuousInf L] {s : Finset ι}
  {f : ι → X → L} {t : Set X} {x : X}

@[fun_prop]
/-
**ContinuousAt.finset_inf'_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：∀ {L : Type u_1} {X : Type u_2} [inst : TopologicalSpace L] [inst_1 : Topo
logicalSpace X] {ι : Type u_3}   [inst_2 : SemilatticeInf L] [ContinuousInf L] {
s : Finset ι} {f : ι → X → L} {x : X} (hne : s.Nonempty),   (∀ i ∈ s, Continuous
At (f i) x) → ContinuousAt (fun a => s.inf' hne fun x => f x a) x
参数：hne : s.Nonempty；∀ i ∈ s, ContinuousAt (f i) x；fun a => s.inf' hne fun x => f
 x a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.finset_inf'_nhds_apply`：∀ {L : Type u_1} [inst : Topologi
calSpace L] {ι : Type u_3} {α : Type u_4} {s : Finset ι} {f : ι → α → L} {l : Fi
lter α}   {g : ι → L} [inst…
-/
lemma ContinuousAt.finset_inf'_apply (hne : s.Nonempty) (hs : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun a ↦ s.inf' hne (f · a)) x :=
  Tendsto.finset_inf'_nhds_apply hne hs

@[fun_prop]
/-
**ContinuousAt.finset_inf'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousAt.finset_inf'_apply (hne : s.Nonempty) (hs : forall i in s, Con
tinuousAt (f i) x) : ContinuousAt (fun a => s.inf' hne (f · a)) x
参数：hne : s.Nonempty；hs : forall i in s, ContinuousAt (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousAt.finset_inf'_apply`：∀ {L : Type u_1} {X : Type u_2} [inst : 
TopologicalSpace L] [inst_1 : TopologicalSpace X] {ι : Type u_3}   [inst_2 : Sem
ilatticeInf L] [Cont…
-/
lemma ContinuousAt.finset_inf' (hne : s.Nonempty) (hs : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (s.inf' hne f) x := by
  simpa only [← Finset.inf'_apply] using finset_inf'_apply hne hs

@[fun_prop]
/-
**ContinuousWithinAt.finset_inf'_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousWith
inAt`。
形式化陈述：∀ {L : Type u_1} {X : Type u_2} [inst : TopologicalSpace L] [inst_1 : Topo
logicalSpace X] {ι : Type u_3}   [inst_2 : SemilatticeInf L] [ContinuousInf L] {
s : Finset ι} {f : ι → X → L} {t : Set X} {x : X} (hne : s.Nonempty),   (∀ i ∈ s
, ContinuousWithinAt (f i) t x) → ContinuousWithinAt (fun a => s.inf' hne fun x 
=> f x a) t x
参数：hne : s.Nonempty；∀ i ∈ s, ContinuousWithinAt (f i) t x；fun a => s.inf' hne fu
n x => f x a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.finset_inf'_nhds_apply`：∀ {L : Type u_1} [inst : Topologi
calSpace L] {ι : Type u_3} {α : Type u_4} {s : Finset ι} {f : ι → α → L} {l : Fi
lter α}   {g : ι → L} [inst…
-/
lemma ContinuousWithinAt.finset_inf'_apply (hne : s.Nonempty)
    (hs : ∀ i ∈ s, ContinuousWithinAt (f i) t x) :
    ContinuousWithinAt (fun a ↦ s.inf' hne (f · a)) t x :=
  Tendsto.finset_inf'_nhds_apply hne hs

@[fun_prop]
/-
**ContinuousWithinAt.finset_inf'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.finset_inf'_apply (hne : s.Nonempty) (hs : forall i in 
s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (fun a => s.inf' hne (f · 
a)) t x
参数：hne : s.Nonempty；hs : forall i in s, ContinuousWithinAt (f i) t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousWithinAt.finset_inf'_apply`：∀ {L : Type u_1} {X : Type u_2} [i
nst : TopologicalSpace L] [inst_1 : TopologicalSpace X] {ι : Type u_3}   [inst_2
 : SemilatticeInf L] [Cont…
-/
lemma ContinuousWithinAt.finset_inf' (hne : s.Nonempty)
    (hs : ∀ i ∈ s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (s.inf' hne f) t x := by
  simpa only [← Finset.inf'_apply] using finset_inf'_apply hne hs

@[fun_prop]
/-
**ContinuousOn.finset_inf'_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {L : Type u_1} {X : Type u_2} [inst : TopologicalSpace L] [inst_1 : Topo
logicalSpace X] {ι : Type u_3}   [inst_2 : SemilatticeInf L] [ContinuousInf L] {
s : Finset ι} {f : ι → X → L} {t : Set X} (hne : s.Nonempty),   (∀ i ∈ s, Contin
uousOn (f i) t) → ContinuousOn (fun a => s.inf' hne fun x => f x a) t
参数：hne : s.Nonempty；∀ i ∈ s, ContinuousOn (f i) t；fun a => s.inf' hne fun x => f
 x a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.finset_inf'_apply`：∀ {L : Type u_1} {X : Type u_2} [i
nst : TopologicalSpace L] [inst_1 : TopologicalSpace X] {ι : Type u_3}   [inst_2
 : SemilatticeInf L] [Cont…
-/
lemma ContinuousOn.finset_inf'_apply (hne : s.Nonempty) (hs : ∀ i ∈ s, ContinuousOn (f i) t) :
    ContinuousOn (fun a ↦ s.inf' hne (f · a)) t := fun x hx ↦
  ContinuousWithinAt.finset_inf'_apply hne fun i hi ↦ hs i hi x hx

@[fun_prop]
/-
**ContinuousOn.finset_inf'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.finset_inf'_apply (hne : s.Nonempty) (hs : forall i in s, Con
tinuousOn (f i) t) : ContinuousOn (fun a => s.inf' hne (f · a)) t
参数：hne : s.Nonempty；hs : forall i in s, ContinuousOn (f i) t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.finset_inf'`：ContinuousWithinAt.finset_inf'_apply (hn
e : s.Nonempty) (hs : forall i in s, ContinuousWithinAt (f i) t x) : ContinuousW
ithinAt (fun a => s.…
-/
lemma ContinuousOn.finset_inf' (hne : s.Nonempty) (hs : ∀ i ∈ s, ContinuousOn (f i) t) :
    ContinuousOn (s.inf' hne f) t := fun x hx ↦
  ContinuousWithinAt.finset_inf' hne fun i hi ↦ hs i hi x hx

@[fun_prop]
/-
**Continuous.finset_inf'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {L : Type u_1} {X : Type u_2} [inst : TopologicalSpace L] [inst_1 : Topo
logicalSpace X] {ι : Type u_3}   [inst_2 : SemilatticeInf L] [ContinuousInf L] {
s : Finset ι} {f : ι → X → L} (hne : s.Nonempty),   (∀ i ∈ s, Continuous (f i)) 
→ Continuous fun a => s.inf' hne fun x => f x a
参数：hne : s.Nonempty；∀ i ∈ s, Continuous (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.finset_inf'_apply`：∀ {L : Type u_1} {X : Type u_2} [inst : 
TopologicalSpace L] [inst_1 : TopologicalSpace X] {ι : Type u_3}   [inst_2 : Sem
ilatticeInf L] [Cont…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
lemma Continuous.finset_inf'_apply (hne : s.Nonempty) (hs : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun a ↦ s.inf' hne (f · a)) :=
  continuous_iff_continuousAt.2 fun _ ↦ ContinuousAt.finset_inf'_apply _ fun i hi ↦
    (hs i hi).continuousAt

@[fun_prop]
/-
**Continuous.finset_inf'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.finset_inf'_apply (hne : s.Nonempty) (hs : forall i in s, Conti
nuous (f i)) : Continuous (fun a => s.inf' hne (f · a))
参数：hne : s.Nonempty；hs : forall i in s, Continuous (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用引理 `ContinuousAt.finset_inf'`：ContinuousAt.finset_inf'_apply (hne : s.Nonemp
ty) (hs : forall i in s, ContinuousAt (f i) x) : ContinuousAt (fun a => s.inf' h
ne (f · a)) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
lemma Continuous.finset_inf' (hne : s.Nonempty) (hs : ∀ i ∈ s, Continuous (f i)) :
    Continuous (s.inf' hne f) :=
  continuous_iff_continuousAt.2 fun _ ↦ ContinuousAt.finset_inf' _ fun i hi ↦ (hs i hi).continuousAt

end FinsetInf'

section FinsetInf

variable {ι : Type*} [SemilatticeInf L] [OrderTop L] [ContinuousInf L] {s : Finset ι}
  {f : ι → X → L} {t : Set X} {x : X}

@[fun_prop]
/-
**ContinuousAt.finset_inf_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousAt.finset_inf_apply (hs : forall i in s, ContinuousAt (f i) x) :
 ContinuousAt (fun a => s.inf (f · a)) x
参数：hs : forall i in s, ContinuousAt (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Tendsto.finset_inf_nhds_apply`：finset_inf_nhds_apply [Semilattice
Inf L] [OrderTop L] [ContinuousInf L] (hs : forall i in s, Tendsto (f i) l (𝓝 (g
 i))) : Tendsto (fun a => …
-/
lemma ContinuousAt.finset_inf_apply (hs : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun a ↦ s.inf (f · a)) x :=
  Tendsto.finset_inf_nhds_apply hs

@[fun_prop]
/-
**ContinuousAt.finset_inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousAt.finset_inf (hs : forall i in s, ContinuousAt (f i) x) : Conti
nuousAt (s.inf f) x
参数：hs : forall i in s, ContinuousAt (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ContinuousAt.finset_inf_apply`：ContinuousAt.finset_inf_apply (hs : foral
l i in s, ContinuousAt (f i) x) : ContinuousAt (fun a => s.inf (f · a)) x
-/
lemma ContinuousAt.finset_inf (hs : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (s.inf f) x := by
  simpa only [← Finset.inf_apply] using finset_inf_apply hs

@[fun_prop]
/-
**ContinuousWithinAt.finset_inf_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.finset_inf_apply (hs : forall i in s, ContinuousWithinA
t (f i) t x) : ContinuousWithinAt (fun a => s.inf (f · a)) t x
参数：hs : forall i in s, ContinuousWithinAt (f i) t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.Tendsto.finset_inf_nhds_apply`：finset_inf_nhds_apply [Semilattice
Inf L] [OrderTop L] [ContinuousInf L] (hs : forall i in s, Tendsto (f i) l (𝓝 (g
 i))) : Tendsto (fun a => …
-/
lemma ContinuousWithinAt.finset_inf_apply
    (hs : ∀ i ∈ s, ContinuousWithinAt (f i) t x) :
    ContinuousWithinAt (fun a ↦ s.inf (f · a)) t x :=
  Tendsto.finset_inf_nhds_apply hs

@[fun_prop]
/-
**ContinuousWithinAt.finset_inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.finset_inf (hs : forall i in s, ContinuousWithinAt (f i
) t x) : ContinuousWithinAt (s.inf f) t x
参数：hs : forall i in s, ContinuousWithinAt (f i) t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ContinuousWithinAt.finset_inf_apply`：ContinuousWithinAt.finset_inf_apply
 (hs : forall i in s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (fun a 
=> s.inf (f · a)) t x
-/
lemma ContinuousWithinAt.finset_inf
    (hs : ∀ i ∈ s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (s.inf f) t x := by
  simpa only [← Finset.inf_apply] using finset_inf_apply hs

@[fun_prop]
/-
**ContinuousOn.finset_inf_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.finset_inf_apply (hs : forall i in s, ContinuousOn (f i) t) :
 ContinuousOn (fun a => s.inf (f · a)) t
参数：hs : forall i in s, ContinuousOn (f i) t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.finset_inf_apply`：ContinuousWithinAt.finset_inf_apply
 (hs : forall i in s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (fun a 
=> s.inf (f · a)) t x
-/
lemma ContinuousOn.finset_inf_apply (hs : ∀ i ∈ s, ContinuousOn (f i) t) :
    ContinuousOn (fun a ↦ s.inf (f · a)) t := fun x hx ↦
  ContinuousWithinAt.finset_inf_apply fun i hi ↦ hs i hi x hx

@[fun_prop]
/-
**ContinuousOn.finset_inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.finset_inf (hs : forall i in s, ContinuousOn (f i) t) : Conti
nuousOn (s.inf f) t
参数：hs : forall i in s, ContinuousOn (f i) t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.finset_inf`：ContinuousWithinAt.finset_inf (hs : foral
l i in s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (s.inf f) t x
-/
lemma ContinuousOn.finset_inf (hs : ∀ i ∈ s, ContinuousOn (f i) t) :
    ContinuousOn (s.inf f) t := fun x hx ↦
  ContinuousWithinAt.finset_inf fun i hi ↦ hs i hi x hx

@[fun_prop]
/-
**Continuous.finset_inf_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.finset_inf_apply (hs : forall i in s, Continuous (f i)) : Conti
nuous (fun a => s.inf (f · a))
参数：hs : forall i in s, Continuous (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用引理 `ContinuousAt.finset_inf_apply`：ContinuousAt.finset_inf_apply (hs : foral
l i in s, ContinuousAt (f i) x) : ContinuousAt (fun a => s.inf (f · a)) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
lemma Continuous.finset_inf_apply (hs : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun a ↦ s.inf (f · a)) :=
  continuous_iff_continuousAt.2 fun _ ↦ ContinuousAt.finset_inf_apply fun i hi ↦
    (hs i hi).continuousAt

@[fun_prop]
/-
**Continuous.finset_inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.finset_inf (hs : forall i in s, Continuous (f i)) : Continuous 
(s.inf f)
参数：hs : forall i in s, Continuous (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用引理 `ContinuousAt.finset_inf`：ContinuousAt.finset_inf (hs : forall i in s, Co
ntinuousAt (f i) x) : ContinuousAt (s.inf f) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
lemma Continuous.finset_inf (hs : ∀ i ∈ s, Continuous (f i)) : Continuous (s.inf f) :=
  continuous_iff_continuousAt.2 fun _ ↦ ContinuousAt.finset_inf fun i hi ↦ (hs i hi).continuousAt

end FinsetInf

