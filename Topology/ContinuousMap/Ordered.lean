/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shing Tak Lam
-/
module

public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.ContinuousMap.Defs

/-!
# Bundled continuous maps into orders, with order-compatible topology

-/

@[expose] public section


variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

namespace ContinuousMap

/-!
We now set up the partial order and lattice structure (given by pointwise min and max)
on continuous functions.
-/

/-
**ContinuousMap.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：partialOrder [PartialOrder β] : PartialOrder C(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We now set up the partial order and lattice structure (given by pointwise min an
d max)
on continuous functions.
-/
instance partialOrder [PartialOrder β] : PartialOrder C(α, β) := fast_instance%
  PartialOrder.lift (fun f => f.toFun) (fun f g _ => by aesop)
/-
**ContinuousMap.le_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：le_def [PartialOrder β] {f g : C(α, β)} : f <= g ↔ forall a, f a <= g a
参数：α, β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.le_def`：Pi.le_def {ι : Type*} {π : ι -> Type*} [forall i, LE (π i)] {
x y : forall i, π i} : x <= y ↔ forall i, x i <= y i
-/
theorem le_def [PartialOrder β] {f g : C(α, β)} : f ≤ g ↔ ∀ a, f a ≤ g a :=
  Pi.le_def
/-
**ContinuousMap.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：lt_def [PartialOrder β] {f g : C(α, β)} : f < g ↔ (forall a, f a <= g a) ∧
 exists a, f a < g a
参数：α, β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
-/
theorem lt_def [PartialOrder β] {f g : C(α, β)} : f < g ↔ (∀ a, f a ≤ g a) ∧ ∃ a, f a < g a :=
  Pi.lt_def

section SemilatticeSup
variable [SemilatticeSup β] [ContinuousSup β]

/-
**ContinuousMap.sup** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：sup : Max C(α, β) where max f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sup : Max C(α, β) where max f g := { toFun := fun a ↦ f a ⊔ g a }
/-
**ContinuousMap.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] [inst_2 : SemilatticeSup β]   [inst_3 : ContinuousSup β] (f g : 
C(α, β)), ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
参数：f g : C(α, β)；f ⊔ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_sup (f g : C(α, β)) : ⇑(f ⊔ g) = ⇑f ⊔ g := rfl
/-
**ContinuousMap.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] [inst_2 : SemilatticeSup β]   [inst_3 : ContinuousSup β] (f g : 
C(α, β)) (a : α), (f ⊔ g) a = f a ⊔ g a
参数：f g : C(α, β)；a : α；f ⊔ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sup_apply (f g : C(α, β)) (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl
/-
**ContinuousMap.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：semilatticeSup : SemilatticeSup C(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeSup : SemilatticeSup C(α, β) := fast_instance%
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ ↦ rfl
/-
**ContinuousMap.sup'_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] [inst_2 : SemilatticeSup β]   [inst_3 : ContinuousSup β] {ι : Ty
pe u_3} {s : Finset ι} (H : s.Nonempty) (f : ι → C(α, β)) (a : α),   (s.sup' H f
) a = s.sup' H fun i => (f i) a
参数：H : s.Nonempty；f : ι → C(α, β)；a : α；s.sup' H f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_sup'_eq_sup'_comp`：∀ {α : Type u_2} {β : Type u_3} {γ : Typ
e u_4} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup γ] {s : Finset β}   (H
 : s.Nonempty) {f : …
-/
lemma sup'_apply {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C(α, β)) (a : α) :
    s.sup' H f a = s.sup' H fun i ↦ f i a :=
  Finset.apply_sup'_eq_sup'_comp H (fun g : C(α, β) ↦ g a) fun _ _ ↦ rfl

@[simp, norm_cast]
/-
**ContinuousMap.coe_sup'** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_sup' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C(α, β)) : 
⇑(s.sup' H f) = s.sup' H fun i => ⇑(f i)
参数：H : s.Nonempty；f : ι -> C(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.sup'_apply`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : SemilatticeSup β]   [inst_
3 : Continuous…
· 使用定理 `Finset.sup'_apply`：∀ {α : Type u_2} {β : Type u_3} {C : β → Type u_7} [i
nst : (b : β) → SemilatticeSup (C b)] {s : Finset α}   (H : s.Nonempty) (f : α →
 (b : β…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_sup' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C(α, β)) :
    ⇑(s.sup' H f) = s.sup' H fun i ↦ ⇑(f i) := by ext; simp [sup'_apply]

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf β] [ContinuousInf β]

/-
**ContinuousMap.inf** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：inf : Min C(α, β) where min f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inf : Min C(α, β) where min f g := { toFun := fun a ↦ f a ⊓ g a }
/-
**ContinuousMap.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] [inst_2 : SemilatticeInf β]   [inst_3 : ContinuousInf β] (f g : 
C(α, β)), ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
参数：f g : C(α, β)；f ⊓ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inf (f g : C(α, β)) : ⇑(f ⊓ g) = ⇑f ⊓ g := rfl
/-
**ContinuousMap.inf_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] [inst_2 : SemilatticeInf β]   [inst_3 : ContinuousInf β] (f g : 
C(α, β)) (a : α), (f ⊓ g) a = f a ⊓ g a
参数：f g : C(α, β)；a : α；f ⊓ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inf_apply (f g : C(α, β)) (a : α) : (f ⊓ g) a = f a ⊓ g a := rfl
/-
**ContinuousMap.semilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：semilatticeInf : SemilatticeInf C(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeInf : SemilatticeInf C(α, β) := fast_instance%
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl
/-
**ContinuousMap.inf'_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] [inst_2 : SemilatticeInf β]   [inst_3 : ContinuousInf β] {ι : Ty
pe u_3} {s : Finset ι} (H : s.Nonempty) (f : ι → C(α, β)) (a : α),   (s.inf' H f
) a = s.inf' H fun i => (f i) a
参数：H : s.Nonempty；f : ι → C(α, β)；a : α；s.inf' H f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_inf'_eq_inf'_comp`：∀ {α : Type u_2} {β : Type u_3} {γ : Typ
e u_4} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf γ] {s : Finset β}   (H
 : s.Nonempty) {f : …
-/
lemma inf'_apply {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C(α, β)) (a : α) :
    s.inf' H f a = s.inf' H fun i ↦ f i a :=
  Finset.apply_inf'_eq_inf'_comp H (fun g : C(α, β) ↦ g a) fun _ _ ↦ rfl

@[simp, norm_cast]
/-
**ContinuousMap.coe_inf'** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_inf' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι -> C(α, β)) : 
⇑(s.inf' H f) = s.inf' H fun i => ⇑(f i)
参数：H : s.Nonempty；f : ι -> C(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.inf'_apply`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : SemilatticeInf β]   [inst_
3 : Continuous…
· 使用定理 `Finset.inf'_apply`：∀ {α : Type u_2} {β : Type u_3} {C : β → Type u_7} [i
nst : (b : β) → SemilatticeInf (C b)] {s : Finset α}   (H : s.Nonempty) (f : α →
 (b : β…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_inf' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C(α, β)) :
    ⇑(s.inf' H f) = s.inf' H fun i ↦ ⇑(f i) := by ext; simp [inf'_apply]

end SemilatticeInf

/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Lattice β] [TopologicalLattice β] : Lattice C(α, β) where

-- TODO transfer this lattice structure to `BoundedContinuousFunction`

section Extend

variable [LinearOrder α] [OrderTopology α] {a b : α} (h : a ≤ b)

/-- Extend a continuous function `f : C(Set.Icc a b, β)` to a function `f : C(α, β)`. -/
/-
**ContinuousMap.IccExtend** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：IccExtend (f : C(Set.Icc a b, β)) : C(α, β) where toFun
参数：f : C(Set.Icc a b, β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a continuous function `f : C(Set.Icc a b, β)` to a function `f : C(α, β)`
.
-/
def IccExtend (f : C(Set.Icc a b, β)) : C(α, β) where
  toFun := Set.IccExtend h f

@[simp]
/-
**ContinuousMap.coe_IccExtend** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_IccExtend (f : C(Set.Icc a b, β)) : ((IccExtend h f : C(α, β)) : α -> 
β) = Set.IccExtend h f
参数：f : C(Set.Icc a b, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_IccExtend (f : C(Set.Icc a b, β)) :
    ((IccExtend h f : C(α, β)) : α → β) = Set.IccExtend h f :=
  rfl

end Extend

end ContinuousMap

