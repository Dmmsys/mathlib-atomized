/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
module

public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Contractible spaces

In this file, we define `ContractibleSpace`, a space that is homotopy equivalent to `Unit`.
-/

@[expose] public section

noncomputable section

namespace ContinuousMap

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A map is nullhomotopic if it is homotopic to a constant map. -/
/-
**ContinuousMap.Nullhomotopic** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：Nullhomotopic (f : C(X, Y)) : Prop
参数：f : C(X, Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map is nullhomotopic if it is homotopic to a constant map.
-/
def Nullhomotopic (f : C(X, Y)) : Prop :=
  ∃ y : Y, Homotopic f (ContinuousMap.const _ y)
/-
**ContinuousMap.nullhomotopic_of_constant** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ap`。
形式化陈述：nullhomotopic_of_constant (y : Y) : Nullhomotopic (ContinuousMap.const X y
)
参数：y : Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.Homotopic.refl`：refl (f : C(X, Y)) : Homotopic f f
-/
theorem nullhomotopic_of_constant (y : Y) : Nullhomotopic (ContinuousMap.const X y) :=
  ⟨y, by rfl⟩
/-
**ContinuousMap.Nullhomotopic.comp_right** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMa
p.Nullhomotopic`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] {f : C(X, Y)}, f.
Nullhomotopic → ∀ (g : C(Y, Z)), (g.comp f).Nullhomotopic
参数：X, Y；g : C(Y, Z)；g.comp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.Homotopic.comp`：comp {g₀ g₁ : C(Y, Z)} {f₀ f₁ : C(X, Y)} (
hg : Homotopic g₀ g₁) (hf : Homotopic f₀ f₁) : Homotopic (g₀.comp f₀) (g₁.comp f
₁)
· 使用定理 `ContinuousMap.Homotopic.refl`：refl (f : C(X, Y)) : Homotopic f f
-/
theorem Nullhomotopic.comp_right {f : C(X, Y)} (hf : f.Nullhomotopic) (g : C(Y, Z)) :
    (g.comp f).Nullhomotopic := by
  obtain ⟨y, hy⟩ := hf
  use g y
  exact .comp (.refl g) hy
/-
**ContinuousMap.Nullhomotopic.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
.Nullhomotopic`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] {f : C(Y, Z)}, f.
Nullhomotopic → ∀ (g : C(X, Y)), (f.comp g).Nullhomotopic
参数：Y, Z；g : C(X, Y)；f.comp g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.Homotopic.comp`：comp {g₀ g₁ : C(Y, Z)} {f₀ f₁ : C(X, Y)} (
hg : Homotopic g₀ g₁) (hf : Homotopic f₀ f₁) : Homotopic (g₀.comp f₀) (g₁.comp f
₁)
· 使用定理 `ContinuousMap.Homotopic.refl`：refl (f : C(X, Y)) : Homotopic f f
-/
theorem Nullhomotopic.comp_left {f : C(Y, Z)} (hf : f.Nullhomotopic) (g : C(X, Y)) :
    (f.comp g).Nullhomotopic := by
  obtain ⟨y, hy⟩ := hf
  use y
  exact .comp hy (.refl g)

end ContinuousMap

open ContinuousMap

/-- A contractible space is one that is homotopy equivalent to `Unit`. -/
/-
**ContractibleSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_1) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A contractible space is one that is homotopy equivalent to `Unit`.
-/
class ContractibleSpace (X : Type*) [TopologicalSpace X] : Prop where
  hequiv_unit' : Nonempty (X ≃ₕ Unit)
/-
**ContractibleSpace.hequiv_unit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContractibleSpace.hequiv_unit (X : Type*) [TopologicalSpace X] [Contractib
leSpace X] : Nonempty (X ≃ₕ Unit)
参数：X : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContractibleSpace.hequiv_unit'`：∀ {X : Type u_1} {inst : TopologicalSpac
e X} [self : ContractibleSpace X], Nonempty (ContinuousMap.HomotopyEquiv X Unit)
-/
theorem ContractibleSpace.hequiv_unit (X : Type*) [TopologicalSpace X] [ContractibleSpace X] :
    Nonempty (X ≃ₕ Unit) :=
  ContractibleSpace.hequiv_unit'
/-
**id_nullhomotopic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：id_nullhomotopic (X : Type*) [TopologicalSpace X] [ContractibleSpace X] : 
(ContinuousMap.id X).Nullhomotopic
参数：X : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContractibleSpace.hequiv_unit`：ContractibleSpace.hequiv_unit (X : Type*)
 [TopologicalSpace X] [ContractibleSpace X] : Nonempty (X ≃ₕ Unit)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.Homotopic.symm`：symm ⦃f g : C(X, Y)⦄ (h : Homotopic f g) :
 Homotopic g f
· 使用定理 `ContinuousMap.HomotopyEquiv.left_inv`：∀ {X : Type u} {Y : Type v} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : ContinuousMap.Homo
topyEquiv X Y), (self.invF…
-/
theorem id_nullhomotopic (X : Type*) [TopologicalSpace X] [ContractibleSpace X] :
    (ContinuousMap.id X).Nullhomotopic := by
  obtain ⟨hv⟩ := ContractibleSpace.hequiv_unit X
  use hv.invFun ()
  convert! hv.left_inv.symm
/-
**contractible_iff_id_nullhomotopic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contractible_iff_id_nullhomotopic (Y : Type*) [TopologicalSpace Y] : Contr
actibleSpace Y ↔ (ContinuousMap.id Y).Nullhomotopic
参数：Y : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `id_nullhomotopic`：id_nullhomotopic (X : Type*) [TopologicalSpace X] [Con
tractibleSpace X] : (ContinuousMap.id X).Nullhomotopic
· 使用定理 `ContinuousMap.Homotopic.symm`：symm ⦃f g : C(X, Y)⦄ (h : Homotopic f g) :
 Homotopic g f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.Homotopic.refl`：refl (f : C(X, Y)) : Homotopic f f
-/
theorem contractible_iff_id_nullhomotopic (Y : Type*) [TopologicalSpace Y] :
    ContractibleSpace Y ↔ (ContinuousMap.id Y).Nullhomotopic := by
  constructor
  · intro
    apply id_nullhomotopic
  rintro ⟨p, h⟩
  refine
    { hequiv_unit' :=
        ⟨{  toFun := ContinuousMap.const _ ()
            invFun := ContinuousMap.const _ p
            left_inv := ?_
            right_inv := ?_ }⟩ }
  · exact h.symm
  · convert! Homotopic.refl (ContinuousMap.id Unit)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
/-
**ContinuousMap.HomotopyEquiv.contractibleSpace** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousMap.HomotopyEquiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [ContractibleSpace Y]   (e : ContinuousMap.HomotopyEquiv X Y), C
ontractibleSpace X
参数：e : ContinuousMap.HomotopyEquiv X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `ContractibleSpace.hequiv_unit`：ContractibleSpace.hequiv_unit (X : Type*)
 [TopologicalSpace X] [ContractibleSpace X] : Nonempty (X ≃ₕ Unit)
-/
protected theorem ContinuousMap.HomotopyEquiv.contractibleSpace [ContractibleSpace Y] (e : X ≃ₕ Y) :
    ContractibleSpace X :=
  ⟨(ContractibleSpace.hequiv_unit Y).map e.trans⟩
/-
**ContinuousMap.HomotopyEquiv.contractibleSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousMap.HomotopyEquiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e : ContinuousMap.HomotopyEquiv X Y), ContractibleSpace X ↔ C
ontractibleSpace Y
参数：e : ContinuousMap.HomotopyEquiv X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyEquiv.contractibleSpace`：∀ {X : Type u_1} {Y : Typ
e u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [ContractibleSp
ace Y]   (e : ContinuousMap.Homotop…
-/
protected theorem ContinuousMap.HomotopyEquiv.contractibleSpace_iff (e : X ≃ₕ Y) :
    ContractibleSpace X ↔ ContractibleSpace Y :=
  ⟨fun _ => e.symm.contractibleSpace, fun _ => e.contractibleSpace⟩
/-
**Homeomorph.contractibleSpace** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [ContractibleSpace Y]   (e : X ≃ₜ Y), ContractibleSpace X
参数：e : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyEquiv.contractibleSpace`：∀ {X : Type u_1} {Y : Typ
e u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [ContractibleSp
ace Y]   (e : ContinuousMap.Homotop…
-/
protected theorem Homeomorph.contractibleSpace [ContractibleSpace Y] (e : X ≃ₜ Y) :
    ContractibleSpace X :=
  e.toHomotopyEquiv.contractibleSpace
/-
**Homeomorph.contractibleSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (e : X ≃ₜ Y),   ContractibleSpace X ↔ ContractibleSpace Y
参数：e : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyEquiv.contractibleSpace_iff`：∀ {X : Type u_1} {Y :
 Type u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : Cont
inuousMap.HomotopyEquiv X Y), Contracti…
-/
protected theorem Homeomorph.contractibleSpace_iff (e : X ≃ₜ Y) :
    ContractibleSpace X ↔ ContractibleSpace Y :=
  e.toHomotopyEquiv.contractibleSpace_iff
/-
**homotopic_of_indiscrete** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：homotopic_of_indiscrete [IndiscreteTopology Y] (f g : C(X, Y)) : f.Homotop
ic g
参数：f g : C(X, Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_indiscreteTopology`：continuous_of_indiscreteTopology {β} [
TopologicalSpace β] [IndiscreteTopology β] {f : α -> β} : Continuous f where isO
pen_preimage
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `unitInterval.instNontrivialElemReal`：Nontrivial ↑unitInterval
-/
lemma homotopic_of_indiscrete [IndiscreteTopology Y] (f g : C(X, Y)) : f.Homotopic g :=
  ⟨⟨fun (t, a) ↦ if t = 0 then f a else g a, continuous_of_indiscreteTopology⟩, by simp, by simp⟩
/-
**nullhomotopic_of_indiscrete** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nullhomotopic_of_indiscrete [Nonempty Y] [IndiscreteTopology Y] (f : C(X, 
Y)) : f.Nullhomotopic
参数：f : C(X, Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `homotopic_of_indiscrete`：homotopic_of_indiscrete [IndiscreteTopology Y] 
(f g : C(X, Y)) : f.Homotopic g
-/
lemma nullhomotopic_of_indiscrete [Nonempty Y] [IndiscreteTopology Y] (f : C(X, Y)) :
    f.Nullhomotopic := by
  inhabit Y
  use default
  exact homotopic_of_indiscrete _ _

namespace ContractibleSpace

/-
**ContractibleSpace.** 是 Mathlib 中的一个实例，位于命名空间 `ContractibleSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty Y] [Subsingleton Y] : ContractibleSpace Y :=
  let ⟨_⟩ := nonempty_unique Y
  ⟨⟨(Homeomorph.homeomorphOfUnique Y Unit).toHomotopyEquiv⟩⟩
/-
**ContractibleSpace.** 是 Mathlib 中的一个实例，位于命名空间 `ContractibleSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty Y] [IndiscreteTopology Y] : ContractibleSpace Y :=
  (contractible_iff_id_nullhomotopic Y).mpr (nullhomotopic_of_indiscrete _)

variable (X Y) in
/-
**ContractibleSpace.hequiv** 是 Mathlib 中的一个定理，位于命名空间 `ContractibleSpace`。
形式化陈述：hequiv [ContractibleSpace X] [ContractibleSpace Y] : Nonempty (X ≃ₕ Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContractibleSpace.hequiv_unit'`：∀ {X : Type u_1} {inst : TopologicalSpac
e X} [self : ContractibleSpace X], Nonempty (ContinuousMap.HomotopyEquiv X Unit)
-/
theorem hequiv [ContractibleSpace X] [ContractibleSpace Y] :
    Nonempty (X ≃ₕ Y) := by
  rcases ContractibleSpace.hequiv_unit' (X := X) with ⟨h⟩
  rcases ContractibleSpace.hequiv_unit' (X := Y) with ⟨h'⟩
  exact ⟨h.trans h'.symm⟩
/-
**ContractibleSpace.** 是 Mathlib 中的一个实例，位于命名空间 `ContractibleSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [ContractibleSpace X] : PathConnectedSpace X := by
  obtain ⟨p, ⟨h⟩⟩ := id_nullhomotopic X
  have : ∀ x, Joined p x := fun x => ⟨(h.evalAt x).symm⟩
  rw [pathConnectedSpace_iff_eq]; use p; ext; tauto

/-- The product of two contractible spaces is contractible. -/
/-
**ContractibleSpace.** 是 Mathlib 中的一个实例，位于命名空间 `ContractibleSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two contractible spaces is contractible.
-/
instance [ContractibleSpace X] [ContractibleSpace Y] : ContractibleSpace (X × Y) := by
  obtain ⟨hX⟩ := hequiv_unit' (X := X)
  obtain ⟨hY⟩ := hequiv_unit' (X := Y)
  refine ⟨⟨(hX.prodCongr hY).trans ?_⟩⟩
  exact (Homeomorph.prodUnique Unit Unit).toHomotopyEquiv

end ContractibleSpace

