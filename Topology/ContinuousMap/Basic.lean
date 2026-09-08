/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Data.Set.UnionLift
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Continuous bundled maps

In this file we define the type `ContinuousMap` of continuous bundled maps.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.
-/

@[expose] public section


open Function Topology

section ContinuousMapClass

variable {F α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [FunLike F α β]
variable [ContinuousMapClass F α β]

/-
**map_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_continuousAt (f : F) (a : α) : ContinuousAt f a
参数：f : F；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
-/
theorem map_continuousAt (f : F) (a : α) : ContinuousAt f a :=
  (map_continuous f).continuousAt
/-
**map_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_continuousWithinAt (f : F) (s : Set α) (a : α) : ContinuousWithinAt f 
s a
参数：f : F；s : Set α；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
-/
theorem map_continuousWithinAt (f : F) (s : Set α) (a : α) : ContinuousWithinAt f s a :=
  (map_continuous f).continuousWithinAt

end ContinuousMapClass

/-! ### Continuous maps -/


namespace ContinuousMap

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

variable {f g : C(α, β)}

/-- Deprecated. Use `map_continuousAt` instead. -/
/-
**ContinuousMap.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] (f : C(α, β)) (x : α),   ContinuousAt (⇑f) x
参数：f : C(α, β)；x : α；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_continuousAt`：map_continuousAt (f : F) (a : α) : ContinuousAt f a

--- 原说明 ---
Deprecated. Use `map_continuousAt` instead.
-/
protected theorem continuousAt (f : C(α, β)) (x : α) : ContinuousAt f x :=
  map_continuousAt f x
/-
**ContinuousMap.map_specializes** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：map_specializes (f : C(α, β)) {x y : α} (h : x ⤳ y) : f x ⤳ f y
参数：f : C(α, β)；h : x ⤳ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.map`：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳
 f y
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
-/
theorem map_specializes (f : C(α, β)) {x y : α} (h : x ⤳ y) : f x ⤳ f y :=
  h.map f.2

section DiscreteTopology
variable [DiscreteTopology α]

/--
The continuous functions from `α` to `β` are the same as the plain functions when `α` is discrete.
-/
@[simps]
/-
**ContinuousMap.equivFnOfDiscrete** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：equivFnOfDiscrete : C(α, β) ≃ (α -> β)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f

--- 原说明 ---
The continuous functions from `α` to `β` are the same as the plain functions whe
n `α` is discrete.
-/
def equivFnOfDiscrete : C(α, β) ≃ (α → β) :=
  ⟨fun f => f,
    fun f => ⟨f, continuous_of_discreteTopology⟩,
    fun _ => by ext; rfl,
    fun _ => by ext; rfl⟩
/-
**ContinuousMap.coe_equivFnOfDiscrete** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] [inst_2 : DiscreteTopology α],   ⇑ContinuousMap.equivFnOfDiscret
e = DFunLike.coe
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_equivFnOfDiscrete : ⇑equivFnOfDiscrete = (DFunLike.coe : C(α, β) → α → β) := rfl
/-
**ContinuousMap.equivFnOfDiscrete_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMap`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] [inst_2 : DiscreteTopology α]   (f : α → β), ⇑(ContinuousMap.equ
ivFnOfDiscrete.symm f) = f
参数：f : α → β；ContinuousMap.equivFnOfDiscrete.symm f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma equivFnOfDiscrete_symm_apply (f : α → β) : equivFnOfDiscrete.symm f = f := rfl

end DiscreteTopology

variable (α)

/-- The identity as a continuous map. -/
/-
**ContinuousMap.id** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：(α : Type u_1) → [inst : TopologicalSpace α] → C(α, α)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity as a continuous map.
-/
protected def id : C(α, α) where
  toFun := id

@[simp, norm_cast]
/-
**ContinuousMap.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_id : ⇑(ContinuousMap.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(ContinuousMap.id α) = id :=
  rfl

/-- The constant map as a continuous map. -/
/-
**ContinuousMap.const** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：const (b : β) : C(α, β) where toFun
参数：b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant map as a continuous map.
-/
def const (b : β) : C(α, β) where
  toFun := fun _ : α => b

@[simp]
/-
**ContinuousMap.coe_const** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_const (b : β) : ⇑(const α b) = Function.const α b
参数：b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl

/-- `Function.const α b` as a bundled continuous function of `b`. -/
@[simps -fullyApplied]
/-
**ContinuousMap.constPi** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：constPi : C(β, α -> β) where toFun b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Function.const α b` as a bundled continuous function of `b`.
-/
def constPi : C(β, α → β) where
  toFun b := Function.const α b
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited β] : Inhabited C(α, β) :=
  ⟨const α default⟩

variable {α}

@[simp]
/-
**ContinuousMap.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：id_apply (a : α) : ContinuousMap.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : ContinuousMap.id α a = a :=
  rfl

@[simp]
/-
**ContinuousMap.const_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：const_apply (b : β) (a : α) : const α b a = b
参数：b : β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl

/-- The composition of continuous maps, as a continuous map. -/
@[implicit_reducible]
/-
**ContinuousMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) where toFun
参数：f : C(β, γ)；g : C(α, β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of continuous maps, as a continuous map.
-/
def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) where
  toFun := f ∘ g

@[simp]
/-
**ContinuousMap.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_comp (f : C(β, γ)) (g : C(α, β)) : ⇑(comp f g) = f ∘ g
参数：f : C(β, γ)；g : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : C(β, γ)) (g : C(α, β)) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
/-
**ContinuousMap.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：comp_apply (f : C(β, γ)) (g : C(α, β)) (a : α) : comp f g a = f (g a)
参数：f : C(β, γ)；g : C(α, β)；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : C(β, γ)) (g : C(α, β)) (a : α) : comp f g a = f (g a) :=
  rfl

@[simp]
/-
**ContinuousMap.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：comp_assoc (f : C(γ, δ)) (g : C(β, γ)) (h : C(α, β)) : (f.comp g).comp h =
 f.comp (g.comp h)
参数：f : C(γ, δ)；g : C(β, γ)；h : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : C(γ, δ)) (g : C(β, γ)) (h : C(α, β)) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**ContinuousMap.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：id_comp (f : C(α, β)) : (ContinuousMap.id _).comp f = f
参数：f : C(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
-/
theorem id_comp (f : C(α, β)) : (ContinuousMap.id _).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**ContinuousMap.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：comp_id (f : C(α, β)) : f.comp (ContinuousMap.id _) = f
参数：f : C(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
-/
theorem comp_id (f : C(α, β)) : f.comp (ContinuousMap.id _) = f :=
  ext fun _ => rfl

@[simp]
/-
**ContinuousMap.const_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：const_comp (c : γ) (f : C(α, β)) : (const β c).comp f = const α c
参数：c : γ；f : C(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
-/
theorem const_comp (c : γ) (f : C(α, β)) : (const β c).comp f = const α c :=
  ext fun _ => rfl

@[simp]
/-
**ContinuousMap.comp_const** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：comp_const (f : C(β, γ)) (b : β) : f.comp (const α b) = const α (f b)
参数：f : C(β, γ)；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
-/
theorem comp_const (f : C(β, γ)) (b : β) : f.comp (const α b) = const α (f b) :=
  ext fun _ => rfl

@[simp]
/-
**ContinuousMap.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：cancel_right {f₁ f₂ : C(β, γ)} {g : C(α, β)} (hg : Surjective g) : f₁.comp
 g = f₂.comp g ↔ f₁ = f₂
参数：β, γ；α, β；hg : Surjective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_right {f₁ f₂ : C(β, γ)} {g : C(α, β)} (hg : Surjective g) :
    f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
  ⟨fun h => ext <| hg.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (ContinuousMap.comp · g)⟩

@[simp]
/-
**ContinuousMap.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：cancel_left {f : C(β, γ)} {g₁ g₂ : C(α, β)} (hf : Injective f) : f.comp g₁
 = f.comp g₂ ↔ g₁ = g₂
参数：β, γ；α, β；hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.comp_apply`：comp_apply (f : C(β, γ)) (g : C(α, β)) (a : α)
 : comp f g a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {f : C(β, γ)} {g₁ g₂ : C(α, β)} (hf : Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h => ext fun a => hf <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] [Nontrivial β] : Nontrivial C(α, β) :=
  ⟨let ⟨b₁, b₂, hb⟩ := exists_pair_ne β
  ⟨const _ b₁, const _ b₂, fun h => hb <| DFunLike.congr_fun h <| Classical.arbitrary α⟩⟩

/-- The bijection `C(X₁, Y₁) ≃ C(X₂, Y₂)` induced by homeomorphisms
`e : X₁ ≃ₜ X₂` and `e' : Y₁ ≃ₜ Y₂`. -/
@[simps]
/-
**ContinuousMap._root_.Homeomorph.continuousMapCongr** 是 Mathlib 中的一个定义，位于命名空间 `
ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `C(X₁, Y₁) ≃ C(X₂, Y₂)` induced by homeomorphisms
`e : X₁ ≃ₜ X₂` and `e' : Y₁ ≃ₜ Y₂`.
-/
def _root_.Homeomorph.continuousMapCongr {X₁ X₂ Y₁ Y₂ : Type*}
    [TopologicalSpace X₁] [TopologicalSpace X₂]
    [TopologicalSpace Y₁] [TopologicalSpace Y₂]
    (e : X₁ ≃ₜ X₂) (e' : Y₁ ≃ₜ Y₂) :
    C(X₁, Y₁) ≃ C(X₂, Y₂) where
  toFun f := ContinuousMap.comp ⟨_, e'.continuous⟩ (f.comp ⟨_, e.symm.continuous⟩)
  invFun g := ContinuousMap.comp ⟨_, e'.symm.continuous⟩ (g.comp ⟨_, e.continuous⟩)
  left_inv _ := by aesop
  right_inv _ := by aesop

section Prod

variable {α₁ α₂ β₁ β₂ : Type*} [TopologicalSpace α₁] [TopologicalSpace α₂] [TopologicalSpace β₁]
  [TopologicalSpace β₂]

/-- `Prod.fst : (x, y) ↦ x` as a bundled continuous map. -/
@[simps -fullyApplied]
/-
**ContinuousMap.fst** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：fst : C(α × β, α) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.fst : (x, y) ↦ x` as a bundled continuous map.
-/
def fst : C(α × β, α) where
  toFun := Prod.fst

/-- `Prod.snd : (x, y) ↦ y` as a bundled continuous map. -/
@[simps -fullyApplied]
/-
**ContinuousMap.snd** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：snd : C(α × β, β) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.snd : (x, y) ↦ y` as a bundled continuous map.
-/
def snd : C(α × β, β) where
  toFun := Prod.snd

/-- Given two continuous maps `f` and `g`, this is the continuous map `x ↦ (f x, g x)`. -/
/-
**ContinuousMap.prodMk** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：prodMk (f : C(α, β₁)) (g : C(α, β₂)) : C(α, β₁ × β₂) where toFun x
参数：f : C(α, β₁)；g : C(α, β₂)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two continuous maps `f` and `g`, this is the continuous map `x ↦ (f x, g x
)`.
-/
def prodMk (f : C(α, β₁)) (g : C(α, β₂)) : C(α, β₁ × β₂) where
  toFun x := (f x, g x)

/-- Given two continuous maps `f` and `g`, this is the continuous map `(x, y) ↦ (f x, g y)`. -/
@[simps]
/-
**ContinuousMap.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：prodMap (f : C(α₁, α₂)) (g : C(β₁, β₂)) : C(α₁ × β₁, α₂ × β₂) where toFun
参数：f : C(α₁, α₂)；g : C(β₁, β₂)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two continuous maps `f` and `g`, this is the continuous map `(x, y) ↦ (f x
, g y)`.
-/
def prodMap (f : C(α₁, α₂)) (g : C(β₁, β₂)) : C(α₁ × β₁, α₂ × β₂) where
  toFun := Prod.map f g

@[simp]
/-
**ContinuousMap.prod_eval** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：prod_eval (f : C(α, β₁)) (g : C(α, β₂)) (a : α) : (prodMk f g) a = (f a, g
 a)
参数：f : C(α, β₁)；g : C(α, β₂)；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_eval (f : C(α, β₁)) (g : C(α, β₂)) (a : α) : (prodMk f g) a = (f a, g a) :=
  rfl

/-- `Prod.swap` bundled as a `ContinuousMap`. -/
@[simps!]
/-
**ContinuousMap.prodSwap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：prodSwap : C(α × β, β × α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.swap` bundled as a `ContinuousMap`.
-/
def prodSwap : C(α × β, β × α) := .prodMk .snd .fst

end Prod

section Sigma

variable {I A : Type*} {X : I → Type*} [TopologicalSpace A] [∀ i, TopologicalSpace (X i)]

/-- `Sigma.mk i` as a bundled continuous map. -/
@[simps apply]
/-
**ContinuousMap.sigmaMk** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：sigmaMk (i : I) : C(X i, Σ i, X i) where toFun
参数：i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sigma.mk i` as a bundled continuous map.
-/
def sigmaMk (i : I) : C(X i, Σ i, X i) where
  toFun := Sigma.mk i

/--
To give a continuous map out of a disjoint union, it suffices to give a continuous map out of
each term. This is `Sigma.uncurry` for continuous maps.
-/
@[simps]
/-
**ContinuousMap.sigma** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：sigma (f : forall i, C(X i, A)) : C((Σ i, X i), A) where toFun ig
参数：f : forall i, C(X i, A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To give a continuous map out of a disjoint union, it suffices to give a continuo
us map out of
each term. This is `Sigma.uncurry` for continuous maps.
-/
def sigma (f : ∀ i, C(X i, A)) : C((Σ i, X i), A) where
  toFun ig := f ig.fst ig.snd
  continuous_toFun := by continuity

variable (A X) in
/--
Giving a continuous map out of a disjoint union is the same as giving a continuous map out of
each term. This is a version of `Equiv.piCurry` for continuous maps.
-/
@[simps]
/-
**ContinuousMap.sigmaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：sigmaEquiv : (forall i, C(X i, A)) ≃ C((Σ i, X i), A) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Giving a continuous map out of a disjoint union is the same as giving a continuo
us map out of
each term. This is a version of `Equiv.piCurry` for continuous maps.
-/
def sigmaEquiv : (∀ i, C(X i, A)) ≃ C((Σ i, X i), A) where
  toFun := sigma
  invFun f i := f.comp (sigmaMk i)

end Sigma

section Pi

variable {I A : Type*} {X Y : I → Type*} [TopologicalSpace A] [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (Y i)]

/-- Abbreviation for product of continuous maps, which is continuous -/
/-
**ContinuousMap.pi** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：pi (f : forall i, C(A, X i)) : C(A, forall i, X i) where toFun (a : A) (i 
: I)
参数：f : forall i, C(A, X i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abbreviation for product of continuous maps, which is continuous
-/
def pi (f : ∀ i, C(A, X i)) : C(A, ∀ i, X i) where
  toFun (a : A) (i : I) := f i a

@[simp]
/-
**ContinuousMap.pi_eval** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：pi_eval (f : forall i, C(A, X i)) (a : A) : (pi f) a = fun i : I => (f i) 
a
参数：f : forall i, C(A, X i)；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_eval (f : ∀ i, C(A, X i)) (a : A) : (pi f) a = fun i : I => (f i) a :=
  rfl

/-- Evaluation at point as a bundled continuous map. -/
@[simps -fullyApplied]
/-
**ContinuousMap.eval** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：eval (i : I) : C(forall j, X j, X i) where toFun
参数：i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation at point as a bundled continuous map.
-/
def eval (i : I) : C(∀ j, X j, X i) where
  toFun := Function.eval i

variable (A X) in
/--
Giving a continuous map out of a disjoint union is the same as giving a continuous map out of
each term
-/
@[simps]
/-
**ContinuousMap.piEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：piEquiv : (forall i, C(A, X i)) ≃ C(A, forall i, X i) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Giving a continuous map out of a disjoint union is the same as giving a continuo
us map out of
each term
-/
def piEquiv : (∀ i, C(A, X i)) ≃ C(A, ∀ i, X i) where
  toFun := pi
  invFun f i := (eval i).comp f

/-- Combine a collection of bundled continuous maps `C(X i, Y i)` into a bundled continuous map
`C(∀ i, X i, ∀ i, Y i)`. -/
@[simps!]
/-
**ContinuousMap.piMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：piMap (f : forall i, C(X i, Y i)) : C((i : I) -> X i, (i : I) -> Y i)
参数：f : forall i, C(X i, Y i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine a collection of bundled continuous maps `C(X i, Y i)` into a bundled con
tinuous map
`C(∀ i, X i, ∀ i, Y i)`.
-/
def piMap (f : ∀ i, C(X i, Y i)) : C((i : I) → X i, (i : I) → Y i) :=
  .pi fun i ↦ (f i).comp (eval i)

/-- "Precomposition" as a continuous map between dependent types. -/
/-
**ContinuousMap.precomp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：precomp {ι : Type*} (φ : ι -> I) : C((i : I) -> X i, (i : ι) -> X (φ i))
参数：φ : ι -> I。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.continuous_precomp'`：Pi.continuous_precomp' {ι' : Type*} (φ : ι' -> ι
) : Continuous (fun (f : (forall i, A i)) (j : ι') => f (φ j))

--- 原说明 ---
"Precomposition" as a continuous map between dependent types.
-/
def precomp {ι : Type*} (φ : ι → I) : C((i : I) → X i, (i : ι) → X (φ i)) :=
  ⟨_, Pi.continuous_precomp' φ⟩

end Pi

section Restrict

variable (s : Set α)

/-- The restriction of a continuous function `α → β` to a subset `s` of `α`. -/
/-
**ContinuousMap.restrict** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：restrict (f : C(α, β)) : C(s, β) where toFun
参数：f : C(α, β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a continuous function `α → β` to a subset `s` of `α`.
-/
def restrict (f : C(α, β)) : C(s, β) where
  toFun := f ∘ ((↑) : s → α)

@[simp]
/-
**ContinuousMap.coe_restrict** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_restrict (f : C(α, β)) : ⇑(f.restrict s) = s.domRestrict f
参数：f : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrict (f : C(α, β)) : ⇑(f.restrict s) = s.domRestrict f :=
  rfl

@[simp]
/-
**ContinuousMap.restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：restrict_apply (f : C(α, β)) (s : Set α) (x : s) : f.restrict s x = f x
参数：f : C(α, β)；s : Set α；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_apply (f : C(α, β)) (s : Set α) (x : s) : f.restrict s x = f x :=
  rfl

@[simp]
/-
**ContinuousMap.restrict_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：restrict_apply_mk (f : C(α, β)) (s : Set α) (x : α) (hx : x in s) : f.rest
rict s ⟨x, hx⟩ = f x
参数：f : C(α, β)；s : Set α；x : α；hx : x in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_apply_mk (f : C(α, β)) (s : Set α) (x : α) (hx : x ∈ s) :
    f.restrict s ⟨x, hx⟩ = f x :=
  rfl
/-
**ContinuousMap.injective_restrict** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：injective_restrict [T2Space β] {s : Set α} (hs : Dense s) : Injective (res
trict s : C(α, β) -> C(s, β))
参数：hs : Dense s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
· 使用定理 `Continuous.ext_on`：Continuous.ext_on [T2Space X] {s : Set Y} (hs : Dense
 s) {f g : Y -> X} (hf : Continuous f) (hg : Continuous g) (h : EqOn f g s) : f 
= g
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.domRestrict_eq_domRestrict_iff`：domRestrict_eq_domRestrict_iff : dom
Restrict s f₁ = domRestrict s f₂ ↔ EqOn f₁ f₂ s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem injective_restrict [T2Space β] {s : Set α} (hs : Dense s) :
    Injective (restrict s : C(α, β) → C(s, β)) := fun f g h ↦
  DFunLike.ext' <| (map_continuous f).ext_on hs (map_continuous g) <|
    Set.domRestrict_eq_domRestrict_iff.1 <| congr_arg DFunLike.coe h

/-- The restriction of a continuous map to the preimage of a set. -/
@[simps]
/-
**ContinuousMap.restrictPreimage** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：restrictPreimage (f : C(α, β)) (s : Set β) : C(f ⁻¹' s, s)
参数：f : C(α, β)；s : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a continuous map to the preimage of a set.
-/
def restrictPreimage (f : C(α, β)) (s : Set β) : C(f ⁻¹' s, s) :=
  ⟨s.restrictPreimage f, continuous_iff_continuousAt.mpr fun _ ↦
    (map_continuousAt f _).restrictPreimage⟩

end Restrict

section mkD

/--
Interpret `f : α → β` as an element of `C(α, β)`, falling back to the default value
`default : C(α, β)` if `f` is not continuous.
This is mainly intended to be used for `C(α, β)`-valued integration. For example, if a family of
functions `f : ι → α → β` satisfies that `f i` is continuous for almost every `i`, you can write
the `C(α, β)`-valued integral "`∫ i, f i`" as `∫ i, ContinuousMap.mkD (f i) 0`.
-/
/-
**ContinuousMap.mkD** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：mkD (f : α -> β) (default : C(α, β)) : C(α, β)
参数：f : α -> β；default : C(α, β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret `f : α → β` as an element of `C(α, β)`, falling back to the default va
lue
`default : C(α, β)` if `f` is not continuous.
This is mainly intended to be used for `C(α, β)`-valued integration. For example
, if a family of
functions `f : ι → α → β` satisfies that `f i` is continuous for almost every `i
`, you can write
the `C(α, β)`-valued integral "`∫ i, f i`" as `∫ i, ContinuousMap.mkD (f i) 0`.
-/
noncomputable def mkD (f : α → β) (default : C(α, β)) : C(α, β) :=
  open scoped Classical in
  if h : Continuous f then ⟨_, h⟩ else default
/-
**ContinuousMap.mkD_of_continuous** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：mkD_of_continuous {f : α -> β} {g : C(α, β)} (hf : Continuous f) : mkD f g
 = ⟨f, hf⟩
参数：α, β；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mkD_of_continuous {f : α → β} {g : C(α, β)} (hf : Continuous f) :
    mkD f g = ⟨f, hf⟩ := by
  simp only [mkD, hf, ↓reduceDIte]
/-
**ContinuousMap.mkD_of_not_continuous** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：mkD_of_not_continuous {f : α -> β} {g : C(α, β)} (hf : ¬ Continuous f) : m
kD f g = g
参数：α, β；hf : ¬ Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mkD_of_not_continuous {f : α → β} {g : C(α, β)} (hf : ¬ Continuous f) :
    mkD f g = g := by
  simp only [mkD, hf, ↓reduceDIte]
/-
**ContinuousMap.mkD_apply_of_continuous** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap
`。
形式化陈述：mkD_apply_of_continuous {f : α -> β} {g : C(α, β)} {x : α} (hf : Continuou
s f) : mkD f g x = f x
参数：α, β；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousMap.mkD_of_continuous`：mkD_of_continuous {f : α -> β} {g : C(α
, β)} (hf : Continuous f) : mkD f g = ⟨f, hf⟩
· 使用定理 `ContinuousMap.coe_mk`：coe_mk (f : X -> Y) (h : Continuous f) : ⇑(⟨f, h⟩ 
: C(X, Y)) = f
-/
lemma mkD_apply_of_continuous {f : α → β} {g : C(α, β)} {x : α} (hf : Continuous f) :
    mkD f g x = f x := by
  rw [mkD_of_continuous hf, coe_mk]
/-
**ContinuousMap.mkD_of_continuousOn** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：mkD_of_continuousOn {s : Set α} {f : α -> β} {g : C(s, β)} (hf : Continuou
sOn f s) : mkD (s.domRestrict f) g = ⟨s.domRestrict f, hf.domRestrict⟩
参数：s, β；hf : ContinuousOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMap.mkD_of_continuous`：mkD_of_continuous {f : α -> β} {g : C(α
, β)} (hf : Continuous f) : mkD f g = ⟨f, hf⟩
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
-/
lemma mkD_of_continuousOn {s : Set α} {f : α → β} {g : C(s, β)}
    (hf : ContinuousOn f s) :
    mkD (s.domRestrict f) g = ⟨s.domRestrict f, hf.domRestrict⟩ := mkD_of_continuous hf.domRestrict
/-
**ContinuousMap.mkD_of_not_continuousOn** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap
`。
形式化陈述：mkD_of_not_continuousOn {s : Set α} {f : α -> β} {g : C(s, β)} (hf : ¬ Con
tinuousOn f s) : mkD (s.domRestrict f) g = g
参数：s, β；hf : ¬ ContinuousOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMap.mkD_of_not_continuous`：mkD_of_not_continuous {f : α -> β} 
{g : C(α, β)} (hf : ¬ Continuous f) : mkD f g = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
-/
lemma mkD_of_not_continuousOn {s : Set α} {f : α → β} {g : C(s, β)}
    (hf : ¬ ContinuousOn f s) :
    mkD (s.domRestrict f) g = g := by
  rw [continuousOn_iff_continuous_domRestrict] at hf
  exact mkD_of_not_continuous hf
/-
**ContinuousMap.mkD_apply_of_continuousOn** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousM
ap`。
形式化陈述：mkD_apply_of_continuousOn {s : Set α} {f : α -> β} {g : C(s, β)} {x : s} (
hf : ContinuousOn f s) : mkD (s.domRestrict f) g x = f x
参数：s, β；hf : ContinuousOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousMap.mkD_of_continuousOn`：mkD_of_continuousOn {s : Set α} {f : 
α -> β} {g : C(s, β)} (hf : ContinuousOn f s) : mkD (s.domRestrict f) g = ⟨s.dom
Restrict f, hf.domRestr…
· 使用定理 `ContinuousMap.coe_mk`：coe_mk (f : X -> Y) (h : Continuous f) : ⇑(⟨f, h⟩ 
: C(X, Y)) = f
· 使用定理 `Set.domRestrict_apply`：domRestrict_apply (f : (a : α) -> π a) (s : Set α
) (x : s) : s.domRestrict f x = f x
-/
lemma mkD_apply_of_continuousOn {s : Set α} {f : α → β} {g : C(s, β)} {x : s}
    (hf : ContinuousOn f s) :
    mkD (s.domRestrict f) g x = f x := by rw [mkD_of_continuousOn hf, coe_mk, Set.domRestrict_apply]
/-
**ContinuousMap.mkD_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：mkD_eq_self {f g : C(α, β)} : mkD f g = f
参数：α, β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMap.mkD_of_continuous`：mkD_of_continuous {f : α -> β} {g : C(α
, β)} (hf : Continuous f) : mkD f g = ⟨f, hf⟩
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
-/
lemma mkD_eq_self {f g : C(α, β)} : mkD f g = f :=
  mkD_of_continuous f.continuous

end mkD

section Gluing

variable {ι : Type*} (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))
  (hφ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
  (hS : ∀ x : α, ∃ i, S i ∈ 𝓝 x)

/-- A family `φ i` of continuous maps `C(S i, β)`, where the domains `S i` contain a neighbourhood
of each point in `α` and the functions `φ i` agree pairwise on intersections, can be glued to
construct a continuous map in `C(α, β)`. -/
/-
**ContinuousMap.liftCover** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：liftCover : C(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family `φ i` of continuous maps `C(S i, β)`, where the domains `S i` contain a
 neighbourhood
of each point in `α` and the functions `φ i` agree pairwise on intersections, ca
n be glued to
construct a continuous map in `C(α, β)`.
-/
noncomputable def liftCover : C(α, β) :=
  haveI H : ⋃ i, S i = Set.univ :=
    Set.iUnion_eq_univ_iff.2 fun x ↦ (hS x).imp fun _ ↦ mem_of_mem_nhds
  mk (Set.liftCover S (fun i ↦ φ i) hφ H) <| continuous_of_cover_nhds hS fun i ↦ by
    rw [continuousOn_iff_continuous_domRestrict]
    simpa +unfoldPartialApp only [Set.domRestrict, Set.liftCover_coe]
      using map_continuous (φ i)

variable {S φ hφ hS}

@[simp]
/-
**ContinuousMap.liftCover_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：liftCover_coe {i : ι} (x : S i) : liftCover S φ hφ hS x = φ i x
参数：x : S i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.liftCover.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : To
pologicalSpace α] [inst_1 : TopologicalSpace β] {ι : Type u_5} (S : ι → Set α)  
 (φ : (i : ι) → C(…
· 使用定理 `ContinuousMap.coe_mk`：coe_mk (f : X -> Y) (h : Continuous f) : ⇑(⟨f, h⟩ 
: C(X, Y)) = f
· 使用定理 `Set.liftCover_coe`：liftCover_coe {i : ι} (x : S i) : liftCover S f hf hS
 x = f i x
-/
theorem liftCover_coe {i : ι} (x : S i) : liftCover S φ hφ hS x = φ i x := by
  rw [liftCover, coe_mk, Set.liftCover_coe _]

@[simp]
/-
**ContinuousMap.liftCover_restrict** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：liftCover_restrict {i : ι} : (liftCover S φ hφ hS).restrict (S i) = φ i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.liftCover_coe`：liftCover_coe {i : ι} (x : S i) : liftCover
 S φ hφ hS x = φ i x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftCover_restrict {i : ι} : (liftCover S φ hφ hS).restrict (S i) = φ i := by
  ext
  simp only [restrict_apply, liftCover_coe]

variable (A : Set (Set α)) (F : ∀ s ∈ A, C(s, β))
  (hF : ∀ (s) (hs : s ∈ A) (t) (ht : t ∈ A) (x : α) (hxi : x ∈ s) (hxj : x ∈ t),
    F s hs ⟨x, hxi⟩ = F t ht ⟨x, hxj⟩)
  (hA : ∀ x : α, ∃ i ∈ A, i ∈ 𝓝 x)

/-- A family `F s` of continuous maps `C(s, β)`, where (1) the domains `s` are taken from a set `A`
of sets in `α` which contain a neighbourhood of each point in `α` and (2) the functions `F s` agree
pairwise on intersections, can be glued to construct a continuous map in `C(α, β)`. -/
/-
**ContinuousMap.liftCover'** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：liftCover' : C(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family `F s` of continuous maps `C(s, β)`, where (1) the domains `s` are taken
 from a set `A`
of sets in `α` which contain a neighbourhood of each point in `α` and (2) the fu
nctions `F s` agree
pairwise on intersections, can be glued to construct a continuous map in `C(α, β
)`.
-/
noncomputable def liftCover' : C(α, β) :=
  let F : ∀ i : A, C(i, β) := fun i => F i i.prop
  liftCover ((↑) : A → Set α) F (fun i j => hF i i.prop j j.prop)
    fun x => let ⟨s, hs, hsx⟩ := hA x; ⟨⟨s, hs⟩, hsx⟩

variable {A F hF hA}

-- Porting note: did not need `by delta liftCover'; exact` in mathlib3; goal was
-- closed by `liftCover_coe x'`
-- Might be something to do with the `let`s in the definition of `liftCover'`?
@[simp]
/-
**ContinuousMap.liftCover_coe'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：liftCover_coe' {s : Set α} {hs : s in A} (x : s) : liftCover' A F hF hA x 
= F s hs x
参数：x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.liftCover_coe`：liftCover_coe {i : ι} (x : S i) : liftCover
 S φ hφ hS x = φ i x
-/
theorem liftCover_coe' {s : Set α} {hs : s ∈ A} (x : s) : liftCover' A F hF hA x = F s hs x :=
  let x' : ((↑) : A → Set α) ⟨s, hs⟩ := x
  by delta liftCover'; exact ContinuousMap.liftCover_coe x'

@[simp]
/-
**ContinuousMap.liftCover_restrict'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：liftCover_restrict' {s : Set α} {hs : s in A} : (liftCover' A F hF hA).res
trict s = F s hs
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `ContinuousMap.liftCover_coe'`：liftCover_coe' {s : Set α} {hs : s in A} (
x : s) : liftCover' A F hF hA x = F s hs x
-/
theorem liftCover_restrict' {s : Set α} {hs : s ∈ A} :
    (liftCover' A F hF hA).restrict s = F s hs := ext <| liftCover_coe' (hF := hF) (hA := hA)

end Gluing

/-- `Set.inclusion` as a bundled continuous map. -/
/-
**ContinuousMap.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：inclusion {s t : Set α} (h : s subseteq t) : C(s, t) where toFun
参数：h : s subseteq t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_inclusion`：continuous_inclusion {s t : Set X} (h : s subseteq
 t) : Continuous (inclusion h)

--- 原说明 ---
`Set.inclusion` as a bundled continuous map.
-/
def inclusion {s t : Set α} (h : s ⊆ t) : C(s, t) where
  toFun := Set.inclusion h
  continuous_toFun := continuous_inclusion h

end ContinuousMap

section Lift

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : C(X, Y)}

/-- `Setoid.quotientKerEquivOfRightInverse` as a homeomorphism. -/
@[simps!]
/-
**Function.RightInverse.homeomorph** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.RightInverse.homeomorph {f' : C(Y, X)} (hf : Function.RightInvers
e f' f) : Quotient (Setoid.ker f) ≃ₜ Y where toEquiv
参数：Y, X；hf : Function.RightInverse f' f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Setoid.quotientKerEquivOfRightInverse` as a homeomorphism.
-/
def Function.RightInverse.homeomorph {f' : C(Y, X)} (hf : Function.RightInverse f' f) :
    Quotient (Setoid.ker f) ≃ₜ Y where
  toEquiv := Setoid.quotientKerEquivOfRightInverse _ _ hf
  continuous_toFun := isQuotientMap_quot_mk.continuous_iff.mpr (map_continuous f)
  continuous_invFun := continuous_quotient_mk'.comp (map_continuous f')

namespace Topology.IsQuotientMap

/--
The homeomorphism from the quotient of a quotient map to its codomain. This is
`Setoid.quotientKerEquivOfSurjective` as a homeomorphism.
-/
@[simps!]
/-
**Topology.IsQuotientMap.homeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Topology.IsQuotie
ntMap`。
形式化陈述：homeomorph (hf : IsQuotientMap f) : Quotient (Setoid.ker f) ≃ₜ Y where toE
quiv
参数：hf : IsQuotientMap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homeomorphism from the quotient of a quotient map to its codomain. This is
`Setoid.quotientKerEquivOfSurjective` as a homeomorphism.
-/
noncomputable def homeomorph (hf : IsQuotientMap f) : Quotient (Setoid.ker f) ≃ₜ Y where
  toEquiv := Setoid.quotientKerEquivOfSurjective _ hf.surjective
  continuous_toFun := isQuotientMap_quot_mk.continuous_iff.mpr hf.continuous
  continuous_invFun := by
    rw [hf.continuous_iff]
    convert! continuous_quotient_mk'
    ext
    simp only [Equiv.invFun_as_coe, Function.comp_apply,
      (Setoid.quotientKerEquivOfSurjective f hf.surjective).symm_apply_eq]
    rfl

variable (hf : IsQuotientMap f) (g : C(X, Z)) (h : Function.FactorsThrough g f)

/-- Descend a continuous map, which is constant on the fibres, along a quotient map. -/
@[simps]
/-
**Topology.IsQuotientMap.lift** 是 Mathlib 中的一个定义，位于命名空间 `Topology.IsQuotientMap`
。
形式化陈述：lift : C(Y, Z) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Descend a continuous map, which is constant on the fibres, along a quotient map.
-/
noncomputable def lift : C(Y, Z) where
  toFun := ((fun i ↦ Quotient.liftOn' i g (fun _ _ (hab : f _ = f _) ↦ h hab)) :
    Quotient (Setoid.ker f) → Z) ∘ hf.homeomorph.symm
  continuous_toFun := Continuous.comp (continuous_quot_lift _ g.2) (Homeomorph.continuous _)

/--
The obvious triangle induced by `IsQuotientMap.lift` commutes:
```
     g
  X --→ Z
  |   ↗
f |  / hf.lift g h
  v /
  Y
```
-/
@[simp]
/-
**Topology.IsQuotientMap.lift_comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsQuotien
tMap`。
形式化陈述：lift_comp : (hf.lift g h).comp f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Topology.IsQuotientMap.lift_apply`：∀ {X : Type u_1} {Y : Type u_2} {Z : 
Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : 
TopologicalSpace Z] {f …
· 使用定理 `Quotient.liftOn'.congr_simp`：∀ {α : Sort u_1} {φ : Sort u_4} {s₁ : Setoi
d α} (q q_1 : Quotient s₁),   q = q_1 → ∀ (f f_1 : α → φ) (e_f : f = f_1) (h : ∀
 (a b : α), s₁ a …
· 使用定理 `Topology.IsQuotientMap.homeomorph_symm_apply`：∀ {X : Type u_1} {Y : Type
 u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : C(X, Y)}   
(hf : Topology.IsQuotientMap ⇑f) (…
· 使用定理 `Function.rightInverse_surjInv`：rightInverse_surjInv (hf : Surjective f) 
: RightInverse (surjInv hf) f

--- 原说明 ---
The obvious triangle induced by `IsQuotientMap.lift` commutes:
```
     g
  X --→ Z
  |   ↗
f |  / hf.lift g h
  v /
  Y
```
-/
theorem lift_comp : (hf.lift g h).comp f = g := by
  ext
  simpa using h (Function.rightInverse_surjInv _ _)

/-- `IsQuotientMap.lift` as an equivalence. -/
@[simps]
/-
**Topology.IsQuotientMap.liftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Topology.IsQuotien
tMap`。
形式化陈述：liftEquiv : { g : C(X, Z) // Function.FactorsThrough g f} ≃ C(Y, Z) where 
toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsQuotientMap.lift` as an equivalence.
-/
noncomputable def liftEquiv : { g : C(X, Z) // Function.FactorsThrough g f} ≃ C(Y, Z) where
  toFun g := hf.lift g g.prop
  invFun g := ⟨g.comp f, fun _ _ h ↦ by simp only [ContinuousMap.comp_apply]; rw [h]⟩
  left_inv := by intro; simp
  right_inv := by
    intro g
    ext a
    simpa using congrArg g (Function.rightInverse_surjInv hf.surjective a)

end Topology.IsQuotientMap
end Lift

namespace Homeomorph

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
variable (f : α ≃ₜ β) (g : β ≃ₜ γ)

/-
**Homeomorph.instContinuousMapClass** 是 Mathlib 中的一个实例，位于命名空间 `Homeomorph`。
形式化陈述：instContinuousMapClass : ContinuousMapClass (α ≃ₜ β) α β where map_continu
ous f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.continuous_toFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous sel
f.toFun
-/
instance instContinuousMapClass : ContinuousMapClass (α ≃ₜ β) α β where
  map_continuous f := f.continuous_toFun

@[simp]
/-
**Homeomorph.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：coe_refl : (Homeomorph.refl α : C(α, α)) = ContinuousMap.id α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl : (Homeomorph.refl α : C(α, α)) = ContinuousMap.id α :=
  rfl

@[simp]
/-
**Homeomorph.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：coe_trans : (f.trans g : C(α, γ)) = (g : C(β, γ)).comp f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans : (f.trans g : C(α, γ)) = (g : C(β, γ)).comp f :=
  rfl

/-- Left inverse to a continuous map from a homeomorphism, mirroring `Equiv.symm_comp_self`. -/
@[simp]
/-
**Homeomorph.symm_comp_toContinuousMap** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：symm_comp_toContinuousMap : (f.symm : C(β, α)).comp (f : C(α, β)) = Contin
uousMap.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.coe_trans`：coe_trans : (f.trans g : C(α, γ)) = (g : C(β, γ)).
comp f
· 使用定理 `Homeomorph.self_trans_symm`：self_trans_symm (h : X ≃ₜ Y) : h.trans h.sym
m = Homeomorph.refl X
· 使用定理 `Homeomorph.coe_refl`：coe_refl : (Homeomorph.refl α : C(α, α)) = Continuo
usMap.id α

--- 原说明 ---
Left inverse to a continuous map from a homeomorphism, mirroring `Equiv.symm_com
p_self`.
-/
theorem symm_comp_toContinuousMap :
    (f.symm : C(β, α)).comp (f : C(α, β)) = ContinuousMap.id α := by
  rw [← coe_trans, self_trans_symm, coe_refl]

/-- Right inverse to a continuous map from a homeomorphism, mirroring `Equiv.self_comp_symm`. -/
@[simp]
/-
**Homeomorph.toContinuousMap_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：toContinuousMap_comp_symm : (f : C(α, β)).comp (f.symm : C(β, α)) = Contin
uousMap.id β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.coe_trans`：coe_trans : (f.trans g : C(α, γ)) = (g : C(β, γ)).
comp f
· 使用定理 `Homeomorph.symm_trans_self`：symm_trans_self (h : X ≃ₜ Y) : h.symm.trans 
h = Homeomorph.refl Y
· 使用定理 `Homeomorph.coe_refl`：coe_refl : (Homeomorph.refl α : C(α, α)) = Continuo
usMap.id α

--- 原说明 ---
Right inverse to a continuous map from a homeomorphism, mirroring `Equiv.self_co
mp_symm`.
-/
theorem toContinuousMap_comp_symm :
    (f : C(α, β)).comp (f.symm : C(β, α)) = ContinuousMap.id β := by
  rw [← coe_trans, symm_trans_self, coe_refl]

end Homeomorph

