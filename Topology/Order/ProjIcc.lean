/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Topology.Order.Basic

/-!
# Projection onto a closed interval

In this file we prove that the projection `Set.projIcc f a b h` is a quotient map, and use it
to show that `Set.IccExtend h f` is continuous if and only if `f` is continuous.
-/

public section


open Set Filter Topology

variable {α β γ : Type*} [LinearOrder α] {a b c : α} {h : a ≤ b}

/-
**Filter.Tendsto.IccExtend** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : LinearOrder α] {a b
 : α} {h : a ≤ b} (f : γ → ↑(Set.Icc a b) → β)   {la : Filter α} {lb : Filter β}
 {lc : Filter γ},   Filter.Tendsto (↿f) (lc ×ˢ Filter.map (Set.projIcc a b h) la
) lb →     Filter.Tendsto (↿(Set.IccExtend h ∘ f)) (lc ×ˢ la) lb
参数：f : γ → ↑(Set.Icc a b) → β；↿f；lc ×ˢ Filter.map (Set.projIcc a b h) la；↿(Set.I
ccExtend h ∘ f)；lc ×ˢ la。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)
-/
protected theorem Filter.Tendsto.IccExtend (f : γ → Icc a b → β) {la : Filter α} {lb : Filter β}
    {lc : Filter γ} (hf : Tendsto ↿f (lc ×ˢ la.map (projIcc a b h)) lb) :
    Tendsto (↿(IccExtend h ∘ f)) (lc ×ˢ la) lb :=
  hf.comp <| tendsto_id.prodMap tendsto_map

variable [TopologicalSpace α] [OrderTopology α] [TopologicalSpace β] [TopologicalSpace γ]

@[continuity, fun_prop]
/-
**continuous_projIcc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_projIcc : Continuous (projIcc a b h)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.max`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : LinearOrder α] [OrderClosedTopology α] {f g : β → α}   [inst_3 : Topol
ogic…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Continuous.min`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : LinearOrder α] [OrderClosedTopology α] {f g : β → α}   [inst_3 : Topol
ogic…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
-/
theorem continuous_projIcc : Continuous (projIcc a b h) := Continuous.subtype_mk (by fun_prop) _
/-
**isQuotientMap_projIcc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isQuotientMap_projIcc : IsQuotientMap (projIcc a b h) where surjective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen`：∀ {X : Type u_1} {Y
 : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace 
Y],   (∀ (s : Set Y), IsOpen (f ⁻¹' s) ↔ …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.projIcc_val`：projIcc_val (x : Icc a b) : projIcc a b h x = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_projIcc`：continuous_projIcc : Continuous (projIcc a b h)
· 使用定理 `Set.projIcc_surjective`：projIcc_surjective : Surjective (projIcc a b h)
-/
theorem isQuotientMap_projIcc : IsQuotientMap (projIcc a b h) where
  surjective := projIcc_surjective h
  isCoinducing := .of_isOpen_preimage_iff_isOpen fun s ↦
    ⟨fun hs => ⟨_, hs, by ext; simp⟩, fun hs => hs.preimage continuous_projIcc⟩

@[simp]
/-
**continuous_IccExtend_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_IccExtend_iff {f : Icc a b -> β} : Continuous (IccExtend h f) ↔
 Continuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsQuotientMap.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {
Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : To
pologicalSpace Y] [inst_2 :…
· 使用定理 `isQuotientMap_projIcc`：isQuotientMap_projIcc : IsQuotientMap (projIcc a 
b h) where surjective
-/
theorem continuous_IccExtend_iff {f : Icc a b → β} : Continuous (IccExtend h f) ↔ Continuous f :=
  isQuotientMap_projIcc.continuous_iff.symm

/-- See Note [continuity lemma statement]. -/
@[fun_prop]
/-
**Continuous.IccExtend** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : LinearOrder α] {a b
 : α} {h : a ≤ b}   [inst_1 : TopologicalSpace α] [OrderTopology α] [inst_3 : To
pologicalSpace β] [inst_4 : TopologicalSpace γ]   {f : γ → ↑(Set.Icc a b) → β} {
g : γ → α},   Continuous ↿f → Continuous g → Continuous fun a_1 => Set.IccExtend
 h (f a_1) (g a_1)
参数：Set.Icc a b；f a_1；g a_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_projIcc`：continuous_projIcc : Continuous (projIcc a b h)

--- 原说明 ---
See Note [continuity lemma statement].
-/
protected theorem Continuous.IccExtend {f : γ → Icc a b → β} {g : γ → α} (hf : Continuous ↿f)
    (hg : Continuous g) : Continuous fun a => IccExtend h (f a) (g a) :=
  show Continuous (↿f ∘ fun x => (x, projIcc a b h (g x)))
  from hf.comp <| continuous_id.prodMk <| continuous_projIcc.comp hg

/-- A useful special case of `Continuous.IccExtend`. -/
@[continuity, fun_prop]
/-
**Continuous.Icc_extend'** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] {a b : α} {h : a ≤ 
b} [inst_1 : TopologicalSpace α]   [OrderTopology α] [inst_3 : TopologicalSpace 
β] {f : ↑(Set.Icc a b) → β},   Continuous f → Continuous (Set.IccExtend h f)
参数：Set.Icc a b；Set.IccExtend h f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_projIcc`：continuous_projIcc : Continuous (projIcc a b h)

--- 原说明 ---
A useful special case of `Continuous.IccExtend`.
-/
protected theorem Continuous.Icc_extend' {f : Icc a b → β} (hf : Continuous f) :
    Continuous (IccExtend h f) :=
  hf.comp continuous_projIcc

@[fun_prop]
/-
**ContinuousAt.IccExtend** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.IccExtend {x : γ} (f : γ -> Icc a b -> β) {g : γ -> α} (hf : 
ContinuousAt ↿f (x, projIcc a b h (g x))) (hg : ContinuousAt g x) : ContinuousAt
 (fun a => IccExtend h (f a) (g a)) x
参数：f : γ -> Icc a b -> β；hf : ContinuousAt ↿f (x, projIcc a b h (g x))；hg : Cont
inuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_projIcc`：continuous_projIcc : Continuous (projIcc a b h)
-/
theorem ContinuousAt.IccExtend {x : γ} (f : γ → Icc a b → β) {g : γ → α}
    (hf : ContinuousAt ↿f (x, projIcc a b h (g x))) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => IccExtend h (f a) (g a)) x :=
  show ContinuousAt (↿f ∘ fun x => (x, projIcc a b h (g x))) x from
    ContinuousAt.comp hf <| continuousAt_id.prodMk <| continuous_projIcc.continuousAt.comp hg
