/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.SetLike.Basic

/-!
# Order intervals

This file defines (nonempty) closed intervals in an order (see `Set.Icc`). This is a prototype for
interval arithmetic.

## Main declarations

* `NonemptyInterval`: Nonempty intervals. Pairs where the second element is greater than the first.
* `Interval`: Intervals. Either `∅` or a nonempty interval.
-/

@[expose] public section


open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*} {κ : ι → Sort*}

/-- The nonempty closed intervals in an order.

We define intervals by the pair of endpoints `fst`, `snd`. To convert intervals to the set of
elements between these endpoints, use the coercion `NonemptyInterval α → Set α`. -/
@[ext (flat := false)]
/-
**NonemptyInterval** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → [LE α] → Type u_6
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nonempty closed intervals in an order.

We define intervals by the pair of endpoints `fst`, `snd`. To convert intervals 
to the set of
elements between these endpoints, use the coercion `NonemptyInterval α → Set α`.
-/
structure NonemptyInterval (α : Type*) [LE α] extends Prod α α where
  /-- The starting point of an interval is smaller than the endpoint. -/
  fst_le_snd : fst ≤ snd

namespace NonemptyInterval

section LE

variable [LE α] {s t : NonemptyInterval α}

/-
**NonemptyInterval.toProd_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`
。
形式化陈述：toProd_injective : Injective (toProd : NonemptyInterval α -> α × α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toProd_injective : Injective (toProd : NonemptyInterval α → α × α) :=
  fun s t h => by cases s; cases t; congr

/-- Allow lifting a pair `(a, b)` with `a ≤ b` to `NonemptyInterval`
in the `lift` tactic. -/
/-
**NonemptyInterval.instCanLift** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
形式化陈述：instCanLift : CanLift (α × α) (NonemptyInterval α) NonemptyInterval.toProd
 (fun x => x.1 <= x.2) where prf x hx
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Allow lifting a pair `(a, b)` with `a ≤ b` to `NonemptyInterval`
in the `lift` tactic.
-/
instance instCanLift :
    CanLift (α × α) (NonemptyInterval α) NonemptyInterval.toProd (fun x ↦ x.1 ≤ x.2) where
  prf x hx := ⟨⟨x, hx⟩, rfl⟩

/-- The injection that induces the order on intervals. -/
/-
**NonemptyInterval.toDualProd** 是 Mathlib 中的一个定义，位于命名空间 `NonemptyInterval`。
形式化陈述：toDualProd : NonemptyInterval α -> αᵒᵈ × α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The injection that induces the order on intervals.
-/
def toDualProd : NonemptyInterval α → αᵒᵈ × α :=
  toProd

@[simp]
/-
**NonemptyInterval.toDualProd_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`
。
形式化陈述：toDualProd_apply (s : NonemptyInterval α) : s.toDualProd = (toDual s.fst, 
s.snd)
参数：s : NonemptyInterval α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDualProd_apply (s : NonemptyInterval α) : s.toDualProd = (toDual s.fst, s.snd) :=
  rfl
/-
**NonemptyInterval.toDualProd_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInter
val`。
形式化陈述：toDualProd_injective : Injective (toDualProd : NonemptyInterval α -> αᵒᵈ ×
 α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonemptyInterval.toProd_injective`：toProd_injective : Injective (toProd 
: NonemptyInterval α -> α × α)
-/
theorem toDualProd_injective : Injective (toDualProd : NonemptyInterval α → αᵒᵈ × α) :=
  toProd_injective
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : IsEmpty (NonemptyInterval α) :=
  ⟨fun s => isEmptyElim s.fst⟩
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton α] : Subsingleton (NonemptyInterval α) :=
  toDualProd_injective.subsingleton
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] : DecidableEq (NonemptyInterval α) :=
  toDualProd_injective.decidableEq
/-
**NonemptyInterval.le** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
形式化陈述：le : LE (NonemptyInterval α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance le : LE (NonemptyInterval α) :=
  ⟨fun s t => t.fst ≤ s.fst ∧ s.snd ≤ t.snd⟩
/-
**NonemptyInterval.le_def** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：le_def : s <= t ↔ t.fst <= s.fst ∧ s.snd <= t.snd
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def : s ≤ t ↔ t.fst ≤ s.fst ∧ s.snd ≤ t.snd :=
  Iff.rfl
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableLE α] : DecidableLE (NonemptyInterval α) :=
  fun _ _ => decidable_of_iff' _ le_def

/-- `toDualProd` as an order embedding. -/
@[simps]
/-
**NonemptyInterval.toDualProdHom** 是 Mathlib 中的一个定义，位于命名空间 `NonemptyInterval`。
形式化陈述：toDualProdHom : NonemptyInterval α ↪o αᵒᵈ × α where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonemptyInterval.toDualProd_injective`：toDualProd_injective : Injective 
(toDualProd : NonemptyInterval α -> αᵒᵈ × α)

--- 原说明 ---
`toDualProd` as an order embedding.
-/
def toDualProdHom : NonemptyInterval α ↪o αᵒᵈ × α where
  toFun := toDualProd
  inj' := toDualProd_injective
  map_rel_iff' := Iff.rfl

/-- Turn an interval into an interval in the dual order. -/
/-
**NonemptyInterval.dual** 是 Mathlib 中的一个定义，位于命名空间 `NonemptyInterval`。
形式化陈述：dual : NonemptyInterval α ≃ NonemptyInterval αᵒᵈ where toFun s
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonemptyInterval.fst_le_snd`：∀ {α : Type u_6} [inst : LE α] (self : None
mptyInterval α), self.toProd.1 ≤ self.toProd.2

--- 原说明 ---
Turn an interval into an interval in the dual order.
-/
def dual : NonemptyInterval α ≃ NonemptyInterval αᵒᵈ where
  toFun s := ⟨s.toProd.swap, s.fst_le_snd⟩
  invFun s := ⟨s.toProd.swap, s.fst_le_snd⟩

@[simp]
/-
**NonemptyInterval.fst_dual** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：fst_dual (s : NonemptyInterval α) : s.dual.fst = toDual s.snd
参数：s : NonemptyInterval α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_dual (s : NonemptyInterval α) : s.dual.fst = toDual s.snd :=
  rfl

@[simp]
/-
**NonemptyInterval.snd_dual** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：snd_dual (s : NonemptyInterval α) : s.dual.snd = toDual s.fst
参数：s : NonemptyInterval α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_dual (s : NonemptyInterval α) : s.dual.snd = toDual s.fst :=
  rfl

end LE

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] {s : NonemptyInterval α} {x : α × α} {a : α}

/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder (NonemptyInterval α) :=
  fast_instance% Preorder.lift toDualProd
/-
**NonemptyInterval.toDualProd_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：toDualProd_mono : Monotone (toDualProd : _ -> αᵒᵈ × α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDualProd_mono : Monotone (toDualProd : _ → αᵒᵈ × α) := fun _ _ => id
/-
**NonemptyInterval.toDualProd_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInte
rval`。
形式化陈述：toDualProd_strictMono : StrictMono (toDualProd : _ -> αᵒᵈ × α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDualProd_strictMono : StrictMono (toDualProd : _ → αᵒᵈ × α) := fun _ _ => id
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (NonemptyInterval α) (Set α) :=
  ⟨fun s => Icc s.fst s.snd⟩
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : Membership α (NonemptyInterval α) :=
  ⟨fun s a => a ∈ (s : Set α)⟩

@[simp]
/-
**NonemptyInterval.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：mem_mk {hx : x.1 <= x.2} : a in mk x hx ↔ x.1 <= a ∧ a <= x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk {hx : x.1 ≤ x.2} : a ∈ mk x hx ↔ x.1 ≤ a ∧ a ≤ x.2 :=
  Iff.rfl
/-
**NonemptyInterval.mem_def** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：mem_def : a in s ↔ s.fst <= a ∧ a <= s.snd
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_def : a ∈ s ↔ s.fst ≤ a ∧ a ≤ s.snd :=
  Iff.rfl
/-
**NonemptyInterval.coe_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：coe_nonempty (s : NonemptyInterval α) : (s : Set α).Nonempty
参数：s : NonemptyInterval α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
· 使用定理 `NonemptyInterval.fst_le_snd`：∀ {α : Type u_6} [inst : LE α] (self : None
mptyInterval α), self.toProd.1 ≤ self.toProd.2
-/
theorem coe_nonempty (s : NonemptyInterval α) : (s : Set α).Nonempty :=
  nonempty_Icc.2 s.fst_le_snd

/-- `{a}` as an interval. -/
@[simps]
/-
**NonemptyInterval.pure** 是 Mathlib 中的一个定义，位于命名空间 `NonemptyInterval`。
形式化陈述：pure (a : α) : NonemptyInterval α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`{a}` as an interval.
-/
def pure (a : α) : NonemptyInterval α :=
  ⟨⟨a, a⟩, le_rfl⟩
/-
**NonemptyInterval.mem_pure_self** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：mem_pure_self (a : α) : a in pure a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem mem_pure_self (a : α) : a ∈ pure a :=
  ⟨le_rfl, le_rfl⟩
/-
**NonemptyInterval.pure_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：pure_injective : Injective (pure : α -> NonemptyInterval α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem pure_injective : Injective (pure : α → NonemptyInterval α) := fun _ _ =>
  congr_arg <| Prod.fst ∘ toProd

@[simp]
/-
**NonemptyInterval.dual_pure** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：dual_pure (a : α) : dual (pure a) = pure (toDual a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_pure (a : α) : dual (pure a) = pure (toDual a) :=
  rfl
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (NonemptyInterval α) :=
  ⟨pure default⟩
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nonempty (NonemptyInterval α) :=
  Nonempty.map pure (by infer_instance)
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial α] : Nontrivial (NonemptyInterval α) :=
  pure_injective.nontrivial

/-- Pushforward of nonempty intervals. -/
@[simps!]
/-
**NonemptyInterval.map** 是 Mathlib 中的一个定义，位于命名空间 `NonemptyInterval`。
形式化陈述：map (f : α ->o β) (a : NonemptyInterval α) : NonemptyInterval β
参数：f : α ->o β；a : NonemptyInterval α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pushforward of nonempty intervals.
-/
def map (f : α →o β) (a : NonemptyInterval α) : NonemptyInterval β :=
  ⟨a.toProd.map f f, f.mono a.fst_le_snd⟩

@[simp]
/-
**NonemptyInterval.map_pure** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：map_pure (f : α ->o β) (a : α) : (pure a).map f = pure (f a)
参数：f : α ->o β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) :=
  rfl

@[simp]
/-
**NonemptyInterval.map_map** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：map_map (g : β ->o γ) (f : α ->o β) (a : NonemptyInterval α) : (a.map f).m
ap g = a.map (g.comp f)
参数：g : β ->o γ；f : α ->o β；a : NonemptyInterval α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_map (g : β →o γ) (f : α →o β) (a : NonemptyInterval α) :
    (a.map f).map g = a.map (g.comp f) :=
  rfl

@[simp]
/-
**NonemptyInterval.dual_map** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：dual_map (f : α ->o β) (a : NonemptyInterval α) : dual (a.map f) = a.dual.
map f.dual
参数：f : α ->o β；a : NonemptyInterval α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_map (f : α →o β) (a : NonemptyInterval α) :
    dual (a.map f) = a.dual.map f.dual :=
  rfl

/-- Binary pushforward of nonempty intervals. -/
@[simps]
/-
**NonemptyInterval.map** 是 Mathlib 中的一个定义，位于命名空间 `NonemptyInterval`。
形式化陈述：map (f : α ->o β) (a : NonemptyInterval α) : NonemptyInterval β
参数：f : α ->o β；a : NonemptyInterval α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Binary pushforward of nonempty intervals.
-/
def map₂ (f : α → β → γ) (h₀ : ∀ b, Monotone fun a => f a b) (h₁ : ∀ a, Monotone (f a)) :
    NonemptyInterval α → NonemptyInterval β → NonemptyInterval γ := fun s t =>
  ⟨(f s.fst t.fst, f s.snd t.snd), (h₀ _ s.fst_le_snd).trans <| h₁ _ t.fst_le_snd⟩

@[simp]
/-
**NonemptyInterval.map** 是 Mathlib 中的一个定义，位于命名空间 `NonemptyInterval`。
形式化陈述：map (f : α ->o β) (a : NonemptyInterval α) : NonemptyInterval β
参数：f : α ->o β；a : NonemptyInterval α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_pure (f : α → β → γ) (h₀ h₁) (a : α) (b : β) :
    map₂ f h₀ h₁ (pure a) (pure b) = pure (f a b) :=
  rfl

@[simp]
/-
**NonemptyInterval.dual_map** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：dual_map (f : α ->o β) (a : NonemptyInterval α) : dual (a.map f) = a.dual.
map f.dual
参数：f : α ->o β；a : NonemptyInterval α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_map₂ (f : α → β → γ) (h₀ h₁ s t) :
    dual (map₂ f h₀ h₁ s t) =
      map₂ (fun a b => toDual <| f (ofDual a) <| ofDual b) (fun _ => (h₀ _).dual)
        (fun _ => (h₁ _).dual) (dual s) (dual t) :=
  rfl

variable [BoundedOrder α]
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTop (NonemptyInterval α) where
  top := ⟨⟨⊥, ⊤⟩, bot_le⟩
  le_top _ := ⟨bot_le, le_top⟩

@[simp]
/-
**NonemptyInterval.dual_top** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：dual_top : dual (⊤ : NonemptyInterval α) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_top : dual (⊤ : NonemptyInterval α) = ⊤ :=
  rfl

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {s t : NonemptyInterval α} {a b : α}

/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (NonemptyInterval α) :=
  fast_instance% PartialOrder.lift _ toDualProd_injective
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableLE α] : DecidableLE (NonemptyInterval α) :=
  fun _ _ => decidable_of_iff' _ le_def

/-- Consider a nonempty interval `[a, b]` as the set `[a, b]`. -/
/-
**NonemptyInterval.coeHom** 是 Mathlib 中的一个定义，位于命名空间 `NonemptyInterval`。
形式化陈述：coeHom : NonemptyInterval α ↪o Set α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider a nonempty interval `[a, b]` as the set `[a, b]`.
-/
def coeHom : NonemptyInterval α ↪o Set α :=
  OrderEmbedding.ofMapLEIff (fun s => Icc s.fst s.snd) fun s _ => Icc_subset_Icc_iff s.fst_le_snd
/-
**NonemptyInterval.setLike** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
形式化陈述：setLike : SetLike (NonemptyInterval α) α where coe s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance setLike : SetLike (NonemptyInterval α) α where
  coe s := Icc s.fst s.snd
  coe_injective := coeHom.injective

@[norm_cast]
/-
**NonemptyInterval.coe_subset_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：coe_subset_coe : (s : Set α) subseteq t ↔ (s : NonemptyInterval α) <= t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
-/
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ (s : NonemptyInterval α) ≤ t :=
  (@coeHom α _).le_iff_le

@[norm_cast]
/-
**NonemptyInterval.coe_ssubset_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：coe_ssubset_coe : (s : Set α) ⊂ t ↔ s < t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
-/
theorem coe_ssubset_coe : (s : Set α) ⊂ t ↔ s < t :=
  (@coeHom α _).lt_iff_lt

@[simp]
/-
**NonemptyInterval.coe_coeHom** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：coe_coeHom : (coeHom : NonemptyInterval α -> Set α) = ((↑) : NonemptyInter
val α -> Set α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coeHom : (coeHom : NonemptyInterval α → Set α) = ((↑) : NonemptyInterval α → Set α) :=
  rfl
/-
**NonemptyInterval.coe_def** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：coe_def (s : NonemptyInterval α) : (s : Set α) = Set.Icc s.toProd.1 s.toPr
od.2
参数：s : NonemptyInterval α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_def (s : NonemptyInterval α) : (s : Set α) = Set.Icc s.toProd.1 s.toProd.2 := rfl

@[simp, norm_cast]
/-
**NonemptyInterval.coe_pure** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：coe_pure (a : α) : (pure a : Set α) = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
-/
theorem coe_pure (a : α) : (pure a : Set α) = {a} :=
  Icc_self _

@[simp]
/-
**NonemptyInterval.mem_pure** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：mem_pure : b in pure a ↔ b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `NonemptyInterval.coe_pure`：coe_pure (a : α) : (pure a : Set α) = {a}
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_pure : b ∈ pure a ↔ b = a := by
  rw [← SetLike.mem_coe, coe_pure, mem_singleton_iff]

@[simp, norm_cast]
/-
**NonemptyInterval.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：coe_top [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Set α) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_bot_top`：Icc_bot_top [Preorder α] [BoundedOrder α] : Icc (⊥ : α)
 ⊤ = univ
-/
theorem coe_top [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Set α) = univ :=
  Icc_bot_top

@[simp, norm_cast]
/-
**NonemptyInterval.coe_dual** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：coe_dual (s : NonemptyInterval α) : (dual s : Set αᵒᵈ) = ofDual ⁻¹' s
参数：s : NonemptyInterval α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_toDual`：Icc_toDual : Icc (toDual a) (toDual b) = ofDual ⁻¹' Icc 
b a
-/
theorem coe_dual (s : NonemptyInterval α) : (dual s : Set αᵒᵈ) = ofDual ⁻¹' s :=
  Icc_toDual
/-
**NonemptyInterval.subset_coe_map** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：subset_coe_map (f : α ->o β) (s : NonemptyInterval α) : f '' s subseteq s.
map f
参数：f : α ->o β；s : NonemptyInterval α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem subset_coe_map (f : α →o β) (s : NonemptyInterval α) : f '' s ⊆ s.map f :=
  image_subset_iff.2 fun _ ha => ⟨f.mono ha.1, f.mono ha.2⟩

end PartialOrder

section Lattice

variable [Lattice α]

/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (NonemptyInterval α) :=
  ⟨fun s t => ⟨⟨s.fst ⊓ t.fst, s.snd ⊔ t.snd⟩, inf_le_left.trans <| s.fst_le_snd.trans le_sup_left⟩⟩
/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup (NonemptyInterval α) :=
  fast_instance% toDualProd_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[simp]
/-
**NonemptyInterval.fst_sup** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：fst_sup (s t : NonemptyInterval α) : (s ⊔ t).fst = s.fst ⊓ t.fst
参数：s t : NonemptyInterval α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_sup (s t : NonemptyInterval α) : (s ⊔ t).fst = s.fst ⊓ t.fst :=
  rfl

@[simp]
/-
**NonemptyInterval.snd_sup** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：snd_sup (s t : NonemptyInterval α) : (s ⊔ t).snd = s.snd ⊔ t.snd
参数：s t : NonemptyInterval α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_sup (s t : NonemptyInterval α) : (s ⊔ t).snd = s.snd ⊔ t.snd :=
  rfl

end Lattice

end NonemptyInterval

/-- The closed intervals in an order.

We represent intervals either as `⊥` or a nonempty interval given by its endpoints `fst`, `snd`.
To convert intervals to the set of elements between these endpoints, use the coercion
`Interval α → Set α`. -/
/-
**Interval** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Interval (α : Type*) [LE α]
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closed intervals in an order.

We represent intervals either as `⊥` or a nonempty interval given by its endpoin
ts `fst`, `snd`.
To convert intervals to the set of elements between these endpoints, use the coe
rcion
`Interval α → Set α`.
-/
def Interval (α : Type*) [LE α] :=
  WithBot (NonemptyInterval α)
deriving Inhabited, LE, OrderBot

namespace Interval

section LE

variable [LE α]

/-- Canonical coercion from nonempty intervals to intervals -/
/-
**Interval.coe** 是 Mathlib 中的一个定义，位于命名空间 `Interval`。
形式化陈述：{α : Type u_1} → [inst : LE α] → NonemptyInterval α → Interval α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Canonical coercion from nonempty intervals to intervals
-/
@[coe] def coe (x : NonemptyInterval α) : Interval α := (x : WithBot _)
/-
**Interval.** 是 Mathlib 中的一个实例，位于命名空间 `Interval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Canonical coercion from nonempty intervals to intervals
-/
instance : Coe (NonemptyInterval α) (Interval α) :=
  ⟨coe⟩
/-
**Interval.canLift** 是 Mathlib 中的一个实例，位于命名空间 `Interval`。
形式化陈述：canLift : CanLift (Interval α) (NonemptyInterval α) (↑) fun r => r != ⊥
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance canLift : CanLift (Interval α) (NonemptyInterval α) (↑) fun r => r ≠ ⊥ :=
  WithBot.canLift

/-- Recursor for `Interval` using the preferred forms `⊥` and `↑a`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/-
**Interval.recBotCoe** 是 Mathlib 中的一个定义，位于命名空间 `Interval`。
形式化陈述：recBotCoe {C : Interval α -> Sort*} (bot : C ⊥) (coe : forall a : Nonempty
Interval α, C a) : forall n : Interval α, C n
参数：bot : C ⊥；coe : forall a : NonemptyInterval α, C a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursor for `Interval` using the preferred forms `⊥` and `↑a`.
-/
def recBotCoe {C : Interval α → Sort*} (bot : C ⊥) (coe : ∀ a : NonemptyInterval α, C a) :
    ∀ n : Interval α, C n :=
  WithBot.recBotCoe bot coe
/-
**Interval.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：coe_injective : Injective ((↑) : NonemptyInterval α -> Interval α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_injective`：coe_injective : Injective ((↑) : α -> WithBot α)
-/
theorem coe_injective : Injective ((↑) : NonemptyInterval α → Interval α) :=
  WithBot.coe_injective

@[norm_cast]
/-
**Interval.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：coe_inj {s t : NonemptyInterval α} : (s : Interval α) = t ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_inj`：coe_inj : (a : WithBot α) = b ↔ a = b
-/
theorem coe_inj {s t : NonemptyInterval α} : (s : Interval α) = t ↔ s = t :=
  WithBot.coe_inj

protected
/-
**Interval.** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem «forall» {p : Interval α → Prop} : (∀ s, p s) ↔ p ⊥ ∧ ∀ s : NonemptyInterval α, p s :=
  Option.forall

protected
/-
**Interval.** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem «exists» {p : Interval α → Prop} : (∃ s, p s) ↔ p ⊥ ∨ ∃ s : NonemptyInterval α, p s :=
  Option.exists
/-
**Interval.** 是 Mathlib 中的一个实例，位于命名空间 `Interval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : Unique (Interval α) :=
  inferInstanceAs <| Unique (Option _)

/-- Turn an interval into an interval in the dual order. -/
/-
**Interval.dual** 是 Mathlib 中的一个定义，位于命名空间 `Interval`。
形式化陈述：dual : Interval α ≃ Interval αᵒᵈ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn an interval into an interval in the dual order.
-/
def dual : Interval α ≃ Interval αᵒᵈ :=
  NonemptyInterval.dual.withBotCongr

end LE

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ]

/-
**Interval.** 是 Mathlib 中的一个实例，位于命名空间 `Interval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder (Interval α) :=
  inferInstanceAs <| Preorder (WithBot _)

/-- `{a}` as an interval. -/
/-
**Interval.pure** 是 Mathlib 中的一个定义，位于命名空间 `Interval`。
形式化陈述：pure (a : α) : Interval α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`{a}` as an interval.
-/
def pure (a : α) : Interval α :=
  NonemptyInterval.pure a
/-
**Interval.pure_injective** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：pure_injective : Injective (pure : α -> Interval α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Interval.coe_injective`：coe_injective : Injective ((↑) : NonemptyInterva
l α -> Interval α)
· 使用定理 `NonemptyInterval.pure_injective`：pure_injective : Injective (pure : α ->
 NonemptyInterval α)
-/
theorem pure_injective : Injective (pure : α → Interval α) :=
  coe_injective.comp NonemptyInterval.pure_injective

@[simp]
/-
**Interval.dual_pure** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：dual_pure (a : α) : dual (pure a) = pure (toDual a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_pure (a : α) : dual (pure a) = pure (toDual a) :=
  rfl

@[simp]
/-
**Interval.dual_bot** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：dual_bot : dual (⊥ : Interval α) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_bot : dual (⊥ : Interval α) = ⊥ :=
  rfl

@[simp]
/-
**Interval.pure_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：pure_ne_bot {a : α} : pure a != ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_ne_bot`：coe_ne_bot : (a : WithBot α) != ⊥
-/
theorem pure_ne_bot {a : α} : pure a ≠ ⊥ :=
  WithBot.coe_ne_bot

@[simp]
/-
**Interval.bot_ne_pure** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：bot_ne_pure {a : α} : ⊥ != pure a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.bot_ne_coe`：bot_ne_coe : ⊥ != (a : WithBot α)
-/
theorem bot_ne_pure {a : α} : ⊥ ≠ pure a :=
  WithBot.bot_ne_coe
/-
**Interval.** 是 Mathlib 中的一个实例，位于命名空间 `Interval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nontrivial (Interval α) :=
  Option.nontrivial

/-- Pushforward of intervals. -/
/-
**Interval.map** 是 Mathlib 中的一个定义，位于命名空间 `Interval`。
形式化陈述：map (f : α ->o β) : Interval α -> Interval β
参数：f : α ->o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pushforward of intervals.
-/
def map (f : α →o β) : Interval α → Interval β :=
  WithBot.map (NonemptyInterval.map f)

@[simp]
/-
**Interval.map_pure** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：map_pure (f : α ->o β) (a : α) : (pure a).map f = pure (f a)
参数：f : α ->o β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) :=
  rfl

@[simp]
/-
**Interval.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：map_map (g : β ->o γ) (f : α ->o β) (s : Interval α) : (s.map f).map g = s
.map (g.comp f)
参数：g : β ->o γ；f : α ->o β；s : Interval α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} (h : β → 
γ) (g : α → β) (x : Option α),   Option.map h (Option.map g x) = Option.map (h ∘
 g) …
-/
theorem map_map (g : β →o γ) (f : α →o β) (s : Interval α) : (s.map f).map g = s.map (g.comp f) :=
  Option.map_map _ _ _

@[simp]
/-
**Interval.dual_map** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：dual_map (f : α ->o β) (s : Interval α) : dual (s.map f) = s.dual.map f.du
al
参数：f : α ->o β；s : Interval α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.map_comm`：map_comm {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂
 : γ -> δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) : map g₁ (map f₁ a) = map g₂ (map f₂ 
a)
-/
theorem dual_map (f : α →o β) (s : Interval α) : dual (s.map f) = s.dual.map f.dual := by
  cases s
  · rfl
  · exact WithBot.map_comm rfl _

@[simp, norm_cast]
/-
**Interval.coe_le_coe** 是 Mathlib 中的一个引理，位于命名空间 `Interval`。
形式化陈述：coe_le_coe {s t : NonemptyInterval α} : (s : Interval α) <= t ↔ s <= t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
-/
lemma coe_le_coe {s t : NonemptyInterval α} : (s : Interval α) ≤ t ↔ s ≤ t :=
  WithBot.coe_le_coe

variable [BoundedOrder α]
/-
**Interval.boundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `Interval`。
形式化陈述：boundedOrder : BoundedOrder (Interval α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance boundedOrder : BoundedOrder (Interval α) :=
  inferInstanceAs <| BoundedOrder (WithBot _)

@[simp]
/-
**Interval.dual_top** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：dual_top : dual (⊤ : Interval α) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_top : dual (⊤ : Interval α) = ⊤ :=
  rfl

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {s t : Interval α} {a b : α}

/-
**Interval.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Interval`。
形式化陈述：partialOrder : PartialOrder (Interval α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance partialOrder : PartialOrder (Interval α) :=
  inferInstanceAs <| PartialOrder (WithBot _)

/-- Consider an interval `[a, b]` as the set `[a, b]`. -/
/-
**Interval.coeHom** 是 Mathlib 中的一个定义，位于命名空间 `Interval`。
形式化陈述：coeHom : Interval α ↪o Set α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider an interval `[a, b]` as the set `[a, b]`.
-/
def coeHom : Interval α ↪o Set α :=
  OrderEmbedding.ofMapLEIff
    (fun s =>
      match s with
      | ⊥ => ∅
      | some s => s)
    fun s t =>
    match s, t with
    | ⊥, _ => iff_of_true bot_le bot_le
    | some s, ⊥ =>
      iff_of_false (fun h => s.coe_nonempty.ne_empty <| le_bot_iff.1 h) (WithBot.not_coe_le_bot _)
    | some _, some _ => (@NonemptyInterval.coeHom α _).le_iff_le.trans WithBot.coe_le_coe.symm
/-
**Interval.setLike** 是 Mathlib 中的一个实例，位于命名空间 `Interval`。
形式化陈述：setLike : SetLike (Interval α) α where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance setLike : SetLike (Interval α) α where
  coe := coeHom
  coe_injective := coeHom.injective

@[norm_cast]
/-
**Interval.coe_subset_coe** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：coe_subset_coe : (s : Set α) subseteq t ↔ s <= t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
-/
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ s ≤ t :=
  (@coeHom α _).le_iff_le

@[norm_cast]
/-
**Interval.coe_sSubset_coe** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：coe_sSubset_coe : (s : Set α) ⊂ t ↔ s < t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
-/
theorem coe_sSubset_coe : (s : Set α) ⊂ t ↔ s < t :=
  (@coeHom α _).lt_iff_lt

@[simp, norm_cast]
/-
**Interval.coe_pure** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：coe_pure (a : α) : (pure a : Set α) = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
-/
theorem coe_pure (a : α) : (pure a : Set α) = {a} :=
  Icc_self _

@[simp, norm_cast]
/-
**Interval.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：coe_coe (s : NonemptyInterval α) : ((s : Interval α) : Set α) = s
参数：s : NonemptyInterval α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe (s : NonemptyInterval α) : ((s : Interval α) : Set α) = s :=
  rfl

@[simp, norm_cast]
/-
**Interval.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：coe_bot : ((⊥ : Interval α) : Set α) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ((⊥ : Interval α) : Set α) = ∅ :=
  rfl

@[simp, norm_cast]
/-
**Interval.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：coe_top [BoundedOrder α] : ((⊤ : Interval α) : Set α) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_bot_top`：Icc_bot_top [Preorder α] [BoundedOrder α] : Icc (⊥ : α)
 ⊤ = univ
-/
theorem coe_top [BoundedOrder α] : ((⊤ : Interval α) : Set α) = univ :=
  Icc_bot_top

@[simp, norm_cast]
/-
**Interval.coe_dual** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：coe_dual (s : Interval α) : (dual s : Set αᵒᵈ) = ofDual ⁻¹' s
参数：s : Interval α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonemptyInterval.coe_dual`：coe_dual (s : NonemptyInterval α) : (dual s :
 Set αᵒᵈ) = ofDual ⁻¹' s
-/
theorem coe_dual (s : Interval α) : (dual s : Set αᵒᵈ) = ofDual ⁻¹' s := by
  cases s with
  | bot => rfl
  | coe s₀ => exact NonemptyInterval.coe_dual s₀
/-
**Interval.subset_coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PartialOrder α] [inst_1 : PartialO
rder β] (f : α →o β) (s : Interval α),   ⇑f '' ↑s ⊆ ↑(Interval.map f s)
参数：f : α →o β；s : Interval α；Interval.map f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `NonemptyInterval.subset_coe_map`：subset_coe_map (f : α ->o β) (s : Nonem
ptyInterval α) : f '' s subseteq s.map f
-/
theorem subset_coe_map (f : α →o β) : ∀ s : Interval α, f '' s ⊆ s.map f
  | ⊥ => by simp
  | (s : NonemptyInterval α) => s.subset_coe_map _

@[simp]
/-
**Interval.mem_pure** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：mem_pure : b in pure a ↔ b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Interval.coe_pure`：coe_pure (a : α) : (pure a : Set α) = {a}
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_pure : b ∈ pure a ↔ b = a := by rw [← SetLike.mem_coe, coe_pure, mem_singleton_iff]
/-
**Interval.mem_pure_self** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：mem_pure_self (a : α) : a in pure a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Interval.mem_pure`：mem_pure : b in pure a ↔ b = a
-/
theorem mem_pure_self (a : α) : a ∈ pure a :=
  mem_pure.2 rfl

end PartialOrder

section Lattice

variable [Lattice α]

/-
**Interval.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Interval`。
形式化陈述：semilatticeSup : SemilatticeSup (Interval α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeSup : SemilatticeSup (Interval α) :=
  inferInstanceAs <| SemilatticeSup (WithBot _)

section Decidable

variable [DecidableLE α]

/-
**Interval.lattice** 是 Mathlib 中的一个实例，位于命名空间 `Interval`。
形式化陈述：lattice : Lattice (Interval α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lattice : Lattice (Interval α) :=
  { Interval.semilatticeSup with
    inf := fun s t =>
      match s, t with
      | ⊥, _ => ⊥
      | _, ⊥ => ⊥
      | some s, some t =>
        if h : s.fst ≤ t.snd ∧ t.fst ≤ s.snd then
          coe ⟨⟨s.fst ⊔ t.fst, s.snd ⊓ t.snd⟩,
              sup_le (le_inf s.fst_le_snd h.1) <| le_inf h.2 t.fst_le_snd⟩
        else ⊥
    inf_le_left := fun s t =>
      match s, t with
      | ⊥, ⊥ => bot_le
      | ⊥, some _ => bot_le
      | some _, ⊥ => bot_le
      | some s, some t => by
        change dite _ _ _ ≤ _
        split_ifs
        · exact WithBot.coe_le_coe.2 ⟨le_sup_left, inf_le_left⟩
        · exact bot_le
    inf_le_right := fun s t =>
      match s, t with
      | ⊥, ⊥ => bot_le
      | ⊥, some _ => bot_le
      | some _, ⊥ => bot_le
      | some s, some t => by
        change dite _ _ _ ≤ _
        split_ifs
        · exact WithBot.coe_le_coe.2 ⟨le_sup_right, inf_le_right⟩
        · exact bot_le
    le_inf := fun s t c =>
      match s, t, c with
      | ⊥, _, _ => fun _ _ => bot_le
      | (s : NonemptyInterval α), t, c => fun hb hc => by
        lift t to NonemptyInterval α using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hb
        lift c to NonemptyInterval α using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hc
        change _ ≤ dite _ _ _
        simp only [Interval.coe_le_coe] at hb hc ⊢
        rw [dif_pos, Interval.coe_le_coe]
        · exact ⟨sup_le hb.1 hc.1, le_inf hb.2 hc.2⟩
        -- Porting note: had to add the next 6 lines including the changes because
        -- it seems that lean cannot automatically turn `NonemptyInterval.toDualProd s`
        -- into `s.toProd` anymore.
        rcases hb with ⟨hb₁, hb₂⟩
        rcases hc with ⟨hc₁, hc₂⟩
        change t.toProd.fst ≤ s.toProd.fst at hb₁
        change s.toProd.snd ≤ t.toProd.snd at hb₂
        change c.toProd.fst ≤ s.toProd.fst at hc₁
        change s.toProd.snd ≤ c.toProd.snd at hc₂
        -- Porting note: originally it just had `hb.1` etc. in this next line
        exact ⟨hb₁.trans <| s.fst_le_snd.trans hc₂, hc₁.trans <| s.fst_le_snd.trans hb₂⟩ }
/-
**Interval.inf_coe** 是 Mathlib 中的一个引理，位于命名空间 `Interval`。
形式化陈述：inf_coe (s t : NonemptyInterval α) : (s : Interval α) ⊓ t = if h : s.fst <
= t.snd ∧ t.fst <= s.snd then coe ⟨⟨s.fst ⊔ t.fst, s.snd ⊓ t.snd⟩, sup_le (le_in
f s.fst_le_snd h.1) le_inf h.2 t.fst_le_snd⟩ else ⊥
参数：s t : NonemptyInterval α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inf_coe (s t : NonemptyInterval α) :
    (s : Interval α) ⊓ t = if h : s.fst ≤ t.snd ∧ t.fst ≤ s.snd then
      coe ⟨⟨s.fst ⊔ t.fst, s.snd ⊓ t.snd⟩,
        sup_le (le_inf s.fst_le_snd h.1) <| le_inf h.2 t.fst_le_snd⟩
      else ⊥ := rfl

@[simp, norm_cast]
/-
**Interval.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : DecidableLE α] (s t : Interv
al α), ↑(s ⊓ t) = ↑s ∩ ↑t
参数：s t : Interval α；s ⊓ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bot_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊓ a = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `inf_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), a ⊓ ⊥ = ⊥
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `NonemptyInterval.fst_le_snd`：∀ {α : Type u_6} [inst : LE α] (self : None
mptyInterval α), self.toProd.1 ≤ self.toProd.2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Icc_inter_Icc`：Icc_inter_Icc : Icc a₁ b₁ inter Icc a₂ b₂ = Icc (a₁ ⊔
 a₂) (b₁ ⊓ b₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Set.Icc_eq_empty`：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem coe_inf : ∀ s t : Interval α, (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t
  | ⊥, _ => by
    rw [bot_inf_eq]
    exact (empty_inter _).symm
  | (s : NonemptyInterval α), ⊥ => by
    rw [inf_bot_eq]
    exact (inter_empty _).symm
  | (s : NonemptyInterval α), (t : NonemptyInterval α) => by
    simp only [coe_coe, NonemptyInterval.coe_def, Icc_inter_Icc, inf_coe]
    split_ifs with h
    · simp only [coe_coe, NonemptyInterval.coe_def]
    · refine (Icc_eq_empty <| mt ?_ h).symm
      exact fun h ↦ ⟨le_sup_left.trans <| h.trans inf_le_right,
        le_sup_right.trans <| h.trans inf_le_left⟩

end Decidable

@[simp, norm_cast]
/-
**Interval.disjoint_coe** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：disjoint_coe (s t : Interval α) : Disjoint (s : Set α) t ↔ Disjoint s t
参数：s t : Interval α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Interval.coe_subset_coe`：coe_subset_coe : (s : Set α) subseteq t ↔ s <= 
t
· 使用定理 `Interval.coe_inf`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Decidabl
eLE α] (s t : Interval α), ↑(s ⊓ t) = ↑s ∩ ↑t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_coe (s t : Interval α) : Disjoint (s : Set α) t ↔ Disjoint s t := by
  classical
    rw [disjoint_iff_inf_le, disjoint_iff_inf_le, ← coe_subset_coe, coe_inf]
    rfl

end Lattice

end Interval

namespace NonemptyInterval

section Preorder

variable [Preorder α] {s t : NonemptyInterval α} {a : α}

@[simp, norm_cast]
/-
**NonemptyInterval.coe_pure_interval** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval
`。
形式化陈述：coe_pure_interval (a : α) : (pure a : Interval α) = Interval.pure a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pure_interval (a : α) : (pure a : Interval α) = Interval.pure a :=
  rfl

@[simp, norm_cast]
/-
**NonemptyInterval.coe_eq_pure** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：coe_eq_pure : (s : Interval α) = Interval.pure a ↔ s = pure a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Interval.coe_inj`：coe_inj {s t : NonemptyInterval α} : (s : Interval α) 
= t ↔ s = t
· 使用定理 `NonemptyInterval.coe_pure_interval`：coe_pure_interval (a : α) : (pure a 
: Interval α) = Interval.pure a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_eq_pure : (s : Interval α) = Interval.pure a ↔ s = pure a := by
  rw [← Interval.coe_inj, coe_pure_interval]

@[simp, norm_cast]
/-
**NonemptyInterval.coe_top_interval** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`
。
形式化陈述：coe_top_interval [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Interval α
) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top_interval [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Interval α) = ⊤ :=
  rfl

end Preorder

@[simp, norm_cast]
/-
**NonemptyInterval.mem_coe_interval** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`
。
形式化陈述：mem_coe_interval [PartialOrder α] {s : NonemptyInterval α} {x : α} : x in 
(s : Interval α) ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe_interval [PartialOrder α] {s : NonemptyInterval α} {x : α} :
    x ∈ (s : Interval α) ↔ x ∈ s :=
  Iff.rfl

@[simp, norm_cast]
/-
**NonemptyInterval.coe_sup_interval** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`
。
形式化陈述：coe_sup_interval [Lattice α] (s t : NonemptyInterval α) : (↑(s ⊔ t) : Inte
rval α) = ↑s ⊔ ↑t
参数：s t : NonemptyInterval α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup_interval [Lattice α] (s t : NonemptyInterval α) :
    (↑(s ⊔ t) : Interval α) = ↑s ⊔ ↑t :=
  rfl

end NonemptyInterval

namespace Interval

section CompleteLattice

variable [CompleteLattice α]

open scoped Classical in
/-
**Interval.completeLattice** 是 Mathlib 中的一个实例，位于命名空间 `Interval`。
形式化陈述：completeLattice [DecidableLE α] : CompleteLattice (Interval α) where sSup
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance completeLattice [DecidableLE α] : CompleteLattice (Interval α) where
  sSup := fun S =>
    if h : S ⊆ {⊥} then ⊥
    else
      coe
        ⟨⟨⨅ (s : NonemptyInterval α) (_ : ↑s ∈ S), s.fst,
            ⨆ (s : NonemptyInterval α) (_ : ↑s ∈ S), s.snd⟩, by
          obtain ⟨s, hs, ha⟩ := not_subset.1 h
          lift s to NonemptyInterval α using ha
          exact iInf₂_le_of_le s hs (le_iSup₂_of_le s hs s.fst_le_snd)⟩
  isLUB_sSup _ := by
    constructor
    · intro s ha
      split_ifs with h
      · exact (h ha).le
      cases s
      · exact bot_le
      · -- Porting note: This case was
        -- `exact WithBot.some_le_some.2 ⟨iInf₂_le _ ha, le_iSup₂_of_le _ ha le_rfl⟩`
        -- but there seems to be a defEq-problem at `iInf₂_le` that lean cannot resolve yet.
        apply Interval.coe_le_coe.2
        constructor
        · apply iInf₂_le
          exact ha
        · exact le_iSup₂_of_le _ ha le_rfl
    · intro s ha
      split_ifs with h
      · exact bot_le
      obtain ⟨b, hs, hb⟩ := not_subset.1 h
      lift s to NonemptyInterval α using ne_bot_of_le_ne_bot hb (ha hs)
      exact
        Interval.coe_le_coe.2
          ⟨le_iInf₂ fun c hc => (WithBot.coe_le_coe.1 <| ha hc).1,
            iSup₂_le fun c hc => (WithBot.coe_le_coe.1 <| ha hc).2⟩
  sInf := fun S =>
    if h :
        ⊥ ∉ S ∧
          ∀ ⦃s : NonemptyInterval α⦄,
            ↑s ∈ S → ∀ ⦃t : NonemptyInterval α⦄, ↑t ∈ S → s.fst ≤ t.snd then
      coe
        ⟨⟨⨆ (s : NonemptyInterval α) (_ : ↑s ∈ S), s.fst,
            ⨅ (s : NonemptyInterval α) (_ : ↑s ∈ S), s.snd⟩,
          iSup₂_le fun s hs => le_iInf₂ <| h.2 hs⟩
    else ⊥
  isGLB_sInf s₁ := by
    constructor
    · intro s ha
      split_ifs with h
      · lift s to NonemptyInterval α using ne_of_mem_of_not_mem ha h.1
        -- Porting note: Lean failed to figure out the function `f` by itself,
        -- so I added it through manually
        let f := fun (s : NonemptyInterval α) (_ : ↑s ∈ s₁) => s.toProd.fst
        exact WithBot.coe_le_coe.2 ⟨le_iSup₂ (f := f) s ha, iInf₂_le s ha⟩
      · exact bot_le
    · intro s ha
      cases s with
      | bot => exact bot_le
      | coe s =>
        split_ifs with h
        · exact WithBot.coe_le_coe.2
            ⟨iSup₂_le fun t hb => (WithBot.coe_le_coe.1 <| ha hb).1,
              le_iInf₂ fun t hb => (WithBot.coe_le_coe.1 <| ha hb).2⟩
        · rw [not_and_or, not_not] at h
          rcases h with h | h
          · exact ha h
          · cases h fun b hb c hc ↦ (WithBot.coe_le_coe.1 <| ha hb).1.trans
              (s.fst_le_snd.trans (WithBot.coe_le_coe.1 <| ha hc).2)

@[simp, norm_cast]
/-
**Interval.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：coe_sInf [DecidableLE α] (S : Set (Interval α)) : ↑(sInf S) = ⋂ s in S, (s
 : Set α)
参数：S : Set (Interval α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eq_empty_of_subset_empty`：eq_empty_of_subset_empty {s : Set α} : s s
ubseteq ∅ -> s = ∅
· 使用定理 `Set.iInter₂_subset_of_subset`：iInter₂_subset_of_subset {s : forall i, κ 
i -> Set α} {t : Set α} (i : ι) (j : κ i) (h : s i j subseteq t) : ⋂ (i) (j), s 
i j subseteq t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem coe_sInf [DecidableLE α] (S : Set (Interval α)) : ↑(sInf S) = ⋂ s ∈ S, (s : Set α) := by
  classical
  change ((dite _ _ _ : Interval α) : Set α) = ⋂ (s : Interval α) (_ : s ∈ S), (s : Set α)
  split_ifs with h
  · ext
    simp [Interval.forall, h.1, ← forall_and, ← NonemptyInterval.mem_def]
  simp_rw [not_and_or, Classical.not_not] at h
  rcases h with h | h
  · refine (eq_empty_of_subset_empty ?_).symm
    exact iInter₂_subset_of_subset _ h Subset.rfl
  · refine (not_nonempty_iff_eq_empty.1 ?_).symm
    rintro ⟨x, hx⟩
    rw [mem_iInter₂] at hx
    exact h fun s ha t hb => (hx _ ha).1.trans (hx _ hb).2

@[simp, norm_cast]
/-
**Interval.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：coe_iInf [DecidableLE α] (f : ι -> Interval α) : ↑(⨅ i, f i) = ⋂ i, (f i :
 Set α)
参数：f : ι -> Interval α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Interval.coe_sInf`：coe_sInf [DecidableLE α] (S : Set (Interval α)) : ↑(s
Inf S) = ⋂ s in S, (s : Set α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf [DecidableLE α] (f : ι → Interval α) :
    ↑(⨅ i, f i) = ⋂ i, (f i : Set α) := by simp [iInf]

@[norm_cast]
/-
**Interval.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：coe_iInf [DecidableLE α] (f : ι -> Interval α) : ↑(⨅ i, f i) = ⋂ i, (f i :
 Set α)
参数：f : ι -> Interval α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Interval.coe_sInf`：coe_sInf [DecidableLE α] (S : Set (Interval α)) : ↑(s
Inf S) = ⋂ s in S, (s : Set α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf₂ [DecidableLE α] (f : ∀ i, κ i → Interval α) :
    ↑(⨅ (i) (j), f i j) = ⋂ (i) (j), (f i j : Set α) := by simp_rw [coe_iInf]

end CompleteLattice

end Interval

