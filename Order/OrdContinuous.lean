/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.RelIso.Basic

/-!
# Order continuity

We say that a function is *left order continuous* if it sends all least upper bounds
to least upper bounds. The order dual notion is called *right order continuity*.

For monotone functions `ℝ → ℝ` these notions correspond to the usual left and right continuity.

We prove some basic lemmas (`map_sup`, `map_sSup` etc) and prove that a `RelIso` is both left
and right order continuous.
-/

@[expose] public section


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

open Function OrderDual Set

/-!
### Definitions
-/


/-- A function `f` between preorders is left order continuous if it preserves all suprema of
nonempty sets. We define it using `IsLUB` instead of `sSup` so that the proof works both for
complete lattices and conditionally complete lattices. -/
@[to_dual
/-- A function `f` between preorders is right order continuous if it preserves all infima of
nonempty sets.  We define it using `IsGLB` instead of `sInf` so that the proof works both for
complete lattices and conditionally complete lattices. -/]
/-
**LeftOrdContinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LeftOrdContinuous [Preorder α] [Preorder β] (f : α -> β)
参数：f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def LeftOrdContinuous [Preorder α] [Preorder β] (f : α → β) :=
  ∀ ⦃s : Set α⦄ ⦃x⦄, s.Nonempty → IsLUB s x → IsLUB (f '' s) (f x)

namespace LeftOrdContinuous

section Preorder

variable (α) [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β}

@[to_dual]
/-
**LeftOrdContinuous.id** 是 Mathlib 中的一个定理，位于命名空间 `LeftOrdContinuous`。
形式化陈述：∀ (α : Type u) [inst : Preorder α], LeftOrdContinuous id
参数：α : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
protected theorem id : LeftOrdContinuous (id : α → α) := fun s _ x h => by
  simpa only [image_id] using! h

variable {α}

@[to_dual]
/-
**LeftOrdContinuous.dual** 是 Mathlib 中的一个定理，位于命名空间 `LeftOrdContinuous`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f :
 α → β},   LeftOrdContinuous f → RightOrdContinuous (⇑OrderDual.toDual ∘ f ∘ ⇑Or
derDual.ofDual)
参数：⇑OrderDual.toDual ∘ f ∘ ⇑OrderDual.ofDual。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem dual :
    LeftOrdContinuous f → RightOrdContinuous (toDual ∘ f ∘ ofDual) :=
  id

@[deprecated (since := "2026-04-08")] alias rightOrdContinuous_dual := LeftOrdContinuous.dual

@[deprecated (since := "2026-04-08")] alias _root_.RightOrdContinuous.orderDual :=
  RightOrdContinuous.dual

@[to_dual]
/-
**LeftOrdContinuous.map_isGreatest** 是 Mathlib 中的一个定理，位于命名空间 `LeftOrdContinuous`
。
形式化陈述：map_isGreatest (hf : LeftOrdContinuous f) {s : Set α} {x : α} (h : IsGreat
est s x) : IsGreatest (f '' s) (f x)
参数：hf : LeftOrdContinuous f；h : IsGreatest s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
-/
theorem map_isGreatest (hf : LeftOrdContinuous f) {s : Set α} {x : α} (h : IsGreatest s x) :
    IsGreatest (f '' s) (f x) :=
  ⟨mem_image_of_mem f h.1, (hf ⟨x, h.1⟩ h.isLUB).1⟩

@[to_dual]
/-
**LeftOrdContinuous.mono** 是 Mathlib 中的一个定理，位于命名空间 `LeftOrdContinuous`。
形式化陈述：mono (hf : LeftOrdContinuous f) : Monotone f
参数：hf : LeftOrdContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `upperBounds_insert`：upperBounds_insert (a : α) (s : Set α) : upperBounds
 (insert a s) = Ici a inter upperBounds s
· 使用定理 `upperBounds_singleton`：upperBounds_singleton : upperBounds {a} = Ici a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LeftOrdContinuous.map_isGreatest`：map_isGreatest (hf : LeftOrdContinuous
 f) {s : Set α} {x : α} (h : IsGreatest s x) : IsGreatest (f '' s) (f x)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem mono (hf : LeftOrdContinuous f) : Monotone f := fun a₁ a₂ h =>
  have : IsGreatest {a₁, a₂} a₂ := ⟨Or.inr rfl, by simp [*]⟩
  (hf.map_isGreatest this).2 <| mem_image_of_mem _ (Or.inl rfl)

@[to_dual]
/-
**LeftOrdContinuous.comp** 是 Mathlib 中的一个定理，位于命名空间 `LeftOrdContinuous`。
形式化陈述：comp (hg : LeftOrdContinuous g) (hf : LeftOrdContinuous f) : LeftOrdContin
uous (g ∘ f)
参数：hg : LeftOrdContinuous g；hf : LeftOrdContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
-/
theorem comp (hg : LeftOrdContinuous g) (hf : LeftOrdContinuous f) : LeftOrdContinuous (g ∘ f) :=
  fun s x hs h => by simpa only [image_image] using! hg (.image _ hs) (hf hs h)

@[to_dual]
/-
**LeftOrdContinuous.iterate** 是 Mathlib 中的一个定理，位于命名空间 `LeftOrdContinuous`。
形式化陈述：∀ {α : Type u} [inst : Preorder α] {f : α → α}, LeftOrdContinuous f → ∀ (n
 : ℕ), LeftOrdContinuous f^[n]
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem iterate {f : α → α} (hf : LeftOrdContinuous f) (n : ℕ) :
    LeftOrdContinuous f^[n] :=
  match n with
  | 0 => LeftOrdContinuous.id α
  | (n + 1) => (LeftOrdContinuous.iterate hf n).comp hf

end Preorder

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β] {f : α → β}

@[to_dual]
/-
**LeftOrdContinuous.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `LeftOrdContinuous`。
形式化陈述：map_sup (hf : LeftOrdContinuous f) (x y : α) : f (x ⊔ y) = f x ⊔ f y
参数：hf : LeftOrdContinuous f；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `Set.insert_nonempty`：insert_nonempty (a : α) (s : Set α) : (insert a s).
Nonempty
· 使用定理 `isLUB_pair`：isLUB_pair [SemilatticeSup γ] {a b : γ} : IsLUB {a, b} (a ⊔ 
b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_pair`：image_pair (f : α -> β) (a b : α) : f '' {a, b} = {f a, 
f b}
-/
theorem map_sup (hf : LeftOrdContinuous f) (x y : α) : f (x ⊔ y) = f x ⊔ f y :=
  (hf (insert_nonempty ..) isLUB_pair).unique <| by simp only [image_pair, isLUB_pair]

@[to_dual]
/-
**LeftOrdContinuous.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `LeftOrdContinuous`。
形式化陈述：le_iff (hf : LeftOrdContinuous f) (h : Injective f) {x y} : f x <= f y ↔ x
 <= y
参数：hf : LeftOrdContinuous f；h : Injective f。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LeftOrdContinuous.map_sup`：map_sup (hf : LeftOrdContinuous f) (x y : α) 
: f (x ⊔ y) = f x ⊔ f y
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_iff (hf : LeftOrdContinuous f) (h : Injective f) {x y} : f x ≤ f y ↔ x ≤ y := by
  simp only [← sup_eq_right, ← hf.map_sup, h.eq_iff]

@[to_dual]
/-
**LeftOrdContinuous.lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `LeftOrdContinuous`。
形式化陈述：lt_iff (hf : LeftOrdContinuous f) (h : Injective f) {x y} : f x < f y ↔ x 
< y
参数：hf : LeftOrdContinuous f；h : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LeftOrdContinuous.le_iff`：le_iff (hf : LeftOrdContinuous f) (h : Injecti
ve f) {x y} : f x <= f y ↔ x <= y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_iff (hf : LeftOrdContinuous f) (h : Injective f) {x y} : f x < f y ↔ x < y := by
  simp only [lt_iff_le_not_ge, hf.le_iff h]

variable (f)

/-- Convert an injective left order continuous function to an order embedding. -/
@[to_dual
/-- Convert an injective right order continuous function to an order embedding. -/]
/-
**LeftOrdContinuous.toOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `LeftOrdContinuou
s`。
形式化陈述：toOrderEmbedding (hf : LeftOrdContinuous f) (h : Injective f) : α ↪o β
参数：hf : LeftOrdContinuous f；h : Injective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LeftOrdContinuous.le_iff`：le_iff (hf : LeftOrdContinuous f) (h : Injecti
ve f) {x y} : f x <= f y ↔ x <= y
-/
def toOrderEmbedding (hf : LeftOrdContinuous f) (h : Injective f) : α ↪o β :=
  ⟨⟨f, h⟩, hf.le_iff h⟩

variable {f}

@[to_dual (attr := simp)]
/-
**LeftOrdContinuous.coe_toOrderEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `LeftOrdConti
nuous`。
形式化陈述：coe_toOrderEmbedding (hf : LeftOrdContinuous f) (h : Injective f) : ⇑(hf.t
oOrderEmbedding f h) = f
参数：hf : LeftOrdContinuous f；h : Injective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toOrderEmbedding (hf : LeftOrdContinuous f) (h : Injective f) :
    ⇑(hf.toOrderEmbedding f h) = f :=
  rfl

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] {f : α → β}

@[to_dual]
/-
**LeftOrdContinuous.map_sSup'** 是 Mathlib 中的一个定理，位于命名空间 `LeftOrdContinuous`。
形式化陈述：map_sSup' (hf : LeftOrdContinuous f) {s : Set α} (hs : s.Nonempty) : f (sS
up s) = sSup (f '' s)
参数：hf : LeftOrdContinuous f；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
-/
theorem map_sSup' (hf : LeftOrdContinuous f) {s : Set α} (hs : s.Nonempty) :
    f (sSup s) = sSup (f '' s) :=
  (hf hs <| isLUB_sSup s).sSup_eq.symm

@[to_dual]
/-
**LeftOrdContinuous.map_sSup** 是 Mathlib 中的一个定理，位于命名空间 `LeftOrdContinuous`。
形式化陈述：map_sSup (hf : LeftOrdContinuous f) {s : Set α} (hs : s.Nonempty) : f (sSu
p s) = ⨆ x in s, f x
参数：hf : LeftOrdContinuous f；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LeftOrdContinuous.map_sSup'`：map_sSup' (hf : LeftOrdContinuous f) {s : S
et α} (hs : s.Nonempty) : f (sSup s) = sSup (f '' s)
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
-/
theorem map_sSup (hf : LeftOrdContinuous f) {s : Set α} (hs : s.Nonempty) :
    f (sSup s) = ⨆ x ∈ s, f x := by
  rw [hf.map_sSup' hs, sSup_image]

@[to_dual]
/-
**LeftOrdContinuous.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `LeftOrdContinuous`。
形式化陈述：map_iSup (hf : LeftOrdContinuous f) [Nonempty ι] (g : ι -> α) : f (⨆ i, g 
i) = ⨆ i, f (g i)
参数：hf : LeftOrdContinuous f；g : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LeftOrdContinuous.map_sSup'`：map_sSup' (hf : LeftOrdContinuous f) {s : S
et α} (hs : s.Nonempty) : f (sSup s) = sSup (f '' s)
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
theorem map_iSup (hf : LeftOrdContinuous f) [Nonempty ι] (g : ι → α) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  simp only [iSup, hf.map_sSup' (range_nonempty g), ← range_comp]
  rfl

end CompleteLattice

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {f : α → β}

@[to_dual]
/-
**LeftOrdContinuous.map_csSup** 是 Mathlib 中的一个定理，位于命名空间 `LeftOrdContinuous`。
形式化陈述：map_csSup (hf : LeftOrdContinuous f) {s : Set α} (sne : s.Nonempty) (sbdd 
: BddAbove s) : f (sSup s) = sSup (f '' s)
参数：hf : LeftOrdContinuous f；sne : s.Nonempty；sbdd : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
-/
theorem map_csSup (hf : LeftOrdContinuous f) {s : Set α} (sne : s.Nonempty) (sbdd : BddAbove s) :
    f (sSup s) = sSup (f '' s) :=
  ((hf sne <| isLUB_csSup sne sbdd).csSup_eq <| sne.image f).symm

@[to_dual]
/-
**LeftOrdContinuous.map_ciSup** 是 Mathlib 中的一个定理，位于命名空间 `LeftOrdContinuous`。
形式化陈述：map_ciSup (hf : LeftOrdContinuous f) {g : ι -> α} (hg : BddAbove (range g)
) : f (⨆ i, g i) = ⨆ i, f (g i)
参数：hf : LeftOrdContinuous f；hg : BddAbove (range g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LeftOrdContinuous.map_csSup`：map_csSup (hf : LeftOrdContinuous f) {s : S
et α} (sne : s.Nonempty) (sbdd : BddAbove s) : f (sSup s) = sSup (f '' s)
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
theorem map_ciSup (hf : LeftOrdContinuous f) {g : ι → α} (hg : BddAbove (range g)) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  simp only [iSup, hf.map_csSup (range_nonempty _) hg, ← range_comp]
  rfl

end ConditionallyCompleteLattice

end LeftOrdContinuous

namespace GaloisConnection
variable [Preorder α] [Preorder β] {f : α → β} {g : β → α}

/-- A left adjoint in a Galois connection is left-continuous in the order-theoretic sense. -/
/-
**GaloisConnection.leftOrdContinuous** 是 Mathlib 中的一个引理，位于命名空间 `GaloisConnection
`。
形式化陈述：leftOrdContinuous (gc : GaloisConnection f g) : LeftOrdContinuous f
参数：gc : GaloisConnection f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.isLUB_l_image`：isLUB_l_image {s : Set α} {a : α} (h : I
sLUB s a) : IsLUB (l '' s) (l a)

--- 原说明 ---
A left adjoint in a Galois connection is left-continuous in the order-theoretic 
sense.
-/
lemma leftOrdContinuous (gc : GaloisConnection f g) : LeftOrdContinuous f :=
  fun _ _ _ ↦ gc.isLUB_l_image

/-- A right adjoint in a Galois connection is right-continuous in the order-theoretic sense. -/
/-
**GaloisConnection.rightOrdContinuous** 是 Mathlib 中的一个引理，位于命名空间 `GaloisConnectio
n`。
形式化陈述：rightOrdContinuous (gc : GaloisConnection f g) : RightOrdContinuous g
参数：gc : GaloisConnection f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.isGLB_u_image`：∀ {α : Type u} {β : Type v} [inst : Preo
rder α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → 
∀ {s : Set α} {a : α…

--- 原说明 ---
A right adjoint in a Galois connection is right-continuous in the order-theoreti
c sense.
-/
lemma rightOrdContinuous (gc : GaloisConnection f g) : RightOrdContinuous g :=
  fun _ _ _ ↦ gc.isGLB_u_image

end GaloisConnection

namespace OrderIso
variable [Preorder α] [Preorder β] (e : α ≃o β)

/-
**OrderIso.leftOrdContinuous** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] (e :
 α ≃o β), LeftOrdContinuous ⇑e
参数：e : α ≃o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `GaloisConnection.leftOrdContinuous`：leftOrdContinuous (gc : GaloisConnec
tion f g) : LeftOrdContinuous f
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
protected lemma leftOrdContinuous : LeftOrdContinuous e := e.to_galoisConnection.leftOrdContinuous

@[to_dual existing]
/-
**OrderIso.rightOrdContinuous** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] (e :
 α ≃o β), RightOrdContinuous ⇑e
参数：e : α ≃o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `GaloisConnection.rightOrdContinuous`：rightOrdContinuous (gc : GaloisConn
ection f g) : RightOrdContinuous g
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
protected lemma rightOrdContinuous : RightOrdContinuous e :=
  e.symm.to_galoisConnection.rightOrdContinuous

end OrderIso

