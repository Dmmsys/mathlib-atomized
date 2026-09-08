/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Anatole Dedecker
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Saddle points of a map

* `IsSaddlePointOn`.
  Let `f : E × F → β` be a map, where `β` is preordered.
  A pair `(a,b)` in `E × F` is a *saddle point* of `f` on `X × Y`
  if `f a y ≤ f x b` for all `x ∈ X` and all `y` in `Y`.

* `isSaddlePointOn_iff`: if `β` is a complete linear order,
  then `(a, b) ∈ X × Y` is a saddle point on `X × Y` iff
  `⨆ y ∈ Y, f a y = ⨅ x ∈ X, f x b = f a b`.

-/

@[expose] public section

open Set

section SaddlePoint

variable {E F : Type*} {β : Type*}
variable (X : Set E) (Y : Set F) (f : E → F → β)

/-- The trivial minimax inequality -/
/-
**iSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSup [SupSet α] (s : ι -> α) : α
参数：s : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial minimax inequality
-/
theorem iSup₂_iInf₂_le_iInf₂_iSup₂ [CompleteLinearOrder β] :
    ⨆ y ∈ Y, ⨅ x ∈ X, f x y ≤ ⨅ x ∈ X, ⨆ y ∈ Y, f x y := by
  rw [iSup₂_le_iff]; intro y hy
  rw [le_iInf₂_iff]; intro x hx
  exact iInf₂_le_of_le x hx (le_iSup₂_of_le y hy (le_refl _))

-- [Hiriart-Urruty, (4.1.4)]
/-- The pair `(a, b)` is a saddle point of `f` on `X × Y`
if `f a y ≤ f x b` for all `x ∈ X` and all `y` in `Y`.

Note: we do not require that `a ∈ X` and `b ∈ Y`. -/
/-
**IsSaddlePointOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsSaddlePointOn [Preorder β] (a : E) (b : F) : Prop
参数：a : E；b : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pair `(a, b)` is a saddle point of `f` on `X × Y`
if `f a y ≤ f x b` for all `x ∈ X` and all `y` in `Y`.

Note: we do not require that `a ∈ X` and `b ∈ Y`.
-/
def IsSaddlePointOn [Preorder β] (a : E) (b : F) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, f a y ≤ f x b

variable {X Y f}
/-
**IsSaddlePointOn.swap_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSaddlePointOn.swap_left [Preorder β] {a a' : E} {b b' : F} (ha' : a' in 
X) (hb : b in Y) (h : IsSaddlePointOn X Y f a b) (h' : IsSaddlePointOn X Y f a' 
b') : IsSaddlePointOn X Y f a b'
参数：ha' : a' in X；hb : b in Y；h : IsSaddlePointOn X Y f a b；h' : IsSaddlePointOn 
X Y f a' b'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
lemma IsSaddlePointOn.swap_left [Preorder β] {a a' : E} {b b' : F} (ha' : a' ∈ X) (hb : b ∈ Y)
    (h : IsSaddlePointOn X Y f a b) (h' : IsSaddlePointOn X Y f a' b') :
    IsSaddlePointOn X Y f a b' := fun x hx y hy ↦
  le_trans (h a' ha' y hy) (h' x hx b hb)
/-
**IsSaddlePointOn.swap_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSaddlePointOn.swap_right [Preorder β] {a a' : E} {b b' : F} (ha : a in X
) (hb' : b' in Y) (h : IsSaddlePointOn X Y f a b) (h' : IsSaddlePointOn X Y f a'
 b') : IsSaddlePointOn X Y f a' b
参数：ha : a in X；hb' : b' in Y；h : IsSaddlePointOn X Y f a b；h' : IsSaddlePointOn 
X Y f a' b'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSaddlePointOn.swap_left`：IsSaddlePointOn.swap_left [Preorder β] {a a' 
: E} {b b' : F} (ha' : a' in X) (hb : b in Y) (h : IsSaddlePointOn X Y f a b) (h
' : IsSaddlePoi…
-/
lemma IsSaddlePointOn.swap_right [Preorder β] {a a' : E} {b b' : F} (ha : a ∈ X) (hb' : b' ∈ Y)
    (h : IsSaddlePointOn X Y f a b) (h' : IsSaddlePointOn X Y f a' b') :
    IsSaddlePointOn X Y f a' b :=
  IsSaddlePointOn.swap_left ha hb' h' h

-- [Hiriart-Urruty, (4.1.1)]
/-
**isSaddlePointOn_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSaddlePointOn_iff [CompleteLinearOrder β] {a : E} (ha : a in X) {b : F} 
(hb : b in Y) : IsSaddlePointOn X Y f a b ↔ ⨆ y in Y, f a y = f a b ∧ ⨅ x in X, 
f x b = f a b
参数：ha : a in X；hb : b in Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isSaddlePointOn_iff [CompleteLinearOrder β]
    {a : E} (ha : a ∈ X) {b : F} (hb : b ∈ Y) :
    IsSaddlePointOn X Y f a b ↔
      ⨆ y ∈ Y, f a y = f a b ∧ ⨅ x ∈ X, f x b = f a b := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h, h'⟩ x hx y hy ↦ ?_⟩
  · apply le_antisymm
    · simp only [iSup_le_iff]
      exact h a ha
    · apply le_iSup₂ b hb
  · apply le_antisymm
    · apply iInf₂_le a ha
    · simp only [le_iInf_iff]
      intro x hx
      exact h x hx b hb
  · trans f a b
    · -- f a y ≤ f a b
      rw [← h]
      apply le_iSup₂ y hy
    · -- f a b ≤ f x b
      rw [← h']
      apply iInf₂_le x hx

-- [Hiriart-Urruty, Prop. 4.2.2]
/-
**isSaddlePointOn_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSaddlePointOn_iff' [CompleteLinearOrder β] {a : E} (ha : a in X) {b : F}
 (hb : b in Y) : IsSaddlePointOn X Y f a b ↔ ⨆ y in Y, f a y <= ⨅ x in X, f x b
参数：ha : a in X；hb : b in Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isSaddlePointOn_iff`：isSaddlePointOn_iff [CompleteLinearOrder β] {a : E}
 (ha : a in X) {b : F} (hb : b in Y) : IsSaddlePointOn X Y f a b ↔ ⨆ y in Y, f a
 y = f a …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
-/
lemma isSaddlePointOn_iff' [CompleteLinearOrder β]
    {a : E} (ha : a ∈ X) {b : F} (hb : b ∈ Y) :
    IsSaddlePointOn X Y f a b ↔
      ⨆ y ∈ Y, f a y ≤ ⨅ x ∈ X, f x b := by
  rw [isSaddlePointOn_iff ha hb]
  refine ⟨fun ⟨h, h'⟩ ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · exact le_trans (le_of_eq h) (le_of_eq h'.symm)
  · apply le_antisymm
    · exact le_trans h (iInf₂_le a ha)
    · apply le_iSup₂ b hb
  · apply le_antisymm
    · apply iInf₂_le a ha
    · apply le_trans (le_iSup₂ b hb) h

-- [Hiriart-Urruty, Prop. 4.2.2]
-- The converse doesn't seem to hold
/-- Minimax formulation of saddle points -/
/-
**isSaddlePointOn_value** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSaddlePointOn_value [CompleteLinearOrder β] {a : E} (ha : a in X) {b : F
} (hb : b in Y) (h : IsSaddlePointOn X Y f a b) : ⨅ x in X, ⨆ y in Y, f x y = f 
a b ∧ ⨆ y in Y, ⨅ x in X, f x y = f a b
参数：ha : a in X；hb : b in Y；h : IsSaddlePointOn X Y f a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `isSaddlePointOn_iff`：isSaddlePointOn_iff [CompleteLinearOrder β] {a : E}
 (ha : a in X) {b : F} (hb : b in Y) : IsSaddlePointOn X Y f a b ↔ ⨆ y in Y, f a
 y = f a …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `iInf₂_mono`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : C
ompleteLattice α] {f g : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), g i j ≤ f i
…
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `iSup₂_mono`：iSup₂_mono {f g : forall i, κ i -> α} (h : forall i j, f i j
 <= g i j) : ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j

--- 原说明 ---
Minimax formulation of saddle points
-/
lemma isSaddlePointOn_value [CompleteLinearOrder β]
    {a : E} (ha : a ∈ X) {b : F} (hb : b ∈ Y)
    (h : IsSaddlePointOn X Y f a b) :
    ⨅ x ∈ X, ⨆ y ∈ Y, f x y = f a b ∧
      ⨆ y ∈ Y, ⨅ x ∈ X, f x y = f a b := by
  rw [isSaddlePointOn_iff ha hb] at h
  constructor
  · apply le_antisymm
    · rw [← h.1]
      exact le_trans (iInf₂_le a ha) (le_rfl)
    · rw [← h.2]
      apply iInf₂_mono
      intro x _
      apply le_iSup₂ b hb
  · apply le_antisymm
    · rw [← h.1]
      apply iSup₂_mono
      intro y _
      apply iInf₂_le a ha
    · rw [← h.2]
      apply le_trans (le_rfl) (le_iSup₂ b hb)

end SaddlePoint

