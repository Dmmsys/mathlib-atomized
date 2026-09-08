/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Upper/lower bounds in ordered monoids and groups

In this file we prove a few facts like “`-s` is bounded above iff `s` is bounded below”
(`bddAbove_neg`).
-/

public section

open Function Set
open scoped Pointwise

variable {ι G M : Type*}

section Mul
variable [Mul M] [Preorder M] [MulLeftMono M]
  [MulRightMono M] {f g : ι → M} {s t : Set M} {a b : M}

@[to_additive]
/-
**mul_mem_upperBounds_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_mem_upperBounds_mul (ha : a in upperBounds s) (hb : b in upperBounds t
) : a * b in upperBounds (s * t)
参数：ha : a in upperBounds s；hb : b in upperBounds t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.forall_mem_image2`：forall_mem_image2 {p : γ -> Prop} : (forall z in 
image2 f s t, p z) ↔ forall x in s, forall y in t, p (f x y)
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
-/
lemma mul_mem_upperBounds_mul (ha : a ∈ upperBounds s) (hb : b ∈ upperBounds t) :
    a * b ∈ upperBounds (s * t) := forall_mem_image2.2 fun _ hx _ hy => mul_le_mul' (ha hx) (hb hy)

@[to_additive]
/-
**subset_upperBounds_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：subset_upperBounds_mul (s t : Set M) : upperBounds s * upperBounds t subse
teq upperBounds (s * t)
参数：s t : Set M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
· 使用引理 `mul_mem_upperBounds_mul`：mul_mem_upperBounds_mul (ha : a in upperBounds 
s) (hb : b in upperBounds t) : a * b in upperBounds (s * t)
-/
lemma subset_upperBounds_mul (s t : Set M) : upperBounds s * upperBounds t ⊆ upperBounds (s * t) :=
  image2_subset_iff.2 fun _ hx _ hy => mul_mem_upperBounds_mul hx hy

@[to_additive]
/-
**mul_mem_lowerBounds_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_mem_lowerBounds_mul (ha : a in lowerBounds s) (hb : b in lowerBounds t
) : a * b in lowerBounds (s * t)
参数：ha : a in lowerBounds s；hb : b in lowerBounds t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_mem_upperBounds_mul`：mul_mem_upperBounds_mul (ha : a in upperBounds 
s) (hb : b in upperBounds t) : a * b in upperBounds (s * t)
-/
lemma mul_mem_lowerBounds_mul (ha : a ∈ lowerBounds s) (hb : b ∈ lowerBounds t) :
    a * b ∈ lowerBounds (s * t) := mul_mem_upperBounds_mul (M := Mᵒᵈ) ha hb

@[to_additive]
/-
**subset_lowerBounds_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：subset_lowerBounds_mul (s t : Set M) : lowerBounds s * lowerBounds t subse
teq lowerBounds (s * t)
参数：s t : Set M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `subset_upperBounds_mul`：subset_upperBounds_mul (s t : Set M) : upperBoun
ds s * upperBounds t subseteq upperBounds (s * t)
-/
lemma subset_lowerBounds_mul (s t : Set M) : lowerBounds s * lowerBounds t ⊆ lowerBounds (s * t) :=
  subset_upperBounds_mul (M := Mᵒᵈ) _ _

@[to_additive]
/-
**BddAbove.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddAbove.mul (hs : BddAbove s) (ht : BddAbove t) : BddAbove (s * t)
参数：hs : BddAbove s；ht : BddAbove t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用引理 `subset_upperBounds_mul`：subset_upperBounds_mul (s t : Set M) : upperBoun
ds s * upperBounds t subseteq upperBounds (s * t)
· 使用定理 `Set.Nonempty.mul`：∀ {α : Type u_2} [inst : Mul α] {s t : Set α}, s.Nonem
pty → t.Nonempty → (s * t).Nonempty
-/
lemma BddAbove.mul (hs : BddAbove s) (ht : BddAbove t) : BddAbove (s * t) :=
  (Nonempty.mul hs ht).mono (subset_upperBounds_mul s t)

@[to_additive]
/-
**BddBelow.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddBelow.mul (hs : BddBelow s) (ht : BddBelow t) : BddBelow (s * t)
参数：hs : BddBelow s；ht : BddBelow t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用引理 `subset_lowerBounds_mul`：subset_lowerBounds_mul (s t : Set M) : lowerBoun
ds s * lowerBounds t subseteq lowerBounds (s * t)
· 使用定理 `Set.Nonempty.mul`：∀ {α : Type u_2} [inst : Mul α] {s t : Set α}, s.Nonem
pty → t.Nonempty → (s * t).Nonempty
-/
lemma BddBelow.mul (hs : BddBelow s) (ht : BddBelow t) : BddBelow (s * t) :=
  (Nonempty.mul hs ht).mono (subset_lowerBounds_mul s t)

@[to_additive] alias Set.BddAbove.mul := BddAbove.mul

@[to_additive]
/-
**BddAbove.range_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddAbove.range_mul (hf : BddAbove (range f)) (hg : BddAbove (range g)) : B
ddAbove (range fun i => f i * g i)
参数：hf : BddAbove (range f)；hg : BddAbove (range g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `BddAbove.range_comp_left`：BddAbove.range_comp_left {γ : Type*} [Preorder
 β] [Preorder γ] {f : α -> β} {g : β -> γ} (hf : BddAbove (range f)) (hg : Monot
one g) : BddAb…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `bddAbove_range_prod`：bddAbove_range_prod {F : ι -> α × β} : BddAbove (ra
nge F) ↔ BddAbove (range <| Prod.fst ∘ F) ∧ BddAbove (range <| Prod.snd ∘ F)
· 使用定理 `Monotone.mul'`：Monotone.mul' [MulLeftMono α] [MulRightMono α] (hf : Mono
tone f) (hg : Monotone g) : Monotone fun x => f x * g x
· 使用定理 `monotone_fst`：monotone_fst : Monotone (@Prod.fst α β)
· 使用定理 `monotone_snd`：monotone_snd : Monotone (@Prod.snd α β)
-/
lemma BddAbove.range_mul (hf : BddAbove (range f)) (hg : BddAbove (range g)) :
    BddAbove (range fun i ↦ f i * g i) :=
  .range_comp_left (f := fun i ↦ (f i, g i)) (bddAbove_range_prod.2 ⟨hf, hg⟩)
    (monotone_fst.mul' monotone_snd)

@[to_additive]
/-
**BddBelow.range_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddBelow.range_mul (hf : BddBelow (range f)) (hg : BddBelow (range g)) : B
ddBelow (range fun i => f i * g i)
参数：hf : BddBelow (range f)；hg : BddBelow (range g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `BddAbove.range_mul`：BddAbove.range_mul (hf : BddAbove (range f)) (hg : B
ddAbove (range g)) : BddAbove (range fun i => f i * g i)
-/
lemma BddBelow.range_mul (hf : BddBelow (range f)) (hg : BddBelow (range g)) :
    BddBelow (range fun i ↦ f i * g i) := BddAbove.range_mul (M := Mᵒᵈ) hf hg

end Mul

section Group
variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

@[to_additive (attr := simp)]
/-
**bddAbove_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddAbove_inv : BddAbove s⁻¹ ↔ BddBelow s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.bddAbove_preimage`：bddAbove_preimage (e : α ≃o β) {s : Set β} :
 BddAbove (e ⁻¹' s) ↔ BddAbove s
-/
theorem bddAbove_inv : BddAbove s⁻¹ ↔ BddBelow s :=
  (OrderIso.inv G).bddAbove_preimage

@[to_additive (attr := simp)]
/-
**bddBelow_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddBelow_inv : BddBelow s⁻¹ ↔ BddAbove s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.bddBelow_preimage`：∀ {α : Type u} {β : Type v} [inst : Preorder
 α] [inst_1 : Preorder β] (e : α ≃o β) {s : Set β},   BddBelow (⇑e ⁻¹' s) ↔ BddB
elow s
-/
theorem bddBelow_inv : BddBelow s⁻¹ ↔ BddAbove s :=
  (OrderIso.inv G).bddBelow_preimage

@[to_additive]
/-
**BddAbove.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddAbove.inv (h : BddAbove s) : BddBelow s⁻¹
参数：h : BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bddBelow_inv`：bddBelow_inv : BddBelow s⁻¹ ↔ BddAbove s
-/
theorem BddAbove.inv (h : BddAbove s) : BddBelow s⁻¹ :=
  bddBelow_inv.2 h

@[to_additive]
/-
**BddBelow.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddBelow.inv (h : BddBelow s) : BddAbove s⁻¹
参数：h : BddBelow s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bddAbove_inv`：bddAbove_inv : BddAbove s⁻¹ ↔ BddBelow s
-/
theorem BddBelow.inv (h : BddBelow s) : BddAbove s⁻¹ :=
  bddAbove_inv.2 h

@[to_additive (attr := simp)]
/-
**isLUB_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_inv : IsLUB s⁻¹ a ↔ IsGLB s a⁻¹
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isLUB_preimage`：isLUB_preimage {s : Set β} {x : α} : IsLUB (f ⁻
¹' s) x ↔ IsLUB s (f x)
-/
theorem isLUB_inv : IsLUB s⁻¹ a ↔ IsGLB s a⁻¹ :=
  (OrderIso.inv G).isLUB_preimage

@[to_additive]
/-
**isLUB_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_inv' : IsLUB s⁻¹ a⁻¹ ↔ IsGLB s a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isLUB_preimage'`：isLUB_preimage' {s : Set β} {x : β} : IsLUB (f
 ⁻¹' s) (f.symm x) ↔ IsLUB s x
-/
theorem isLUB_inv' : IsLUB s⁻¹ a⁻¹ ↔ IsGLB s a :=
  (OrderIso.inv G).isLUB_preimage'

@[to_additive]
/-
**IsGLB.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.inv (h : IsGLB s a) : IsLUB s⁻¹ a⁻¹
参数：h : IsGLB s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isLUB_inv'`：isLUB_inv' : IsLUB s⁻¹ a⁻¹ ↔ IsGLB s a
-/
theorem IsGLB.inv (h : IsGLB s a) : IsLUB s⁻¹ a⁻¹ :=
  isLUB_inv'.2 h

@[to_additive (attr := simp)]
/-
**isGLB_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_inv : IsGLB s⁻¹ a ↔ IsLUB s a⁻¹
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isGLB_preimage`：isGLB_preimage {s : Set β} {x : α} : IsGLB (f ⁻
¹' s) x ↔ IsGLB s (f x)
-/
theorem isGLB_inv : IsGLB s⁻¹ a ↔ IsLUB s a⁻¹ :=
  (OrderIso.inv G).isGLB_preimage

@[to_additive]
/-
**isGLB_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_inv' : IsGLB s⁻¹ a⁻¹ ↔ IsLUB s a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isGLB_preimage'`：isGLB_preimage' {s : Set β} {x : β} : IsGLB (f
 ⁻¹' s) (f.symm x) ↔ IsGLB s x
-/
theorem isGLB_inv' : IsGLB s⁻¹ a⁻¹ ↔ IsLUB s a :=
  (OrderIso.inv G).isGLB_preimage'

@[to_additive]
/-
**IsLUB.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.inv (h : IsLUB s a) : IsGLB s⁻¹ a⁻¹
参数：h : IsLUB s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isGLB_inv'`：isGLB_inv' : IsGLB s⁻¹ a⁻¹ ↔ IsLUB s a
-/
theorem IsLUB.inv (h : IsLUB s a) : IsGLB s⁻¹ a⁻¹ :=
  isGLB_inv'.2 h

@[to_additive]
/-
**BddBelow.range_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddBelow.range_inv {α : Type*} {f : α -> G} (hf : BddBelow (range f)) : Bd
dAbove (range (fun x => (f x)⁻¹))
参数：hf : BddBelow (range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddBelow.range_comp_left`：∀ {α : Type u} {β : Type v} {γ : Type u_1} [in
st : Preorder β] [inst_1 : Preorder γ] {f : α → β} {g : β → γ},   BddBelow (Set.
range f) → Mon…
· 使用定理 `OrderIso.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (e : α ≃o β), Monotone ⇑e
-/
lemma BddBelow.range_inv {α : Type*} {f : α → G} (hf : BddBelow (range f)) :
    BddAbove (range (fun x => (f x)⁻¹)) :=
  hf.range_comp_left (OrderIso.inv G).monotone

@[to_additive]
/-
**BddAbove.range_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddAbove.range_inv {α : Type*} {f : α -> G} (hf : BddAbove (range f)) : Bd
dBelow (range (fun x => (f x)⁻¹))
参数：hf : BddAbove (range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `BddBelow.range_inv`：BddBelow.range_inv {α : Type*} {f : α -> G} (hf : Bd
dBelow (range f)) : BddAbove (range (fun x => (f x)⁻¹))
-/
lemma BddAbove.range_inv {α : Type*} {f : α → G} (hf : BddAbove (range f)) :
    BddBelow (range (fun x => (f x)⁻¹)) :=
  BddBelow.range_inv (G := Gᵒᵈ) hf

@[to_additive]
/-
**IsLUB.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLUB.mul (hs : IsLUB s a) (ht : IsLUB t b) : IsLUB (s * t) (a * b)
参数：hs : IsLUB s a；ht : IsLUB t b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_image2_of_isLUB_isLUB`：isLUB_image2_of_isLUB_isLUB (h₁ : forall b,
 GaloisConnection (swap l b) (u₁ b)) (h₂ : forall a, GaloisConnection (l a) (u₂ 
a)) (ha₀ : IsLUB …
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
lemma IsLUB.mul (hs : IsLUB s a) (ht : IsLUB t b) :
    IsLUB (s * t) (a * b) :=
  isLUB_image2_of_isLUB_isLUB (fun _ => (OrderIso.mulRight _).to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).to_galoisConnection) hs ht

@[to_additive]
/-
**IsGLB.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGLB.mul (hs : IsGLB s a) (ht : IsGLB t b) : IsGLB (s * t) (a * b)
参数：hs : IsGLB s a；ht : IsGLB t b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLUB.mul`：IsLUB.mul (hs : IsLUB s a) (ht : IsLUB t b) : IsLUB (s * t) (
a * b)
-/
lemma IsGLB.mul (hs : IsGLB s a) (ht : IsGLB t b) :
    IsGLB (s * t) (a * b) :=
  IsLUB.mul (G := Gᵒᵈ) hs ht

@[to_additive]
/-
**IsLUB.div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLUB.div (hs : IsLUB s a) (ht : IsGLB t b) : IsLUB (s / t) (a / b)
参数：hs : IsLUB s a；ht : IsGLB t b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `IsLUB.mul`：IsLUB.mul (hs : IsLUB s a) (ht : IsLUB t b) : IsLUB (s * t) (
a * b)
· 使用定理 `IsGLB.inv`：IsGLB.inv (h : IsGLB s a) : IsLUB s⁻¹ a⁻¹
-/
lemma IsLUB.div (hs : IsLUB s a) (ht : IsGLB t b) :
    IsLUB (s / t) (a / b) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact hs.mul ht.inv

@[to_additive]
/-
**IsGLB.div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGLB.div (hs : IsGLB s a) (ht : IsLUB t b) : IsGLB (s / t) (a / b)
参数：hs : IsGLB s a；ht : IsLUB t b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLUB.div`：IsLUB.div (hs : IsLUB s a) (ht : IsGLB t b) : IsLUB (s / t) (
a / b)
-/
lemma IsGLB.div (hs : IsGLB s a) (ht : IsLUB t b) :
    IsGLB (s / t) (a / b) :=
  IsLUB.div (G := Gᵒᵈ) hs ht

end Group

