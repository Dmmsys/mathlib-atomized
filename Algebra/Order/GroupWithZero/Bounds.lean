/-
Copyright (c) 2025 María Inés de Frutos-Fernández . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Bounds.Image

/-!
# Lemmas about `BddAbove`
-/

public section

open Set

/-- A variant of `BddAbove.range_comp_left` that assumes that `f` is nonnegative and `g` is monotone
on nonnegative values. -/
/-
**BddAbove.range_comp_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddAbove.range_comp_of_nonneg {α β γ : Type*} [Nonempty α] [Preorder β] [Z
ero β] [Preorder γ] {f : α -> β} {g : β -> γ} (hf : BddAbove (range f)) (hf0 : 0
 <= f) (hg : MonotoneOn g {x : β | 0 <= x}) : BddAbove (range (fun x => g (f x))
)
参数：hf : BddAbove (range f)；hf0 : 0 <= f；hg : MonotoneOn g {x : β | 0 <= x}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.map_bddAbove`：map_bddAbove (Hf : MonotoneOn f t) (Hst : s sub
seteq t) : (upperBounds s inter t).Nonempty -> BddAbove (f '' s)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f

--- 原说明 ---
A variant of `BddAbove.range_comp_left` that assumes that `f` is nonnegative and
 `g` is monotone
on nonnegative values.
-/
lemma BddAbove.range_comp_of_nonneg {α β γ : Type*} [Nonempty α] [Preorder β] [Zero β] [Preorder γ]
    {f : α → β} {g : β → γ} (hf : BddAbove (range f)) (hf0 : 0 ≤ f)
    (hg : MonotoneOn g {x : β | 0 ≤ x}) : BddAbove (range (fun x => g (f x))) := by
  suffices hg' : BddAbove (g '' range f) by
    rwa [← Function.comp_def, Set.range_comp]
  apply hg.map_bddAbove (by rintro x ⟨a, rfl⟩; exact hf0 a)
  obtain ⟨b, hb⟩ := hf
  use b, hb
  simp only [mem_upperBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hb
  exact le_trans (hf0 Classical.ofNonempty) (hb Classical.ofNonempty)

/-- If `u v : α → β` are nonnegative and bounded above, then `u * v` is bounded above. -/
/-
**bddAbove_range_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddAbove_range_mul {α β : Type*} [Nonempty α] {u v : α -> β} [Preorder β] 
[Zero β] [Mul β] [PosMulMono β] [MulPosMono β] (hu : BddAbove (Set.range u)) (hu
0 : 0 <= u) (hv : BddAbove (Set.range v)) (hv0 : 0 <= v) : BddAbove (Set.range (
u * v))
参数：hu : BddAbove (Set.range u)；hu0 : 0 <= u；hv : BddAbove (Set.range v)；hv0 : 0 
<= v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `BddAbove.range_comp_of_nonneg`：BddAbove.range_comp_of_nonneg {α β γ : Ty
pe*} [Nonempty α] [Preorder β] [Zero β] [Preorder γ] {f : α -> β} {g : β -> γ} (
hf : BddAbove (rang…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `bddAbove_range_prod`：bddAbove_range_prod {F : ι -> α × β} : BddAbove (ra
nge F) ↔ BddAbove (range <| Prod.fst ∘ F) ∧ BddAbove (range <| Prod.snd ∘ F)
· 使用引理 `MonotoneOn.mul`：MonotoneOn.mul [PosMulMono M₀] [MulPosMono M₀] {s : Set 
α} (hf : MonotoneOn f s) (hg : MonotoneOn g s) (hf₀ : forall x in s, 0 <= f x) (
hg₀ …
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `monotone_fst`：monotone_fst : Monotone (@Prod.fst α β)
· 使用定理 `monotone_snd`：monotone_snd : Monotone (@Prod.snd α β)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `u v : α → β` are nonnegative and bounded above, then `u * v` is bounded abov
e.
-/
theorem bddAbove_range_mul {α β : Type*} [Nonempty α] {u v : α → β} [Preorder β] [Zero β] [Mul β]
    [PosMulMono β] [MulPosMono β] (hu : BddAbove (Set.range u)) (hu0 : 0 ≤ u)
    (hv : BddAbove (Set.range v)) (hv0 : 0 ≤ v) : BddAbove (Set.range (u * v)) :=
  letI : Zero (β × β) := ⟨(0, 0)⟩
  BddAbove.range_comp_of_nonneg (f := fun i ↦ (u i, v i)) (g := fun x ↦ x.1 * x.2)
    (bddAbove_range_prod.mpr ⟨hu, hv⟩) (fun x ↦ ⟨hu0 x, hv0 x⟩) ((monotone_fst.monotoneOn _).mul
      (monotone_snd.monotoneOn _) (fun _ hx ↦ hx.1) (fun _ hx ↦ hx.2))
