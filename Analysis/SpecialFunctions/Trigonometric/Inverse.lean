/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.ProjIcc

/-!
# Inverse trigonometric functions.

See also `Analysis.SpecialFunctions.Trigonometric.Arctan` for the inverse tan function.
(This is delayed as it is easier to set up after developing complex trigonometric functions.)

Basic inequalities on trigonometric functions.
-/

@[expose] public section


noncomputable section

open Topology Filter Set Filter Real

namespace Real
variable {x y : ℝ}

/-- Inverse of the `sin` function, returns values in the range `-π / 2 ≤ arcsin x ≤ π / 2`.
It defaults to `-π / 2` on `(-∞, -1)` and to `π / 2` to `(1, ∞)`. -/
@[pp_nodot]
/-
**Real.arcsin** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：arcsin : Real -> Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inverse of the `sin` function, returns values in the range `-π / 2 ≤ arcsin x ≤ 
π / 2`.
It defaults to `-π / 2` on `(-∞, -1)` and to `π / 2` to `(1, ∞)`.
-/
noncomputable def arcsin : ℝ → ℝ :=
  Subtype.val ∘ IccExtend (neg_le_self zero_le_one) sinOrderIso.symm
/-
**Real.arcsin_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_mem_Icc (x : Real) : arcsin x in Icc (-(π / 2)) (π / 2)
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem arcsin_mem_Icc (x : ℝ) : arcsin x ∈ Icc (-(π / 2)) (π / 2) :=
  Subtype.coe_prop _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Real.range_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：range_arcsin : range arcsin = Icc (-(π / 2)) (π / 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arcsin.eq_1`：Real.arcsin = Subtype.val ∘ Set.IccExtend Real.arcsin.
_proof_2 ⇑Real.sinOrderIso.symm
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.IccExtend_range`：IccExtend_range (f : Icc a b -> β) : range (IccExte
nd h f) = range f
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_arcsin : range arcsin = Icc (-(π / 2)) (π / 2) := by
  rw [arcsin, range_comp Subtype.val]
  ext
  simp
/-
**Real.arcsin_le_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_le_pi_div_two (x : Real) : arcsin x <= π / 2
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.arcsin_mem_Icc`：arcsin_mem_Icc (x : Real) : arcsin x in Icc (-(π / 
2)) (π / 2)
-/
theorem arcsin_le_pi_div_two (x : ℝ) : arcsin x ≤ π / 2 :=
  (arcsin_mem_Icc x).2
/-
**Real.neg_pi_div_two_le_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：neg_pi_div_two_le_arcsin (x : Real) : -(π / 2) <= arcsin x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.arcsin_mem_Icc`：arcsin_mem_Icc (x : Real) : arcsin x in Icc (-(π / 
2)) (π / 2)
-/
theorem neg_pi_div_two_le_arcsin (x : ℝ) : -(π / 2) ≤ arcsin x :=
  (arcsin_mem_Icc x).1
/-
**Real.arcsin_projIcc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_projIcc (x : Real) : arcsin (projIcc (-1) 1 (neg_le_self zero_le_on
e) x) = arcsin x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_le_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : Preorder α] [A
ddLeftMono α] {a : α}, 0 ≤ a → -a ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arcsin.eq_1`：Real.arcsin = Subtype.val ∘ Set.IccExtend Real.arcsin.
_proof_2 ⇑Real.sinOrderIso.symm
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Set.IccExtend_val`：IccExtend_val (f : Icc a b -> β) (x : Icc a b) : IccE
xtend h f x = f x
· 使用定理 `Set.IccExtend.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder 
α] {a b : α} (h : a ≤ b) (f : ↑(Set.Icc a b) → β),   Set.IccExtend h f = f ∘ Set
.projIcc…
-/
theorem arcsin_projIcc (x : ℝ) :
    arcsin (projIcc (-1) 1 (neg_le_self zero_le_one) x) = arcsin x := by
  rw [arcsin, Function.comp_apply, IccExtend_val, Function.comp_apply, IccExtend,
        Function.comp_apply]
/-
**Real.sin_arcsin'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sin_arcsin' {x : Real} (hx : x in Icc (-1 : Real) 1) : sin (arcsin x) = x
参数：hx : x in Icc (-1 : Real) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.IccExtend_of_mem`：IccExtend_of_mem (f : Icc a b -> β) (hx : x in Icc
 a b) : IccExtend h f x = f ⟨x, hx⟩
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
-/
theorem sin_arcsin' {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : sin (arcsin x) = x := by
  simpa [arcsin, IccExtend_of_mem _ _ hx, -OrderIso.apply_symm_apply] using
    Subtype.ext_iff.1 (sinOrderIso.apply_symm_apply ⟨x, hx⟩)
/-
**Real.sin_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sin_arcsin {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) : sin (arcsin x) = x
参数：hx₁ : -1 <= x；hx₂ : x <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sin_arcsin'`：sin_arcsin' {x : Real} (hx : x in Icc (-1 : Real) 1) :
 sin (arcsin x) = x
-/
theorem sin_arcsin {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : sin (arcsin x) = x :=
  sin_arcsin' ⟨hx₁, hx₂⟩
/-
**Real.arcsin_sin'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_sin' {x : Real} (hx : x in Icc (-(π / 2)) (π / 2)) : arcsin (sin x)
 = x
参数：hx : x in Icc (-(π / 2)) (π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.injOn_sin`：injOn_sin : InjOn sin (Icc (-(π / 2)) (π / 2))
· 使用定理 `Real.arcsin_mem_Icc`：arcsin_mem_Icc (x : Real) : arcsin x in Icc (-(π / 
2)) (π / 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sin_arcsin`：sin_arcsin {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) : 
sin (arcsin x) = x
· 使用定理 `Real.neg_one_le_sin`：neg_one_le_sin : -1 <= sin x
· 使用定理 `Real.sin_le_one`：sin_le_one : sin x <= 1
-/
theorem arcsin_sin' {x : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) : arcsin (sin x) = x :=
  injOn_sin (arcsin_mem_Icc _) hx <| by rw [sin_arcsin (neg_one_le_sin _) (sin_le_one _)]
/-
**Real.arcsin_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_sin {x : Real} (hx₁ : -(π / 2) <= x) (hx₂ : x <= π / 2) : arcsin (s
in x) = x
参数：hx₁ : -(π / 2) <= x；hx₂ : x <= π / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.arcsin_sin'`：arcsin_sin' {x : Real} (hx : x in Icc (-(π / 2)) (π / 
2)) : arcsin (sin x) = x
-/
theorem arcsin_sin {x : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) : arcsin (sin x) = x :=
  arcsin_sin' ⟨hx₁, hx₂⟩
/-
**Real.strictMonoOn_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：strictMonoOn_arcsin : StrictMonoOn arcsin (Icc (-1) 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp_strictMonoOn`：∀ {α : Type u} {β : Type v} {γ : Type w} [
inst : Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f 
: α → β} {s : Set …
· 使用定理 `Subtype.strictMono_coe`：Subtype.strictMono_coe [Preorder α] (p : α -> Pr
op) : StrictMono ((↑) : Subtype p -> α)
· 使用定理 `StrictMono.strictMonoOn_IccExtend`：StrictMono.strictMonoOn_IccExtend (hf
 : StrictMono f) : StrictMonoOn (IccExtend h f) (Icc a b)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
theorem strictMonoOn_arcsin : StrictMonoOn arcsin (Icc (-1) 1) :=
  (Subtype.strictMono_coe _).comp_strictMonoOn <|
    sinOrderIso.symm.strictMono.strictMonoOn_IccExtend _

@[gcongr]
/-
**Real.arcsin_lt_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_lt_arcsin {x y : Real} (hx : -1 <= x) (hlt : x < y) (hy : y <= 1) :
 arcsin x < arcsin y
参数：hx : -1 <= x；hlt : x < y；hy : y <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.strictMonoOn_arcsin`：strictMonoOn_arcsin : StrictMonoOn arcsin (Icc
 (-1) 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem arcsin_lt_arcsin {x y : ℝ} (hx : -1 ≤ x) (hlt : x < y) (hy : y ≤ 1) :
    arcsin x < arcsin y :=
  strictMonoOn_arcsin ⟨hx, hlt.le.trans hy⟩ ⟨hx.trans hlt.le, hy⟩ hlt
/-
**Real.monotone_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：monotone_arcsin : Monotone arcsin
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Subtype.mono_coe`：Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monoto
ne ((↑) : Subtype p -> α)
· 使用定理 `Monotone.IccExtend`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder 
α] [inst_1 : Preorder β] {a b : α} (h : a ≤ b)   {f : ↑(Set.Icc a b) → β}, Monot
one f → …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `OrderIso.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (e : α ≃o β), Monotone ⇑e
-/
theorem monotone_arcsin : Monotone arcsin :=
  (Subtype.mono_coe _).comp <| sinOrderIso.symm.monotone.IccExtend _

@[gcongr]
/-
**Real.arcsin_le_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_le_arcsin {x y : Real} (h : x <= y) : arcsin x <= arcsin y
参数：h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.monotone_arcsin`：monotone_arcsin : Monotone arcsin
-/
theorem arcsin_le_arcsin {x y : ℝ} (h : x ≤ y) : arcsin x ≤ arcsin y := monotone_arcsin h
/-
**Real.injOn_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：injOn_arcsin : InjOn arcsin (Icc (-1) 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.injOn`：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn
 f
· 使用定理 `Real.strictMonoOn_arcsin`：strictMonoOn_arcsin : StrictMonoOn arcsin (Icc
 (-1) 1)
-/
theorem injOn_arcsin : InjOn arcsin (Icc (-1) 1) :=
  strictMonoOn_arcsin.injOn
/-
**Real.arcsin_inj** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_inj {x y : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) (hy₁ : -1 <= y) (hy
₂ : y <= 1) : arcsin x = arcsin y ↔ x = y
参数：hx₁ : -1 <= x；hx₂ : x <= 1；hy₁ : -1 <= y；hy₂ : y <= 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `Real.injOn_arcsin`：injOn_arcsin : InjOn arcsin (Icc (-1) 1)
-/
theorem arcsin_inj {x y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) :
    arcsin x = arcsin y ↔ x = y :=
  injOn_arcsin.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

@[continuity, fun_prop]
/-
**Real.continuous_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuous_arcsin : Continuous arcsin
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.Icc_extend'`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOr
der α] {a b : α} {h : a ≤ b} [inst_1 : TopologicalSpace α]   [OrderTopology α] [
inst_3 : Top…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `OrderIso.continuous`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α]
 [inst_1 : Preorder β] [inst_2 : TopologicalSpace α]   [inst_3 : TopologicalSpac
e β] [Ord…
-/
theorem continuous_arcsin : Continuous arcsin :=
  continuous_subtype_val.comp sinOrderIso.symm.continuous.Icc_extend'

@[fun_prop]
/-
**Real.continuousAt_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuousAt_arcsin {x : Real} : ContinuousAt arcsin x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Real.continuous_arcsin`：continuous_arcsin : Continuous arcsin
-/
theorem continuousAt_arcsin {x : ℝ} : ContinuousAt arcsin x :=
  continuous_arcsin.continuousAt
/-
**Real.arcsin_eq_of_sin_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_eq_of_sin_eq {x y : Real} (h₁ : sin x = y) (h₂ : x in Icc (-(π / 2)
) (π / 2)) : arcsin y = x
参数：h₁ : sin x = y；h₂ : x in Icc (-(π / 2)) (π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.injOn_sin`：injOn_sin : InjOn sin (Icc (-(π / 2)) (π / 2))
· 使用定理 `Real.arcsin_mem_Icc`：arcsin_mem_Icc (x : Real) : arcsin x in Icc (-(π / 
2)) (π / 2)
· 使用定理 `Real.sin_arcsin'`：sin_arcsin' {x : Real} (hx : x in Icc (-1 : Real) 1) :
 sin (arcsin x) = x
· 使用定理 `Real.sin_mem_Icc`：sin_mem_Icc (x : Real) : sin x in Icc (-1 : Real) 1
-/
theorem arcsin_eq_of_sin_eq {x y : ℝ} (h₁ : sin x = y) (h₂ : x ∈ Icc (-(π / 2)) (π / 2)) :
    arcsin y = x := by
  subst y
  exact injOn_sin (arcsin_mem_Icc _) h₂ (sin_arcsin' (sin_mem_Icc x))

@[simp]
/-
**Real.arcsin_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_zero : arcsin 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.arcsin_eq_of_sin_eq`：arcsin_eq_of_sin_eq {x y : Real} (h₁ : sin x =
 y) (h₂ : x in Icc (-(π / 2)) (π / 2)) : arcsin y = x
· 使用定理 `Real.sin_zero`：sin_zero : sin 0 = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_div_two_pos`：pi_div_two_pos : 0 < π / 2
-/
theorem arcsin_zero : arcsin 0 = 0 :=
  arcsin_eq_of_sin_eq sin_zero ⟨neg_nonpos.2 pi_div_two_pos.le, pi_div_two_pos.le⟩

@[simp]
/-
**Real.arcsin_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_one : arcsin 1 = π / 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.arcsin_eq_of_sin_eq`：arcsin_eq_of_sin_eq {x y : Real} (h₁ : sin x =
 y) (h₂ : x in Icc (-(π / 2)) (π / 2)) : arcsin y = x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.sin_pi_div_two`：sin_pi_div_two : sin (π / 2) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `neg_le_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : Preorder α] [A
ddLeftMono α] {a : α}, 0 ≤ a → -a ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_div_two_pos`：pi_div_two_pos : 0 < π / 2
-/
theorem arcsin_one : arcsin 1 = π / 2 :=
  arcsin_eq_of_sin_eq sin_pi_div_two <| right_mem_Icc.2 (neg_le_self pi_div_two_pos.le)
/-
**Real.arcsin_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_of_one_le {x : Real} (hx : 1 <= x) : arcsin x = π / 2
参数：hx : 1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `neg_le_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : Preorder α] [A
ddLeftMono α] {a : α}, 0 ≤ a → -a ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.arcsin_projIcc`：arcsin_projIcc (x : Real) : arcsin (projIcc (-1) 1 
(neg_le_self zero_le_one) x) = arcsin x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `Set.projIcc_of_right_le`：projIcc_of_right_le (hx : b <= x) : projIcc a b
 h x = ⟨b, right_mem_Icc.2 h⟩
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Real.arcsin_one`：arcsin_one : arcsin 1 = π / 2
-/
theorem arcsin_of_one_le {x : ℝ} (hx : 1 ≤ x) : arcsin x = π / 2 := by
  rw [← arcsin_projIcc, projIcc_of_right_le _ hx, Subtype.coe_mk, arcsin_one]
/-
**Real.arcsin_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_neg_one : arcsin (-1) = -(π / 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.arcsin_eq_of_sin_eq`：arcsin_eq_of_sin_eq {x y : Real} (h₁ : sin x =
 y) (h₂ : x in Icc (-(π / 2)) (π / 2)) : arcsin y = x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sin_neg`：sin_neg : sin (-x) = -sin x
· 使用定理 `Real.sin_pi_div_two`：sin_pi_div_two : sin (π / 2) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `neg_le_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : Preorder α] [A
ddLeftMono α] {a : α}, 0 ≤ a → -a ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_div_two_pos`：pi_div_two_pos : 0 < π / 2
-/
theorem arcsin_neg_one : arcsin (-1) = -(π / 2) :=
  arcsin_eq_of_sin_eq (by rw [sin_neg, sin_pi_div_two]) <|
    left_mem_Icc.2 (neg_le_self pi_div_two_pos.le)
/-
**Real.arcsin_of_le_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_of_le_neg_one {x : Real} (hx : x <= -1) : arcsin x = -(π / 2)
参数：hx : x <= -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `neg_le_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : Preorder α] [A
ddLeftMono α] {a : α}, 0 ≤ a → -a ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.arcsin_projIcc`：arcsin_projIcc (x : Real) : arcsin (projIcc (-1) 1 
(neg_le_self zero_le_one) x) = arcsin x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Set.projIcc_of_le_left`：projIcc_of_le_left (hx : x <= a) : projIcc a b h
 x = ⟨a, left_mem_Icc.2 h⟩
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Real.arcsin_neg_one`：arcsin_neg_one : arcsin (-1) = -(π / 2)
-/
theorem arcsin_of_le_neg_one {x : ℝ} (hx : x ≤ -1) : arcsin x = -(π / 2) := by
  rw [← arcsin_projIcc, projIcc_of_le_left _ hx, Subtype.coe_mk, arcsin_neg_one]

@[simp]
/-
**Real.arcsin_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_neg (x : Real) : arcsin (-x) = -arcsin x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arcsin_of_le_neg_one`：arcsin_of_le_neg_one {x : Real} (hx : x <= -1
) : arcsin x = -(π / 2)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Real.arcsin_of_one_le`：arcsin_of_one_le {x : Real} (hx : 1 <= x) : arcsi
n x = π / 2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, a ≤ -b ↔ b ≤ -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
· 使用定理 `Real.arcsin_eq_of_sin_eq`：arcsin_eq_of_sin_eq {x y : Real} (h₁ : sin x =
 y) (h₂ : x in Icc (-(π / 2)) (π / 2)) : arcsin y = x
· 使用定理 `Real.sin_neg`：sin_neg : sin (-x) = -sin x
· 使用定理 `Real.sin_arcsin`：sin_arcsin {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) : 
sin (arcsin x) = x
· 使用定理 `Real.arcsin_le_pi_div_two`：arcsin_le_pi_div_two (x : Real) : arcsin x <=
 π / 2
· 使用定理 `neg_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, -a ≤ b ↔ -b ≤ a
· 使用定理 `Real.neg_pi_div_two_le_arcsin`：neg_pi_div_two_le_arcsin (x : Real) : -(π
 / 2) <= arcsin x
-/
theorem arcsin_neg (x : ℝ) : arcsin (-x) = -arcsin x := by
  rcases le_total x (-1) with hx₁ | hx₁
  · rw [arcsin_of_le_neg_one hx₁, neg_neg, arcsin_of_one_le (le_neg.2 hx₁)]
  rcases le_total 1 x with hx₂ | hx₂
  · rw [arcsin_of_one_le hx₂, arcsin_of_le_neg_one (neg_le_neg hx₂)]
  refine arcsin_eq_of_sin_eq ?_ ?_
  · rw [sin_neg, sin_arcsin hx₁ hx₂]
  · exact ⟨neg_le_neg (arcsin_le_pi_div_two _), neg_le.2 (neg_pi_div_two_le_arcsin _)⟩
/-
**Real.arcsin_le_iff_le_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_le_iff_le_sin {x y : Real} (hx : x in Icc (-1 : Real) 1) (hy : y in
 Icc (-(π / 2)) (π / 2)) : arcsin x <= y ↔ x <= sin y
参数：hx : x in Icc (-1 : Real) 1；hy : y in Icc (-(π / 2)) (π / 2)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.arcsin_sin'`：arcsin_sin' {x : Real} (hx : x in Icc (-(π / 2)) (π / 
2)) : arcsin (sin x) = x
· 使用定理 `StrictMonoOn.le_iff_le`：StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a <= f b ↔ a <= b
· 使用定理 `Real.strictMonoOn_arcsin`：strictMonoOn_arcsin : StrictMonoOn arcsin (Icc
 (-1) 1)
· 使用定理 `Real.sin_mem_Icc`：sin_mem_Icc (x : Real) : sin x in Icc (-1 : Real) 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem arcsin_le_iff_le_sin {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-(π / 2)) (π / 2)) :
    arcsin x ≤ y ↔ x ≤ sin y := by
  rw [← arcsin_sin' hy, strictMonoOn_arcsin.le_iff_le hx (sin_mem_Icc _), arcsin_sin' hy]
/-
**Real.arcsin_le_iff_le_sin'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_le_iff_le_sin' {x y : Real} (hy : y in Ico (-(π / 2)) (π / 2)) : ar
csin x <= y ↔ x <= sin y
参数：hy : y in Ico (-(π / 2)) (π / 2)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.arcsin_of_le_neg_one`：arcsin_of_le_neg_one {x : Real} (hx : x <= -1
) : arcsin x = -(π / 2)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Real.neg_one_le_sin`：neg_one_le_sin : -1 <= sin x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Real.arcsin_of_one_le`：arcsin_of_one_le {x : Real} (hx : 1 <= x) : arcsi
n x = π / 2
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Real.sin_le_one`：sin_le_one : sin x <= 1
· 使用定理 `Real.arcsin_le_iff_le_sin`：arcsin_le_iff_le_sin {x y : Real} (hx : x in 
Icc (-1 : Real) 1) (hy : y in Icc (-(π / 2)) (π / 2)) : arcsin x <= y ↔ x <= sin
 y
· 使用定理 `Set.mem_Icc_of_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x 
∈ Set.Ico b a → x ∈ Set.Icc b a
-/
theorem arcsin_le_iff_le_sin' {x y : ℝ} (hy : y ∈ Ico (-(π / 2)) (π / 2)) :
    arcsin x ≤ y ↔ x ≤ sin y := by
  rcases le_total x (-1) with hx₁ | hx₁
  · simp [arcsin_of_le_neg_one hx₁, hy.1, hx₁.trans (neg_one_le_sin _)]
  rcases lt_or_ge 1 x with hx₂ | hx₂
  · simp [arcsin_of_one_le hx₂.le, hy.2.not_ge, (sin_le_one y).trans_lt hx₂]
  exact arcsin_le_iff_le_sin ⟨hx₁, hx₂⟩ (mem_Icc_of_Ico hy)
/-
**Real.le_arcsin_iff_sin_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_arcsin_iff_sin_le {x y : Real} (hx : x in Icc (-(π / 2)) (π / 2)) (hy :
 y in Icc (-1 : Real) 1) : x <= arcsin y ↔ sin x <= y
参数：hx : x in Icc (-(π / 2)) (π / 2)；hy : y in Icc (-1 : Real) 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.arcsin_neg`：arcsin_neg (x : Real) : arcsin (-x) = -arcsin x
· 使用定理 `Real.arcsin_le_iff_le_sin`：arcsin_le_iff_le_sin {x y : Real} (hx : x in 
Icc (-1 : Real) 1) (hy : y in Icc (-(π / 2)) (π / 2)) : arcsin x <= y ↔ x <= sin
 y
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, -a ≤ b ↔ -b ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Real.sin_neg`：sin_neg : sin (-x) = -sin x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_arcsin_iff_sin_le {x y : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) (hy : y ∈ Icc (-1 : ℝ) 1) :
    x ≤ arcsin y ↔ sin x ≤ y := by
  rw [← neg_le_neg_iff, ← arcsin_neg,
    arcsin_le_iff_le_sin ⟨neg_le_neg hy.2, neg_le.2 hy.1⟩ ⟨neg_le_neg hx.2, neg_le.2 hx.1⟩, sin_neg,
    neg_le_neg_iff]
/-
**Real.le_arcsin_iff_sin_le'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_arcsin_iff_sin_le' {x y : Real} (hx : x in Ioc (-(π / 2)) (π / 2)) : x 
<= arcsin y ↔ sin x <= y
参数：hx : x in Ioc (-(π / 2)) (π / 2)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.arcsin_neg`：arcsin_neg (x : Real) : arcsin (-x) = -arcsin x
· 使用定理 `Real.arcsin_le_iff_le_sin'`：arcsin_le_iff_le_sin' {x y : Real} (hy : y i
n Ico (-(π / 2)) (π / 2)) : arcsin x <= y ↔ x <= sin y
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStric
tMono α] {a b : α} [AddRightStrictMono α],   -a < b ↔ -b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Real.sin_neg`：sin_neg : sin (-x) = -sin x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_arcsin_iff_sin_le' {x y : ℝ} (hx : x ∈ Ioc (-(π / 2)) (π / 2)) :
    x ≤ arcsin y ↔ sin x ≤ y := by
  rw [← neg_le_neg_iff, ← arcsin_neg, arcsin_le_iff_le_sin' ⟨neg_le_neg hx.2, neg_lt.2 hx.1⟩,
    sin_neg, neg_le_neg_iff]
/-
**Real.arcsin_lt_iff_lt_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_lt_iff_lt_sin {x y : Real} (hx : x in Icc (-1 : Real) 1) (hy : y in
 Icc (-(π / 2)) (π / 2)) : arcsin x < y ↔ x < sin y
参数：hx : x in Icc (-1 : Real) 1；hy : y in Icc (-(π / 2)) (π / 2)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Real.le_arcsin_iff_sin_le`：le_arcsin_iff_sin_le {x y : Real} (hx : x in 
Icc (-(π / 2)) (π / 2)) (hy : y in Icc (-1 : Real) 1) : x <= arcsin y ↔ sin x <=
 y
-/
theorem arcsin_lt_iff_lt_sin {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-(π / 2)) (π / 2)) :
    arcsin x < y ↔ x < sin y :=
  not_le.symm.trans <| (not_congr <| le_arcsin_iff_sin_le hy hx).trans not_le
/-
**Real.arcsin_lt_iff_lt_sin'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_lt_iff_lt_sin' {x y : Real} (hy : y in Ioc (-(π / 2)) (π / 2)) : ar
csin x < y ↔ x < sin y
参数：hy : y in Ioc (-(π / 2)) (π / 2)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Real.le_arcsin_iff_sin_le'`：le_arcsin_iff_sin_le' {x y : Real} (hx : x i
n Ioc (-(π / 2)) (π / 2)) : x <= arcsin y ↔ sin x <= y
-/
theorem arcsin_lt_iff_lt_sin' {x y : ℝ} (hy : y ∈ Ioc (-(π / 2)) (π / 2)) :
    arcsin x < y ↔ x < sin y :=
  not_le.symm.trans <| (not_congr <| le_arcsin_iff_sin_le' hy).trans not_le
/-
**Real.lt_arcsin_iff_sin_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：lt_arcsin_iff_sin_lt {x y : Real} (hx : x in Icc (-(π / 2)) (π / 2)) (hy :
 y in Icc (-1 : Real) 1) : x < arcsin y ↔ sin x < y
参数：hx : x in Icc (-(π / 2)) (π / 2)；hy : y in Icc (-1 : Real) 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Real.arcsin_le_iff_le_sin`：arcsin_le_iff_le_sin {x y : Real} (hx : x in 
Icc (-1 : Real) 1) (hy : y in Icc (-(π / 2)) (π / 2)) : arcsin x <= y ↔ x <= sin
 y
-/
theorem lt_arcsin_iff_sin_lt {x y : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) (hy : y ∈ Icc (-1 : ℝ) 1) :
    x < arcsin y ↔ sin x < y :=
  not_le.symm.trans <| (not_congr <| arcsin_le_iff_le_sin hy hx).trans not_le
/-
**Real.lt_arcsin_iff_sin_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：lt_arcsin_iff_sin_lt' {x y : Real} (hx : x in Ico (-(π / 2)) (π / 2)) : x 
< arcsin y ↔ sin x < y
参数：hx : x in Ico (-(π / 2)) (π / 2)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Real.arcsin_le_iff_le_sin'`：arcsin_le_iff_le_sin' {x y : Real} (hy : y i
n Ico (-(π / 2)) (π / 2)) : arcsin x <= y ↔ x <= sin y
-/
theorem lt_arcsin_iff_sin_lt' {x y : ℝ} (hx : x ∈ Ico (-(π / 2)) (π / 2)) :
    x < arcsin y ↔ sin x < y :=
  not_le.symm.trans <| (not_congr <| arcsin_le_iff_le_sin' hx).trans not_le
/-
**Real.arcsin_eq_iff_eq_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_eq_iff_eq_sin {x y : Real} (hy : y in Ioo (-(π / 2)) (π / 2)) : arc
sin x = y ↔ x = sin y
参数：hy : y in Ioo (-(π / 2)) (π / 2)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arcsin_le_iff_le_sin'`：arcsin_le_iff_le_sin' {x y : Real} (hy : y i
n Ico (-(π / 2)) (π / 2)) : arcsin x <= y ↔ x <= sin y
· 使用定理 `Set.mem_Ico_of_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x 
∈ Set.Ioo a b → x ∈ Set.Ico a b
· 使用定理 `Real.le_arcsin_iff_sin_le'`：le_arcsin_iff_sin_le' {x y : Real} (hx : x i
n Ioc (-(π / 2)) (π / 2)) : x <= arcsin y ↔ sin x <= y
· 使用定理 `Set.mem_Ioc_of_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x 
∈ Set.Ioo b a → x ∈ Set.Ioc b a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem arcsin_eq_iff_eq_sin {x y : ℝ} (hy : y ∈ Ioo (-(π / 2)) (π / 2)) :
    arcsin x = y ↔ x = sin y := by
  simp only [le_antisymm_iff, arcsin_le_iff_le_sin' (mem_Ico_of_Ioo hy),
    le_arcsin_iff_sin_le' (mem_Ioc_of_Ioo hy)]

@[simp]
/-
**Real.arcsin_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_nonneg {x : Real} : 0 <= arcsin x ↔ 0 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Real.le_arcsin_iff_sin_le'`：le_arcsin_iff_sin_le' {x y : Real} (hx : x i
n Ioc (-(π / 2)) (π / 2)) : x <= arcsin y ↔ sin x <= y
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.pi_div_two_pos`：pi_div_two_pos : 0 < π / 2
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sin_zero`：sin_zero : sin 0 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem arcsin_nonneg {x : ℝ} : 0 ≤ arcsin x ↔ 0 ≤ x :=
  (le_arcsin_iff_sin_le' ⟨neg_lt_zero.2 pi_div_two_pos, pi_div_two_pos.le⟩).trans <| by
    rw [sin_zero]

@[simp]
/-
**Real.arcsin_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_nonpos {x : Real} : arcsin x <= 0 ↔ x <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.arcsin_nonneg`：arcsin_nonneg {x : Real} : 0 <= arcsin x ↔ 0 <= x
· 使用定理 `Real.arcsin_neg`：arcsin_neg (x : Real) : arcsin (-x) = -arcsin x
-/
theorem arcsin_nonpos {x : ℝ} : arcsin x ≤ 0 ↔ x ≤ 0 :=
  neg_nonneg.symm.trans <| arcsin_neg x ▸ arcsin_nonneg.trans neg_nonneg

@[simp]
/-
**Real.arcsin_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_eq_zero_iff {x : Real} : arcsin x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem arcsin_eq_zero_iff {x : ℝ} : arcsin x = 0 ↔ x = 0 := by simp [le_antisymm_iff]

@[simp]
/-
**Real.zero_eq_arcsin_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：zero_eq_arcsin_iff {x} : 0 = arcsin x ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Real.arcsin_eq_zero_iff`：arcsin_eq_zero_iff {x : Real} : arcsin x = 0 ↔ 
x = 0
-/
theorem zero_eq_arcsin_iff {x} : 0 = arcsin x ↔ x = 0 :=
  eq_comm.trans arcsin_eq_zero_iff

@[simp]
/-
**Real.arcsin_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_pos {x : Real} : 0 < arcsin x ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Real.arcsin_nonpos`：arcsin_nonpos {x : Real} : arcsin x <= 0 ↔ x <= 0
-/
theorem arcsin_pos {x : ℝ} : 0 < arcsin x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le arcsin_nonpos

@[simp]
/-
**Real.arcsin_lt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_lt_zero {x : Real} : arcsin x < 0 ↔ x < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Real.arcsin_nonneg`：arcsin_nonneg {x : Real} : 0 <= arcsin x ↔ 0 <= x
-/
theorem arcsin_lt_zero {x : ℝ} : arcsin x < 0 ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le arcsin_nonneg

@[simp]
/-
**Real.arcsin_lt_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_lt_pi_div_two {x : Real} : arcsin x < π / 2 ↔ x < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.arcsin_lt_iff_lt_sin'`：arcsin_lt_iff_lt_sin' {x y : Real} (hy : y i
n Ioc (-(π / 2)) (π / 2)) : arcsin x < y ↔ x < sin y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Ioc b a ↔ b < a
· 使用定理 `neg_lt_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : Preorder α] [A
ddLeftStrictMono α] {a : α}, 0 < a → -a < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.pi_div_two_pos`：pi_div_two_pos : 0 < π / 2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sin_pi_div_two`：sin_pi_div_two : sin (π / 2) = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem arcsin_lt_pi_div_two {x : ℝ} : arcsin x < π / 2 ↔ x < 1 :=
  (arcsin_lt_iff_lt_sin' (right_mem_Ioc.2 <| neg_lt_self pi_div_two_pos)).trans <| by
    rw [sin_pi_div_two]

@[simp]
/-
**Real.neg_pi_div_two_lt_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：neg_pi_div_two_lt_arcsin {x : Real} : -(π / 2) < arcsin x ↔ -1 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.lt_arcsin_iff_sin_lt'`：lt_arcsin_iff_sin_lt' {x y : Real} (hx : x i
n Ico (-(π / 2)) (π / 2)) : x < arcsin y ↔ sin x < y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Ico a b ↔ a < b
· 使用定理 `neg_lt_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : Preorder α] [A
ddLeftStrictMono α] {a : α}, 0 < a → -a < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.pi_div_two_pos`：pi_div_two_pos : 0 < π / 2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sin_neg`：sin_neg : sin (-x) = -sin x
· 使用定理 `Real.sin_pi_div_two`：sin_pi_div_two : sin (π / 2) = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem neg_pi_div_two_lt_arcsin {x : ℝ} : -(π / 2) < arcsin x ↔ -1 < x :=
  (lt_arcsin_iff_sin_lt' <| left_mem_Ico.2 <| neg_lt_self pi_div_two_pos).trans <| by
    rw [sin_neg, sin_pi_div_two]

@[simp]
/-
**Real.arcsin_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_eq_pi_div_two {x : Real} : arcsin x = π / 2 ↔ 1 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.arcsin_lt_pi_div_two`：arcsin_lt_pi_div_two {x : Real} : arcsin x < 
π / 2 ↔ x < 1
· 使用定理 `Real.arcsin_of_one_le`：arcsin_of_one_le {x : Real} (hx : 1 <= x) : arcsi
n x = π / 2
-/
theorem arcsin_eq_pi_div_two {x : ℝ} : arcsin x = π / 2 ↔ 1 ≤ x :=
  ⟨fun h => not_lt.1 fun h' => (arcsin_lt_pi_div_two.2 h').ne h, arcsin_of_one_le⟩

@[simp]
/-
**Real.pi_div_two_eq_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_div_two_eq_arcsin {x} : π / 2 = arcsin x ↔ 1 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Real.arcsin_eq_pi_div_two`：arcsin_eq_pi_div_two {x : Real} : arcsin x = 
π / 2 ↔ 1 <= x
-/
theorem pi_div_two_eq_arcsin {x} : π / 2 = arcsin x ↔ 1 ≤ x :=
  eq_comm.trans arcsin_eq_pi_div_two

@[simp]
/-
**Real.pi_div_two_le_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_div_two_le_arcsin {x} : π / 2 <= arcsin x ↔ 1 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `Real.arcsin_le_pi_div_two`：arcsin_le_pi_div_two (x : Real) : arcsin x <=
 π / 2
· 使用定理 `Real.pi_div_two_eq_arcsin`：pi_div_two_eq_arcsin {x} : π / 2 = arcsin x ↔
 1 <= x
-/
theorem pi_div_two_le_arcsin {x} : π / 2 ≤ arcsin x ↔ 1 ≤ x :=
  (arcsin_le_pi_div_two x).ge_iff_eq'.trans pi_div_two_eq_arcsin

@[simp]
/-
**Real.arcsin_eq_neg_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_eq_neg_pi_div_two {x : Real} : arcsin x = -(π / 2) ↔ x <= -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.neg_pi_div_two_lt_arcsin`：neg_pi_div_two_lt_arcsin {x : Real} : -(π
 / 2) < arcsin x ↔ -1 < x
· 使用定理 `Real.arcsin_of_le_neg_one`：arcsin_of_le_neg_one {x : Real} (hx : x <= -1
) : arcsin x = -(π / 2)
-/
theorem arcsin_eq_neg_pi_div_two {x : ℝ} : arcsin x = -(π / 2) ↔ x ≤ -1 :=
  ⟨fun h => not_lt.1 fun h' => (neg_pi_div_two_lt_arcsin.2 h').ne' h, arcsin_of_le_neg_one⟩

@[simp]
/-
**Real.neg_pi_div_two_eq_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：neg_pi_div_two_eq_arcsin {x} : -(π / 2) = arcsin x ↔ x <= -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Real.arcsin_eq_neg_pi_div_two`：arcsin_eq_neg_pi_div_two {x : Real} : arc
sin x = -(π / 2) ↔ x <= -1
-/
theorem neg_pi_div_two_eq_arcsin {x} : -(π / 2) = arcsin x ↔ x ≤ -1 :=
  eq_comm.trans arcsin_eq_neg_pi_div_two

@[simp]
/-
**Real.arcsin_le_neg_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_le_neg_pi_div_two {x} : arcsin x <= -(π / 2) ↔ x <= -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `Real.neg_pi_div_two_le_arcsin`：neg_pi_div_two_le_arcsin (x : Real) : -(π
 / 2) <= arcsin x
· 使用定理 `Real.arcsin_eq_neg_pi_div_two`：arcsin_eq_neg_pi_div_two {x : Real} : arc
sin x = -(π / 2) ↔ x <= -1
-/
theorem arcsin_le_neg_pi_div_two {x} : arcsin x ≤ -(π / 2) ↔ x ≤ -1 :=
  (neg_pi_div_two_le_arcsin x).ge_iff_eq'.trans arcsin_eq_neg_pi_div_two

@[simp]
/-
**Real.pi_div_four_le_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_div_four_le_arcsin {x} : π / 4 <= arcsin x ↔ √2 / 2 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sin_pi_div_four`：sin_pi_div_four : sin (π / 4) = √2 / 2
· 使用定理 `Real.le_arcsin_iff_sin_le'`：le_arcsin_iff_sin_le' {x y : Real} (hx : x i
n Ioc (-(π / 2)) (π / 2)) : x <= arcsin y ↔ sin x <= y
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 67 条，此处仅展示前 30 条）
-/
theorem pi_div_four_le_arcsin {x} : π / 4 ≤ arcsin x ↔ √2 / 2 ≤ x := by
  rw [← sin_pi_div_four, le_arcsin_iff_sin_le']
  have := pi_pos
  constructor <;> linarith
/-
**Real.cos_arcsin_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cos_arcsin_nonneg (x : Real) : 0 <= cos (arcsin x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.cos_nonneg_of_mem_Icc`：cos_nonneg_of_mem_Icc {x : Real} (hx : x in 
Icc (-(π / 2)) (π / 2)) : 0 <= cos x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.neg_pi_div_two_le_arcsin`：neg_pi_div_two_le_arcsin (x : Real) : -(π
 / 2) <= arcsin x
· 使用定理 `Real.arcsin_le_pi_div_two`：arcsin_le_pi_div_two (x : Real) : arcsin x <=
 π / 2
-/
theorem cos_arcsin_nonneg (x : ℝ) : 0 ≤ cos (arcsin x) :=
  cos_nonneg_of_mem_Icc ⟨neg_pi_div_two_le_arcsin _, arcsin_le_pi_div_two _⟩

-- The junk values for `arcsin` and `sqrt` make this true even outside `[-1, 1]`.
/-
**Real.cos_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cos_arcsin (x : Real) : cos (arcsin x) = √(1 - x ^ 2)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sin_sq_add_cos_sq`：∀ (x : ℝ), Real.sin x ^ 2 + Real.cos x ^ 2 = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt_mul_self`：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
· 使用定理 `Real.cos_arcsin_nonneg`：cos_arcsin_nonneg (x : Real) : 0 <= cos (arcsin 
x)
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_inj`：sqrt_inj (hx : 0 <= x) (hy : 0 <= y) : √x = √y ↔ x = y
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.sin_sq_le_one`：sin_sq_le_one : sin x ^ 2 <= 1
· 使用定理 `eq_sub_iff_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a = b - c ↔ c + a = b
· 使用定理 `Real.sin_arcsin`：sin_arcsin {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) : 
sin (arcsin x) = x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.arcsin_of_one_le`：arcsin_of_one_le {x : Real} (hx : 1 <= x) : arcsi
n x = π / 2
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Real.cos_pi_div_two`：cos_pi_div_two : cos (π / 2) = 0
· 使用定理 `Real.sqrt_eq_zero_of_nonpos`：sqrt_eq_zero_of_nonpos (h : x <= 0) : √x = 
0
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
（共 96 条，此处仅展示前 30 条）
-/
theorem cos_arcsin (x : ℝ) : cos (arcsin x) = √(1 - x ^ 2) := by
  by_cases hx₁ : -1 ≤ x; swap
  · rw [not_le] at hx₁
    rw [arcsin_of_le_neg_one hx₁.le, cos_neg, cos_pi_div_two, sqrt_eq_zero_of_nonpos]
    nlinarith
  by_cases hx₂ : x ≤ 1; swap
  · rw [not_le] at hx₂
    rw [arcsin_of_one_le hx₂.le, cos_pi_div_two, sqrt_eq_zero_of_nonpos]
    nlinarith
  have : sin (arcsin x) ^ 2 + cos (arcsin x) ^ 2 = 1 := sin_sq_add_cos_sq (arcsin x)
  rw [← eq_sub_iff_add_eq', ← sqrt_inj (sq_nonneg _) (sub_nonneg.2 (sin_sq_le_one (arcsin x))), sq,
    sqrt_mul_self (cos_arcsin_nonneg _)] at this
  rw [this, sin_arcsin hx₁ hx₂]

-- The junk values for `arcsin` and `sqrt` make this true even outside `[-1, 1]`.
/-
**Real.tan_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tan_arcsin (x : Real) : tan (arcsin x) = x / √(1 - x ^ 2)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.tan_eq_sin_div_cos`：∀ (x : ℝ), Real.tan x = Real.sin x / Real.cos x
· 使用定理 `Real.cos_arcsin`：cos_arcsin (x : Real) : cos (arcsin x) = √(1 - x ^ 2)
· 使用定理 `Real.sin_arcsin`：sin_arcsin {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) : 
sin (arcsin x) = x
· 使用定理 `Real.sqrt_eq_zero_of_nonpos`：sqrt_eq_zero_of_nonpos (h : x <= 0) : √x = 
0
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 87 条，此处仅展示前 30 条）
-/
theorem tan_arcsin (x : ℝ) : tan (arcsin x) = x / √(1 - x ^ 2) := by
  rw [tan_eq_sin_div_cos, cos_arcsin]
  by_cases hx₁ : -1 ≤ x; swap
  · have h : √(1 - x ^ 2) = 0 := sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [h]
    simp
  by_cases hx₂ : x ≤ 1; swap
  · have h : √(1 - x ^ 2) = 0 := sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [h]
    simp
  rw [sin_arcsin hx₁ hx₂]

/-- Inverse of the `cos` function, returns values in the range `0 ≤ arccos x` and `arccos x ≤ π`.
  It defaults to `π` on `(-∞, -1)` and to `0` to `(1, ∞)`. -/
@[pp_nodot]
/-
**Real.arccos** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：arccos (x : Real) : Real
参数：x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inverse of the `cos` function, returns values in the range `0 ≤ arccos x` and `a
rccos x ≤ π`.
  It defaults to `π` on `(-∞, -1)` and to `0` to `(1, ∞)`.
-/
noncomputable def arccos (x : ℝ) : ℝ :=
  π / 2 - arcsin x
/-
**Real.arccos_eq_pi_div_two_sub_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_eq_pi_div_two_sub_arcsin (x : Real) : arccos x = π / 2 - arcsin x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arccos_eq_pi_div_two_sub_arcsin (x : ℝ) : arccos x = π / 2 - arcsin x :=
  rfl
/-
**Real.arcsin_eq_pi_div_two_sub_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_eq_pi_div_two_sub_arccos (x : Real) : arcsin x = π / 2 - arccos x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arcsin_eq_pi_div_two_sub_arccos (x : ℝ) : arcsin x = π / 2 - arccos x := by simp [arccos]
/-
**Real.arccos_le_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_le_pi (x : Real) : arccos x <= π
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 60 条，此处仅展示前 30 条）
-/
theorem arccos_le_pi (x : ℝ) : arccos x ≤ π := by
  unfold arccos; linarith [neg_pi_div_two_le_arcsin x]
/-
**Real.arccos_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_nonneg (x : Real) : 0 <= arccos x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 57 条，此处仅展示前 30 条）
-/
theorem arccos_nonneg (x : ℝ) : 0 ≤ arccos x := by
  unfold arccos; linarith [arcsin_le_pi_div_two x]

@[simp]
/-
**Real.arccos_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_pos {x : Real} : 0 < arccos x ↔ x < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem arccos_pos {x : ℝ} : 0 < arccos x ↔ x < 1 := by simp [arccos]
/-
**Real.cos_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cos_arccos {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) : cos (arccos x) = x
参数：hx₁ : -1 <= x；hx₂ : x <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arccos.eq_1`：∀ (x : ℝ), Real.arccos x = Real.pi / 2 - Real.arcsin x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.cos_pi_div_two_sub`：cos_pi_div_two_sub (x : Real) : cos (π / 2 - x)
 = sin x
· 使用定理 `Real.sin_arcsin`：sin_arcsin {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) : 
sin (arcsin x) = x
-/
theorem cos_arccos {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : cos (arccos x) = x := by
  rw [arccos, cos_pi_div_two_sub, sin_arcsin hx₁ hx₂]
/-
**Real.arccos_cos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_cos {x : Real} (hx₁ : 0 <= x) (hx₂ : x <= π) : arccos (cos x) = x
参数：hx₁ : 0 <= x；hx₂ : x <= π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arccos.eq_1`：∀ (x : ℝ), Real.arccos x = Real.pi / 2 - Real.arcsin x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sin_pi_div_two_sub`：sin_pi_div_two_sub (x : Real) : sin (π / 2 - x)
 = cos x
· 使用定理 `Real.arcsin_sin`：arcsin_sin {x : Real} (hx₁ : -(π / 2) <= x) (hx₂ : x <=
 π / 2) : arcsin (sin x) = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
（共 51 条，此处仅展示前 30 条）
-/
theorem arccos_cos {x : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π) : arccos (cos x) = x := by
  rw [arccos, ← sin_pi_div_two_sub, arcsin_sin] <;> simp [sub_eq_add_neg] <;> linarith
/-
**Real.arccos_eq_of_eq_cos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：arccos_eq_of_eq_cos (hy₀ : 0 <= y) (hy₁ : y <= π) (hxy : x = cos y) : arcc
os x = y
参数：hy₀ : 0 <= y；hy₁ : y <= π；hxy : x = cos y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arccos_cos`：arccos_cos {x : Real} (hx₁ : 0 <= x) (hx₂ : x <= π) : a
rccos (cos x) = x
-/
lemma arccos_eq_of_eq_cos (hy₀ : 0 ≤ y) (hy₁ : y ≤ π) (hxy : x = cos y) : arccos x = y := by
  rw [hxy, arccos_cos hy₀ hy₁]
/-
**Real.strictAntiOn_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：strictAntiOn_arccos : StrictAntiOn arccos (Icc (-1) 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_lt_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Add
LeftStrictMono α] [AddRightStrictMono α] {a b : α},   a < b → ∀ (c : α), c - b <
 c - …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.strictMonoOn_arcsin`：strictMonoOn_arcsin : StrictMonoOn arcsin (Icc
 (-1) 1)
-/
theorem strictAntiOn_arccos : StrictAntiOn arccos (Icc (-1) 1) := fun _ hx _ hy h =>
  sub_lt_sub_left (strictMonoOn_arcsin hx hy h) _

@[gcongr]
/-
**Real.arccos_lt_arccos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：arccos_lt_arccos {x y : Real} (hx : -1 <= x) (hlt : x < y) (hy : y <= 1) :
 arccos y < arccos x
参数：hx : -1 <= x；hlt : x < y；hy : y <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_lt_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Add
LeftStrictMono α] [AddRightStrictMono α] {a b : α},   a < b → ∀ (c : α), c - b <
 c - …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.arcsin_lt_arcsin`：arcsin_lt_arcsin {x y : Real} (hx : -1 <= x) (hlt
 : x < y) (hy : y <= 1) : arcsin x < arcsin y
-/
lemma arccos_lt_arccos {x y : ℝ} (hx : -1 ≤ x) (hlt : x < y) (hy : y ≤ 1) :
    arccos y < arccos x := by
  unfold arccos; gcongr

@[gcongr]
/-
**Real.arccos_le_arccos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：arccos_le_arccos {x y : Real} (hlt : x <= y) : arccos y <= arccos x
参数：hlt : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_le_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] [AddRightMono α] {a b : α},   a ≤ b → ∀ (c : α), c - b ≤ c - a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.arcsin_le_arcsin`：arcsin_le_arcsin {x y : Real} (h : x <= y) : arcs
in x <= arcsin y
-/
lemma arccos_le_arccos {x y : ℝ} (hlt : x ≤ y) : arccos y ≤ arccos x := by unfold arccos; gcongr
/-
**Real.antitone_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：antitone_arccos : Antitone arccos
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.arccos_le_arccos`：arccos_le_arccos {x y : Real} (hlt : x <= y) : ar
ccos y <= arccos x
-/
theorem antitone_arccos : Antitone arccos := fun _ _ ↦ arccos_le_arccos
/-
**Real.arccos_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_injOn : InjOn arccos (Icc (-1) 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictAntiOn.injOn`：StrictAntiOn.injOn (hf : StrictAntiOn f s) : s.InjOn
 f
· 使用定理 `Real.strictAntiOn_arccos`：strictAntiOn_arccos : StrictAntiOn arccos (Icc
 (-1) 1)
-/
theorem arccos_injOn : InjOn arccos (Icc (-1) 1) :=
  strictAntiOn_arccos.injOn
/-
**Real.arccos_inj** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_inj {x y : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) (hy₁ : -1 <= y) (hy
₂ : y <= 1) : arccos x = arccos y ↔ x = y
参数：hx₁ : -1 <= x；hx₂ : x <= 1；hy₁ : -1 <= y；hy₂ : y <= 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `Real.arccos_injOn`：arccos_injOn : InjOn arccos (Icc (-1) 1)
-/
theorem arccos_inj {x y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) :
    arccos x = arccos y ↔ x = y :=
  arccos_injOn.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

@[simp]
/-
**Real.arccos_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_zero : arccos 0 = π / 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arcsin_zero`：arcsin_zero : arcsin 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arccos_zero : arccos 0 = π / 2 := by simp [arccos]

@[simp]
/-
**Real.arccos_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_one : arccos 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.arcsin_one`：arcsin_one : arcsin 1 = π / 2
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arccos_one : arccos 1 = 0 := by simp [arccos]

@[simp]
/-
**Real.arccos_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_neg_one : arccos (-1) = π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.arcsin_neg`：arcsin_neg (x : Real) : arcsin (-x) = -arcsin x
· 使用定理 `Real.arcsin_one`：arcsin_one : arcsin 1 = π / 2
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arccos_neg_one : arccos (-1) = π := by simp [arccos, add_halves]

@[simp]
/-
**Real.arccos_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_eq_zero {x} : arccos x = 0 ↔ 1 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem arccos_eq_zero {x} : arccos x = 0 ↔ 1 ≤ x := by simp [arccos, sub_eq_zero]

@[simp]
/-
**Real.arccos_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_eq_pi_div_two {x} : arccos x = π / 2 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem arccos_eq_pi_div_two {x} : arccos x = π / 2 ↔ x = 0 := by simp [arccos]

@[simp]
/-
**Real.arccos_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_eq_pi {x} : arccos x = π ↔ x <= -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arccos.eq_1`：∀ (x : ℝ), Real.arccos x = Real.pi / 2 - Real.arcsin x
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `div_two_sub_self`：div_two_sub_self (a : α) : a / 2 - a = -(a / 2)
· 使用定理 `Real.neg_pi_div_two_eq_arcsin`：neg_pi_div_two_eq_arcsin {x} : -(π / 2) =
 arcsin x ↔ x <= -1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem arccos_eq_pi {x} : arccos x = π ↔ x ≤ -1 := by
  rw [arccos, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', div_two_sub_self, neg_pi_div_two_eq_arcsin]
/-
**Real.arccos_lt_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_lt_pi {x} : arccos x < π ↔ -1 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arccos_lt_pi {x} : arccos x < π ↔ -1 < x := by grind [arccos_le_pi, arccos_eq_pi]
/-
**Real.arccos_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_neg (x : Real) : arccos (-x) = π - arccos x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.arccos.eq_1`：∀ (x : ℝ), Real.arccos x = Real.pi / 2 - Real.arcsin x
· 使用定理 `Real.arcsin_neg`：arcsin_neg (x : Real) : arcsin (-x) = -arcsin x
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `sub_sub_self`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - (a
 - b) = b
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
-/
theorem arccos_neg (x : ℝ) : arccos (-x) = π - arccos x := by
  rw [← add_halves π, arccos, arcsin_neg, arccos, add_sub_assoc, sub_sub_self, sub_neg_eq_add]
/-
**Real.arccos_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_of_one_le {x : Real} (hx : 1 <= x) : arccos x = 0
参数：hx : 1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arccos.eq_1`：∀ (x : ℝ), Real.arccos x = Real.pi / 2 - Real.arcsin x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.arcsin_of_one_le`：arcsin_of_one_le {x : Real} (hx : 1 <= x) : arcsi
n x = π / 2
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem arccos_of_one_le {x : ℝ} (hx : 1 ≤ x) : arccos x = 0 := by
  rw [arccos, arcsin_of_one_le hx, sub_self]
/-
**Real.arccos_of_le_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_of_le_neg_one {x : Real} (hx : x <= -1) : arccos x = π
参数：hx : x <= -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arccos.eq_1`：∀ (x : ℝ), Real.arccos x = Real.pi / 2 - Real.arcsin x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.arcsin_of_le_neg_one`：arcsin_of_le_neg_one {x : Real} (hx : x <= -1
) : arcsin x = -(π / 2)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem arccos_of_le_neg_one {x : ℝ} (hx : x ≤ -1) : arccos x = π := by
  rw [arccos, arcsin_of_le_neg_one hx, sub_neg_eq_add, add_halves]

-- The junk values for `arccos` and `sqrt` make this true even outside `[-1, 1]`.
/-
**Real.sin_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sin_arccos (x : Real) : sin (arccos x) = √(1 - x ^ 2)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arccos_eq_pi_div_two_sub_arcsin`：arccos_eq_pi_div_two_sub_arcsin (x
 : Real) : arccos x = π / 2 - arcsin x
· 使用定理 `Real.sin_pi_div_two_sub`：sin_pi_div_two_sub (x : Real) : sin (π / 2 - x)
 = cos x
· 使用定理 `Real.cos_arcsin`：cos_arcsin (x : Real) : cos (arcsin x) = √(1 - x ^ 2)
· 使用定理 `Real.arccos_of_one_le`：arccos_of_one_le {x : Real} (hx : 1 <= x) : arcco
s x = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Real.sin_zero`：sin_zero : sin 0 = 0
· 使用定理 `Real.sqrt_eq_zero_of_nonpos`：sqrt_eq_zero_of_nonpos (h : x <= 0) : √x = 
0
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 87 条，此处仅展示前 30 条）
-/
theorem sin_arccos (x : ℝ) : sin (arccos x) = √(1 - x ^ 2) := by
  by_cases hx₁ : -1 ≤ x; swap
  · rw [not_le] at hx₁
    rw [arccos_of_le_neg_one hx₁.le, sin_pi, sqrt_eq_zero_of_nonpos]
    nlinarith
  by_cases hx₂ : x ≤ 1; swap
  · rw [not_le] at hx₂
    rw [arccos_of_one_le hx₂.le, sin_zero, sqrt_eq_zero_of_nonpos]
    nlinarith
  rw [arccos_eq_pi_div_two_sub_arcsin, sin_pi_div_two_sub, cos_arcsin]

@[simp]
/-
**Real.arccos_le_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_le_pi_div_two {x} : arccos x <= π / 2 ↔ 0 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem arccos_le_pi_div_two {x} : arccos x ≤ π / 2 ↔ 0 ≤ x := by simp [arccos]

@[simp]
/-
**Real.arccos_lt_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_lt_pi_div_two {x : Real} : arccos x < π / 2 ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem arccos_lt_pi_div_two {x : ℝ} : arccos x < π / 2 ↔ 0 < x := by simp [arccos]

@[simp]
/-
**Real.arccos_le_pi_div_four** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_le_pi_div_four {x} : arccos x <= π / 4 ↔ √2 / 2 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arccos.eq_1`：∀ (x : ℝ), Real.arccos x = Real.pi / 2 - Real.arcsin x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.pi_div_four_le_arcsin`：pi_div_four_le_arcsin {x} : π / 4 <= arcsin 
x ↔ √2 / 2 <= x
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 60 条，此处仅展示前 30 条）
-/
theorem arccos_le_pi_div_four {x} : arccos x ≤ π / 4 ↔ √2 / 2 ≤ x := by
  rw [arccos, ← pi_div_four_le_arcsin]
  constructor <;>
    · intro
      linarith

@[continuity, fun_prop]
/-
**Real.continuous_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuous_arccos : Continuous arccos
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Real.continuous_arcsin`：continuous_arcsin : Continuous arcsin
-/
theorem continuous_arccos : Continuous arccos :=
  continuous_const.sub continuous_arcsin

-- The junk values for `arccos` and `sqrt` make this true even outside `[-1, 1]`.
/-
**Real.tan_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tan_arccos (x : Real) : tan (arccos x) = √(1 - x ^ 2) / x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arccos.eq_1`：∀ (x : ℝ), Real.arccos x = Real.pi / 2 - Real.arcsin x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.tan_pi_div_two_sub`：tan_pi_div_two_sub (x : Real) : tan (π / 2 - x)
 = (tan x)⁻¹
· 使用定理 `Real.tan_arcsin`：tan_arcsin (x : Real) : tan (arcsin x) = x / √(1 - x ^ 
2)
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
-/
theorem tan_arccos (x : ℝ) : tan (arccos x) = √(1 - x ^ 2) / x := by
  rw [arccos, tan_pi_div_two_sub, tan_arcsin, inv_div]

-- The junk values for `arccos` and `sqrt` make this true even for `1 < x`.
/-
**Real.arccos_eq_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arccos_eq_arcsin {x : Real} (h : 0 <= x) : arccos x = arcsin (√(1 - x ^ 2)
)
参数：h : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.arcsin_eq_of_sin_eq`：arcsin_eq_of_sin_eq {x y : Real} (h₁ : sin x =
 y) (h₂ : x in Icc (-(π / 2)) (π / 2)) : arcsin y = x
· 使用定理 `Real.sin_arccos`：sin_arccos (x : Real) : sin (arccos x) = √(1 - x ^ 2)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.neg_nonpos_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] 
[AddLeftMono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Real.arccos_nonneg`：arccos_nonneg (x : Real) : 0 <= arccos x
· 使用定理 `Real.arccos_le_pi_div_two`：arccos_le_pi_div_two {x} : arccos x <= π / 2 
↔ 0 <= x
-/
theorem arccos_eq_arcsin {x : ℝ} (h : 0 ≤ x) : arccos x = arcsin (√(1 - x ^ 2)) :=
  (arcsin_eq_of_sin_eq (sin_arccos _)
      ⟨(Left.neg_nonpos_iff.2 (div_nonneg pi_pos.le (by simp))).trans (arccos_nonneg _),
        arccos_le_pi_div_two.2 h⟩).symm

-- The junk values for `arcsin` and `sqrt` make this true even for `1 < x`.
/-
**Real.arcsin_eq_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcsin_eq_arccos {x : Real} (h : 0 <= x) : arcsin x = arccos (√(1 - x ^ 2)
)
参数：h : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.cos_arcsin`：cos_arcsin (x : Real) : cos (arcsin x) = √(1 - x ^ 2)
· 使用定理 `Real.arccos_cos`：arccos_cos {x : Real} (hx₁ : 0 <= x) (hx₂ : x <= π) : a
rccos (cos x) = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.arcsin_nonneg`：arcsin_nonneg {x : Real} : 0 <= arcsin x ↔ 0 <= x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.arcsin_le_pi_div_two`：arcsin_le_pi_div_two (x : Real) : arcsin x <=
 π / 2
· 使用定理 `div_le_self`：div_le_self (ha : 0 <= a) (hb : 1 <= b) : a / b <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem arcsin_eq_arccos {x : ℝ} (h : 0 ≤ x) : arcsin x = arccos (√(1 - x ^ 2)) := by
  rw [eq_comm, ← cos_arcsin]
  exact
    arccos_cos (arcsin_nonneg.2 h)
      ((arcsin_le_pi_div_two _).trans (div_le_self pi_pos.le one_le_two))

/-- `Real.sin` as an `OpenPartialHomeomorph` between `(-π / 2, π / 2)` and `(-1, 1)`. -/
@[simp]
/-
**Real.sinPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：sinPartialHomeomorph : OpenPartialHomeomorph Real Real where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Real.sin` as an `OpenPartialHomeomorph` between `(-π / 2, π / 2)` and `(-1, 1)`
.
-/
def sinPartialHomeomorph : OpenPartialHomeomorph ℝ ℝ where
  toFun := sin
  invFun := arcsin
  source := Ioo (-(π / 2)) (π / 2)
  target := Ioo (-1) 1
  map_source' := by grind [arcsin_lt_pi_div_two, neg_pi_div_two_lt_arcsin, arcsin_sin]
  map_target' _ hy := ⟨neg_pi_div_two_lt_arcsin.2 hy.1, arcsin_lt_pi_div_two.2 hy.2⟩
  left_inv' _ hx := arcsin_sin hx.1.le hx.2.le
  right_inv' _ hy := sin_arcsin hy.1.le hy.2.le
  open_source := isOpen_Ioo
  open_target := isOpen_Ioo
  continuousOn_toFun := continuous_sin.continuousOn
  continuousOn_invFun := continuous_arcsin.continuousOn

/-- `Real.sin` and `Real.arcsin` as a (partial) equivalence from `[-(π / 2), (π / 2)]` to
`[-1, 1]` -/
@[simp]
/-
**Real.sinPartialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：sinPartialEquiv : PartialEquiv Real Real where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Real.arcsin_mem_Icc`：arcsin_mem_Icc (x : Real) : arcsin x in Icc (-(π / 
2)) (π / 2)

--- 原说明 ---
`Real.sin` and `Real.arcsin` as a (partial) equivalence from `[-(π / 2), (π / 2)
]` to
`[-1, 1]`
-/
def sinPartialEquiv : PartialEquiv ℝ ℝ where
  toFun := sin
  invFun := arcsin
  source := Icc (-(π / 2)) (π / 2)
  target := Icc (-1) 1
  map_source' x hx := by simpa [← abs_le] using abs_sin_le_one x
  map_target' θ hθ := arcsin_mem_Icc θ
  left_inv' θ hθ := arcsin_sin (by aesop) (by aesop)
  right_inv' x hx := sin_arcsin (by aesop) (by aesop)
/-
**Real.mapsTo_sin_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mapsTo_sin_Ioo : MapsTo sin (Ioo (-(π / 2)) (π / 2)) (Ioo (-1) 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.map_source'`：∀ {α : Type u_5} {β : Type u_6} (self : Partia
lEquiv α β) ⦃x : α⦄, x ∈ self.source → ↑self x ∈ self.target
-/
theorem mapsTo_sin_Ioo : MapsTo sin (Ioo (-(π / 2)) (π / 2)) (Ioo (-1) 1) :=
  sinPartialHomeomorph.map_source'

@[simp]
/-
**Real.arcsin_image_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：arcsin_image_Icc : arcsin '' Set.Icc (-1) 1 = Set.Icc (-(π / 2)) (π / 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
-/
lemma arcsin_image_Icc : arcsin '' Set.Icc (-1) 1 = Set.Icc (-(π / 2)) (π / 2) := by
  simpa using sinPartialEquiv.symm.image_source_eq_target

/-- `Real.cos` as an `OpenPartialHomeomorph` between `(0, π)` and `(-1, 1)`. -/
@[simp]
/-
**Real.cosPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：cosPartialHomeomorph : OpenPartialHomeomorph Real Real where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Real.cos` as an `OpenPartialHomeomorph` between `(0, π)` and `(-1, 1)`.
-/
def cosPartialHomeomorph : OpenPartialHomeomorph ℝ ℝ where
  toFun := cos
  invFun := arccos
  source := Ioo 0 π
  target := Ioo (-1) 1
  map_source' := by grind [arccos_pos, arccos_lt_pi, arccos_cos]
  map_target' _ hy := ⟨arccos_pos.mpr hy.2, arccos_lt_pi.mpr hy.1⟩
  left_inv' _ hx := arccos_cos hx.1.le hx.2.le
  right_inv' _ hy := cos_arccos hy.1.le hy.2.le
  open_source := isOpen_Ioo
  open_target := isOpen_Ioo
  continuousOn_toFun := continuous_cos.continuousOn
  continuousOn_invFun := continuous_arccos.continuousOn

/-- `Real.cos` and `Real.arccos` as a (partial) equivalence from `[0, π]` to `[-1, 1]` -/
@[simps]
/-
**Real.cosPartialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：cosPartialEquiv : PartialEquiv Real Real where toFun θ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Real.cos` and `Real.arccos` as a (partial) equivalence from `[0, π]` to `[-1, 1
]`
-/
noncomputable def cosPartialEquiv : PartialEquiv ℝ ℝ where
  toFun θ := cos θ
  invFun x := arccos x
  source := Icc 0 π
  target := Icc (-1) 1
  map_source' x hx := by simpa [← abs_le] using abs_cos_le_one x
  map_target' θ hθ := ⟨arccos_nonneg θ, arccos_le_pi θ⟩
  left_inv' θ hθ := arccos_cos (by aesop) (by aesop)
  right_inv' x hx := cos_arccos (by aesop) (by aesop)
/-
**Real.mapsTo_cos_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mapsTo_cos_Ioo : MapsTo cos (Ioo 0 π) (Ioo (-1) 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.map_source'`：∀ {α : Type u_5} {β : Type u_6} (self : Partia
lEquiv α β) ⦃x : α⦄, x ∈ self.source → ↑self x ∈ self.target
-/
theorem mapsTo_cos_Ioo : MapsTo cos (Ioo 0 π) (Ioo (-1) 1) := cosPartialHomeomorph.map_source'

@[simp]
/-
**Real.arccos_image_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：arccos_image_Icc : arccos '' Icc (-1) 1 = Icc 0 π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Real.cosPartialEquiv_symm_apply`：∀ (x : ℝ), ↑Real.cosPartialEquiv.symm x
 = Real.arccos x
· 使用定理 `Real.cosPartialEquiv_target`：Real.cosPartialEquiv.target = Set.Icc (-1) 
1
· 使用定理 `Real.cosPartialEquiv_source`：Real.cosPartialEquiv.source = Set.Icc 0 Rea
l.pi
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
-/
lemma arccos_image_Icc : arccos '' Icc (-1) 1 = Icc 0 π := by
  simpa using cosPartialEquiv.symm.image_source_eq_target

end Real

open Real

/-!
### Convenience dot notation lemmas
-/

namespace Filter.Tendsto

variable {α : Type*} {l : Filter α} {x : ℝ} {f : α → ℝ}

/-
**Filter.Tendsto.arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {x : ℝ} {f : α → ℝ},   Filter.Tendsto f l 
(nhds x) → Filter.Tendsto (fun x => Real.arcsin (f x)) l (nhds (Real.arcsin x))
参数：nhds x；fun x => Real.arcsin (f x)；nhds (Real.arcsin x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Real.continuous_arcsin`：continuous_arcsin : Continuous arcsin
-/
protected theorem arcsin (h : Tendsto f l (𝓝 x)) : Tendsto (arcsin <| f ·) l (𝓝 (arcsin x)) :=
  (continuous_arcsin.tendsto _).comp h
/-
**Filter.Tendsto.arcsin_nhdsLE** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：arcsin_nhdsLE (h : Tendsto f l (𝓝[<=] x)) : Tendsto (arcsin <| f ·) l (𝓝[<
=] (arcsin x))
参数：h : Tendsto f l (𝓝[<=] x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Real.continuous_arcsin`：continuous_arcsin : Continuous arcsin
· 使用定理 `Set.MapsTo.tendsto`：Set.MapsTo.tendsto {s : Set α} {t : Set β} {f : α ->
 β} (h : MapsTo f s t) : Filter.Tendsto f (𝓟 s) (𝓟 t)
· 使用定理 `Real.monotone_arcsin`：monotone_arcsin : Monotone arcsin
-/
theorem arcsin_nhdsLE (h : Tendsto f l (𝓝[≤] x)) :
    Tendsto (arcsin <| f ·) l (𝓝[≤] (arcsin x)) := by
  refine ((continuous_arcsin.tendsto _).inf <| MapsTo.tendsto fun y hy ↦ ?_).comp h
  exact monotone_arcsin hy
/-
**Filter.Tendsto.arcsin_nhdsGE** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：arcsin_nhdsGE (h : Tendsto f l (𝓝[>=] x)) : Tendsto (arcsin <| f ·) l (𝓝[>
=] (arcsin x))
参数：h : Tendsto f l (𝓝[>=] x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Real.continuous_arcsin`：continuous_arcsin : Continuous arcsin
· 使用定理 `Set.MapsTo.tendsto`：Set.MapsTo.tendsto {s : Set α} {t : Set β} {f : α ->
 β} (h : MapsTo f s t) : Filter.Tendsto f (𝓟 s) (𝓟 t)
· 使用定理 `Real.arcsin_le_arcsin`：arcsin_le_arcsin {x y : Real} (h : x <= y) : arcs
in x <= arcsin y
-/
theorem arcsin_nhdsGE (h : Tendsto f l (𝓝[≥] x)) : Tendsto (arcsin <| f ·) l (𝓝[≥] (arcsin x)) :=
  ((continuous_arcsin.tendsto _).inf <| MapsTo.tendsto fun _ ↦ arcsin_le_arcsin).comp h
/-
**Filter.Tendsto.arccos** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {x : ℝ} {f : α → ℝ},   Filter.Tendsto f l 
(nhds x) → Filter.Tendsto (fun x => Real.arccos (f x)) l (nhds (Real.arccos x))
参数：nhds x；fun x => Real.arccos (f x)；nhds (Real.arccos x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Real.continuous_arccos`：continuous_arccos : Continuous arccos
-/
protected theorem arccos (h : Tendsto f l (𝓝 x)) : Tendsto (arccos <| f ·) l (𝓝 (arccos x)) :=
  (continuous_arccos.tendsto _).comp h
/-
**Filter.Tendsto.arccos_nhdsLE** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：arccos_nhdsLE (h : Tendsto f l (𝓝[<=] x)) : Tendsto (arccos <| f ·) l (𝓝[>
=] (arccos x))
参数：h : Tendsto f l (𝓝[<=] x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Real.continuous_arccos`：continuous_arccos : Continuous arccos
· 使用定理 `Set.MapsTo.tendsto`：Set.MapsTo.tendsto {s : Set α} {t : Set β} {f : α ->
 β} (h : MapsTo f s t) : Filter.Tendsto f (𝓟 s) (𝓟 t)
· 使用引理 `Real.arccos_le_arccos`：arccos_le_arccos {x y : Real} (hlt : x <= y) : ar
ccos y <= arccos x
-/
theorem arccos_nhdsLE (h : Tendsto f l (𝓝[≤] x)) : Tendsto (arccos <| f ·) l (𝓝[≥] (arccos x)) :=
  ((continuous_arccos.tendsto _).inf <| MapsTo.tendsto fun _ ↦ arccos_le_arccos).comp h
/-
**Filter.Tendsto.arccos_nhdsGE** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：arccos_nhdsGE (h : Tendsto f l (𝓝[>=] x)) : Tendsto (arccos <| f ·) l (𝓝[<
=] (arccos x))
参数：h : Tendsto f l (𝓝[>=] x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Real.continuous_arccos`：continuous_arccos : Continuous arccos
· 使用定理 `Set.MapsTo.tendsto`：Set.MapsTo.tendsto {s : Set α} {t : Set β} {f : α ->
 β} (h : MapsTo f s t) : Filter.Tendsto f (𝓟 s) (𝓟 t)
· 使用定理 `Real.antitone_arccos`：antitone_arccos : Antitone arccos
-/
theorem arccos_nhdsGE (h : Tendsto f l (𝓝[≥] x)) :
    Tendsto (arccos <| f ·) l (𝓝[≤] (arccos x)) := by
  refine ((continuous_arccos.tendsto _).inf <| MapsTo.tendsto fun y hy ↦ ?_).comp h
  push _ ∈ _ at hy ⊢
  exact antitone_arccos hy

end Filter.Tendsto

variable {X : Type*} [TopologicalSpace X] {f : X → ℝ} {s : Set X} {x : X}

protected nonrec theorem ContinuousWithinAt.arcsin (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (arcsin <| f ·) s x :=
  h.arcsin

protected nonrec theorem ContinuousWithinAt.arccos (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (arccos <| f ·) s x :=
  h.arccos

protected nonrec theorem ContinuousAt.arcsin (h : ContinuousAt f x) :
    ContinuousAt (arcsin <| f ·) x :=
  h.arcsin

protected nonrec theorem ContinuousAt.arccos (h : ContinuousAt f x) :
    ContinuousAt (arccos <| f ·) x :=
  h.arccos

/-
**ContinuousOn.arcsin** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {f : X → ℝ} {s : Set X},   Co
ntinuousOn f s → ContinuousOn (fun x => Real.arcsin (f x)) s
参数：fun x => Real.arcsin (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.arcsin`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
{f : X → ℝ} {s : Set X} {x : X},   ContinuousWithinAt f s x → ContinuousWithinAt
 (fun x => Real…
-/
protected theorem ContinuousOn.arcsin (h : ContinuousOn f s) : ContinuousOn (arcsin <| f ·) s :=
  fun x hx ↦ (h x hx).arcsin
/-
**ContinuousOn.arccos** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {f : X → ℝ} {s : Set X},   Co
ntinuousOn f s → ContinuousOn (fun x => Real.arccos (f x)) s
参数：fun x => Real.arccos (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.arccos`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
{f : X → ℝ} {s : Set X} {x : X},   ContinuousWithinAt f s x → ContinuousWithinAt
 (fun x => Real…
-/
protected theorem ContinuousOn.arccos (h : ContinuousOn f s) : ContinuousOn (arccos <| f ·) s :=
  fun x hx ↦ (h x hx).arccos
/-
**Continuous.arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {f : X → ℝ}, Continuous f → C
ontinuous fun x => Real.arcsin (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Real.continuous_arcsin`：continuous_arcsin : Continuous arcsin
-/
protected theorem Continuous.arcsin (h : Continuous f) : Continuous (arcsin <| f ·) :=
  continuous_arcsin.comp h
/-
**Continuous.arccos** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {f : X → ℝ}, Continuous f → C
ontinuous fun x => Real.arccos (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Real.continuous_arccos`：continuous_arccos : Continuous arccos
-/
protected theorem Continuous.arccos (h : Continuous f) : Continuous (arccos <| f ·) :=
  continuous_arccos.comp h
