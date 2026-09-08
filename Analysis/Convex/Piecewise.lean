/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Analysis.Convex.Function

/-!
# Convex and concave piecewise functions

This file proves convex and concave theorems for piecewise functions.

## Main statements

* `convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici` is the proof that the piecewise
  function `(Set.Iic e).piecewise f g` of a function `f` decreasing and convex on `Set.Iic e` and a
  function `g` increasing and convex on `Set.Ici e`, such that `f e = g e`, is convex on the
  universal set.

  This version has the boundary point included in the left-hand function.

  See `convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic` for the version with the
  boundary point included in the right-hand function.

  See concave version(s) `concaveOn_univ_piecewise_Iic_of_monotoneOn_Iic_antitoneOn_Ici`
  and `concaveOn_univ_piecewise_Ici_of_antitoneOn_Ici_monotoneOn_Iic`.
-/

public section


variable {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [LinearOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E]
  [PosSMulMono 𝕜 E] [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module 𝕜 β] [PosSMulMono 𝕜 β] {e : E} {f g : E → β}

/-- The piecewise function `(Set.Iic e).piecewise f g` of a function `f` decreasing and convex on
`Set.Iic e` and a function `g` increasing and convex on `Set.Ici e`, such that `f e = g e`, is
convex on the universal set. -/
/-
**convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici (hf : ConvexO
n 𝕜 (Set.Iic e) f) (hg : ConvexOn 𝕜 (Set.Ici e) g) (h_anti : AntitoneOn f (Set.I
ic e)) (h_mono : MonotoneOn g (Set.Ici e)) (h_eq : f e = g e) : ConvexOn 𝕜 Set.u
niv ((Set.Iic e).piecewise f g)
参数：hf : ConvexOn 𝕜 (Set.Iic e) f；hg : ConvexOn 𝕜 (Set.Ici e) g；h_anti : Antitone
On f (Set.Iic e)；h_mono : MonotoneOn g (Set.Ici e)；h_eq : f e = g e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Convex.combo_le_max`：Convex.combo_le_max (x y : E) (ha : 0 <= a) (hb : 0
 <= b) (hab : a + b = 1) : a • x + b • y <= max x y
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.notMem_Iic`：∀ {α : Type u_1} [inst : LinearOrder α] {a c : α}, c ∉ S
et.Iic a ↔ a < c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `Convex.min_le_combo`：Convex.min_le_combo (x y : E) (ha : 0 <= a) (hb : 0
 <= b) (hab : a + b = 1) : min x y <= a • x + b • y

--- 原说明 ---
The piecewise function `(Set.Iic e).piecewise f g` of a function `f` decreasing 
and convex on
`Set.Iic e` and a function `g` increasing and convex on `Set.Ici e`, such that `
f e = g e`, is
convex on the universal set.
-/
theorem convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
    (hf : ConvexOn 𝕜 (Set.Iic e) f) (hg : ConvexOn 𝕜 (Set.Ici e) g)
    (h_anti : AntitoneOn f (Set.Iic e)) (h_mono : MonotoneOn g (Set.Ici e)) (h_eq : f e = g e) :
    ConvexOn 𝕜 Set.univ ((Set.Iic e).piecewise f g) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  obtain hx | hx := le_or_gt x e <;> obtain hy | hy := le_or_gt y e
  · have hc : a • x + b • y ≤ e := (Convex.combo_le_max x y ha hb hab).trans (max_le hx hy)
    rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hx, Set.piecewise_eq_of_mem (Set.Iic e) f g hy,
      Set.piecewise_eq_of_mem (Set.Iic e) f g hc]
    exact hf.2 hx hy ha hb hab
  · rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hx,
      Set.piecewise_eq_of_notMem (Set.Iic e) f g (Set.notMem_Iic.mpr hy)]
    obtain hc | hc := le_or_gt (a • x + b • y) e
    · rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hc]
      have hc' : a • x + b • e ≤ a • x + b • y := by gcongr
      trans a • f x + b • f e
      · exact (h_anti (hc'.trans hc) hc hc').trans (hf.2 hx Set.self_mem_Iic ha hb hab)
      · rw [h_eq]
        gcongr
        exact h_mono Set.self_mem_Ici hy.le hy.le
    · rw [Set.piecewise_eq_of_notMem (Set.Iic e) f g (Set.notMem_Iic.mpr hc)]
      have hc' : a • x + b • y ≤ a • e + b • y := by gcongr
      trans a • g e + b • g y
      · exact (h_mono hc.le (hc.le.trans hc') hc').trans (hg.2 Set.self_mem_Ici hy.le ha hb hab)
      · rw [← h_eq]
        gcongr
        exact h_anti hx Set.self_mem_Iic hx
  · rw [Set.piecewise_eq_of_notMem (Set.Iic e) f g (Set.notMem_Iic.mpr hx),
      Set.piecewise_eq_of_mem (Set.Iic e) f g hy]
    obtain hc | hc := le_or_gt (a • x + b • y) e
    · rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hc]
      have hc' : a • e + b • y ≤ a • x + b • y := by gcongr
      trans a • f e + b • f y
      · exact (h_anti (hc'.trans hc) hc hc').trans (hf.2 Set.self_mem_Iic hy ha hb hab)
      · rw [h_eq]
        gcongr
        exact h_mono Set.self_mem_Ici hx.le hx.le
    · rw [Set.piecewise_eq_of_notMem (Set.Iic e) f g (Set.notMem_Iic.mpr hc)]
      have hc' : a • x + b • y ≤ a • x + b • e := by gcongr
      trans a • g x + b • g e
      · exact (h_mono hc.le (hc.le.trans hc') hc').trans (hg.2 hx.le Set.self_mem_Ici ha hb hab)
      · rw [← h_eq]
        gcongr
        exact h_anti hy Set.self_mem_Iic hy
  · have hc : e < a • x + b • y :=
        (lt_min hx hy).trans_le (Convex.min_le_combo x y ha hb hab)
    rw [(Set.Iic e).piecewise_eq_of_notMem f g (Set.notMem_Iic.mpr hx),
      (Set.Iic e).piecewise_eq_of_notMem f g (Set.notMem_Iic.mpr hy),
      (Set.Iic e).piecewise_eq_of_notMem f g (Set.notMem_Iic.mpr hc)]
    exact hg.2 hx.le hy.le ha hb hab

/-- The piecewise function `(Set.Ici e).piecewise f g` of a function `f` increasing and convex on
`Set.Ici e` and a function `g` decreasing and convex on `Set.Iic e`, such that `f e = g e`, is
convex on the universal set. -/
/-
**convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic (hf : ConvexO
n 𝕜 (Set.Ici e) f) (hg : ConvexOn 𝕜 (Set.Iic e) g) (h_mono : MonotoneOn f (Set.I
ci e)) (h_anti : AntitoneOn g (Set.Iic e)) (h_eq : f e = g e) : ConvexOn 𝕜 Set.u
niv ((Set.Ici e).piecewise f g)
参数：hf : ConvexOn 𝕜 (Set.Ici e) f；hg : ConvexOn 𝕜 (Set.Iic e) g；h_mono : Monotone
On f (Set.Ici e)；h_anti : AntitoneOn g (Set.Iic e)；h_eq : f e = g e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici`：convexOn_u
niv_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici (hf : ConvexOn 𝕜 (Set.Iic e) 
f) (hg : ConvexOn 𝕜 (Set.Ici e) g) (h_anti : Antit…

--- 原说明 ---
The piecewise function `(Set.Ici e).piecewise f g` of a function `f` increasing 
and convex on
`Set.Ici e` and a function `g` decreasing and convex on `Set.Iic e`, such that `
f e = g e`, is
convex on the universal set.
-/
theorem convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic
    (hf : ConvexOn 𝕜 (Set.Ici e) f) (hg : ConvexOn 𝕜 (Set.Iic e) g)
    (h_mono : MonotoneOn f (Set.Ici e)) (h_anti : AntitoneOn g (Set.Iic e)) (h_eq : f e = g e) :
    ConvexOn 𝕜 Set.univ ((Set.Ici e).piecewise f g) := by
  have h_piecewise_Ici_eq_piecewise_Iic :
      (Set.Ici e).piecewise f g = (Set.Iic e).piecewise g f := by
    ext x; by_cases hx : x = e
      <;> simp [Set.piecewise, @le_iff_lt_or_eq _ _ x e, ← @ite_not _ (e ≤ _), hx, h_eq]
  rw [h_piecewise_Ici_eq_piecewise_Iic]
  exact convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici hg hf h_anti h_mono h_eq.symm

/-- The piecewise function `(Set.Iic e).piecewise f g` of a function `f` increasing and concave on
`Set.Iic e` and a function `g` decreasing and concave on `Set.Ici e`, such that `f e = g e`, is
concave on the universal set. -/
/-
**concaveOn_univ_piecewise_Iic_of_monotoneOn_Iic_antitoneOn_Ici** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：concaveOn_univ_piecewise_Iic_of_monotoneOn_Iic_antitoneOn_Ici (hf : Concav
eOn 𝕜 (Set.Iic e) f) (hg : ConcaveOn 𝕜 (Set.Ici e) g) (h_mono : MonotoneOn f (Se
t.Iic e)) (h_anti : AntitoneOn g (Set.Ici e)) (h_eq : f e = g e) : ConcaveOn 𝕜 S
et.univ ((Set.Iic e).piecewise f g)
参数：hf : ConcaveOn 𝕜 (Set.Iic e) f；hg : ConcaveOn 𝕜 (Set.Ici e) g；h_mono : Monoto
neOn f (Set.Iic e)；h_anti : AntitoneOn g (Set.Ici e)；h_eq : f e = g e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_convexOn_iff`：neg_convexOn_iff : ConvexOn 𝕜 s (-f) ↔ ConcaveOn 𝕜 s f
· 使用定理 `Set.piecewise_neg`：∀ {I : Type u} {f : I → Type v} [inst : (i : I) → Neg
 (f i)] (s : Set I) [inst_1 : (i : I) → Decidable (i ∈ s)]   (f₁ g₁ : (i : I) → 
f i), s…
· 使用定理 `convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici`：convexOn_u
niv_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici (hf : ConvexOn 𝕜 (Set.Iic e) 
f) (hg : ConvexOn 𝕜 (Set.Ici e) g) (h_anti : Antit…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `MonotoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `AntitoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b

--- 原说明 ---
The piecewise function `(Set.Iic e).piecewise f g` of a function `f` increasing 
and concave on
`Set.Iic e` and a function `g` decreasing and concave on `Set.Ici e`, such that 
`f e = g e`, is
concave on the universal set.
-/
theorem concaveOn_univ_piecewise_Iic_of_monotoneOn_Iic_antitoneOn_Ici
    (hf : ConcaveOn 𝕜 (Set.Iic e) f) (hg : ConcaveOn 𝕜 (Set.Ici e) g)
    (h_mono : MonotoneOn f (Set.Iic e)) (h_anti : AntitoneOn g (Set.Ici e)) (h_eq : f e = g e) :
    ConcaveOn 𝕜 Set.univ ((Set.Iic e).piecewise f g) := by
  rw [← neg_convexOn_iff, ← Set.piecewise_neg]
  exact convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
    hf.neg hg.neg h_mono.neg h_anti.neg (neg_inj.mpr h_eq)

/-- The piecewise function `(Set.Ici e).piecewise f g` of a function `f` decreasing and concave on
`Set.Ici e` and a function `g` increasing and concave on `Set.Iic e`, such that `f e = g e`, is
concave on the universal set. -/
/-
**concaveOn_univ_piecewise_Ici_of_antitoneOn_Ici_monotoneOn_Iic** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：concaveOn_univ_piecewise_Ici_of_antitoneOn_Ici_monotoneOn_Iic (hf : Concav
eOn 𝕜 (Set.Ici e) f) (hg : ConcaveOn 𝕜 (Set.Iic e) g) (h_anti : AntitoneOn f (Se
t.Ici e)) (h_mono : MonotoneOn g (Set.Iic e)) (h_eq : f e = g e) : ConcaveOn 𝕜 S
et.univ ((Set.Ici e).piecewise f g)
参数：hf : ConcaveOn 𝕜 (Set.Ici e) f；hg : ConcaveOn 𝕜 (Set.Iic e) g；h_anti : Antito
neOn f (Set.Ici e)；h_mono : MonotoneOn g (Set.Iic e)；h_eq : f e = g e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_convexOn_iff`：neg_convexOn_iff : ConvexOn 𝕜 s (-f) ↔ ConcaveOn 𝕜 s f
· 使用定理 `Set.piecewise_neg`：∀ {I : Type u} {f : I → Type v} [inst : (i : I) → Neg
 (f i)] (s : Set I) [inst_1 : (i : I) → Decidable (i ∈ s)]   (f₁ g₁ : (i : I) → 
f i), s…
· 使用定理 `convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic`：convexOn_u
niv_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic (hf : ConvexOn 𝕜 (Set.Ici e) 
f) (hg : ConvexOn 𝕜 (Set.Iic e) g) (h_mono : Monot…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `AntitoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MonotoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b

--- 原说明 ---
The piecewise function `(Set.Ici e).piecewise f g` of a function `f` decreasing 
and concave on
`Set.Ici e` and a function `g` increasing and concave on `Set.Iic e`, such that 
`f e = g e`, is
concave on the universal set.
-/
theorem concaveOn_univ_piecewise_Ici_of_antitoneOn_Ici_monotoneOn_Iic
    (hf : ConcaveOn 𝕜 (Set.Ici e) f) (hg : ConcaveOn 𝕜 (Set.Iic e) g)
    (h_anti : AntitoneOn f (Set.Ici e)) (h_mono : MonotoneOn g (Set.Iic e)) (h_eq : f e = g e) :
    ConcaveOn 𝕜 Set.univ ((Set.Ici e).piecewise f g) := by
  rw [← neg_convexOn_iff, ← Set.piecewise_neg]
  exact convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic
    hf.neg hg.neg h_anti.neg h_mono.neg (neg_inj.mpr h_eq)
