/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monovary
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic.FieldSimp

/-!
# Product of convex functions

This file proves that the product of convex functions is convex, provided they monovary.

As corollaries, we also prove that `x ↦ x ^ n` is convex
* `Even.convexOn_pow`: for even `n : ℕ`.
* `convexOn_pow`: over $[0, +∞)$ for `n : ℕ`.
* `convexOn_zpow`: over $(0, +∞)$ For `n : ℤ`.
-/

public section

open Set

variable {𝕜 E F G : Type*}

section LinearOrderedCommRing
variable [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [CommRing E] [LinearOrder E] [IsStrictOrderedRing E]
  [AddCommGroup F] [LinearOrder F] [IsOrderedAddMonoid F]
  [AddCommGroup G] [Module 𝕜 G]
  [Module 𝕜 E] [Module 𝕜 F] [Module E F] [IsScalarTower 𝕜 E F] [SMulCommClass 𝕜 E F]
  [IsOrderedModule 𝕜 F] [IsStrictOrderedModule E F] {s : Set G} {f : G → E} {g : G → F}

/-
**ConvexOn.smul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.smul' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : forall ⦃
x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x) (hfg : MonovaryOn
 f g s) : ConvexOn 𝕜 s (f • g)
参数：hf : ConvexOn 𝕜 s f；hg : ConvexOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> 0 <= f x；
hg₀ : forall ⦃x⦄, x in s -> 0 <= g x；hfg : MonovaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `smul_le_smul`：smul_le_smul [PosSMulMono α β] [SMulPosMono α β] (ha : a₁ 
<= a₂) (hb : b₁ <= b₂) (h₁ : 0 <= a₁) (h₂ : 0 <= b₂) : a₁ • b₁ <= a₂ • b₂
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_smul_smul_comm`：smul_smul_smul_comm [SMul α β] [SMul α γ] [SMul β δ
] [SMul α δ] [SMul γ δ] [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommCla
ss β γ δ]…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `MonovaryOn.smul_add_smul_le_smul_add_smul`：∀ {ι : Type u_1} {α : Type u_
2} {β : Type u_3} [inst : Ring α] [inst_1 : LinearOrder α] [IsStrictOrderedRing 
α]   [inst_3 : AddCommGroup β] …
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
（共 35 条，此处仅展示前 30 条）
-/
lemma ConvexOn.smul' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : MonovaryOn f g s) : ConvexOn 𝕜 s (f • g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  dsimp
  refine
    (smul_le_smul (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab) (hf₀ <| hf.1 hx hy ha hb hab) <|
      add_nonneg (smul_nonneg ha <| hg₀ hx) <| smul_nonneg hb <| hg₀ hy).trans ?_
  calc
      _ = (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g y + f y • g x) := ?_
    _ ≤ (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g x + f y • g y) := by
        gcongr _ + (a * b) • ?_; exact hfg.smul_add_smul_le_smul_add_smul hx hy
    _ = (a * (a + b)) • (f x • g x) + (b * (a + b)) • (f y • g y) := by
        simp only [mul_add, add_smul, smul_add, mul_comm _ a]; abel
    _ = _ := by simp_rw [hab, mul_one]
  simp only [add_smul, smul_add]
  rw [← smul_smul_smul_comm a, ← smul_smul_smul_comm b, ← smul_smul_smul_comm a b,
    ← smul_smul_smul_comm b b, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_comm b,
    add_comm _ ((b * b) • f y • g y), add_add_add_comm, add_comm ((a * b) • f y • g x)]
/-
**ConcaveOn.smul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.smul' [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜 s f) (hg : Concave
On 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> 0 
<= g x) (hfg : AntivaryOn f g s) : ConcaveOn 𝕜 s (f • g)
参数：hf : ConcaveOn 𝕜 s f；hg : ConcaveOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> 0 <= f 
x；hg₀ : forall ⦃x⦄, x in s -> 0 <= g x；hfg : AntivaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用引理 `smul_le_smul`：smul_le_smul [PosSMulMono α β] [SMulPosMono α β] (ha : a₁ 
<= a₂) (hb : b₁ <= b₂) (h₁ : 0 <= a₁) (h₂ : 0 <= b₂) : a₁ • b₁ <= a₂ • b₂
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `_private.Mathlib.Analysis.Convex.Mul.0.ConcaveOn.smul'._abel_1_1`：∀ {𝕜 :
 Type u_2} {E : Type u_3} {F : Type u_1} {G : Type u_4} [inst : CommRing 𝕜] [ins
t_1 : CommRing E]   [inst_2 : AddCommGroup F] [inst_3 …
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `AntivaryOn.smul_add_smul_le_smul_add_smul`：∀ {ι : Type u_1} {α : Type u_
2} {β : Type u_3} [inst : Ring α] [inst_1 : LinearOrder α] [IsStrictOrderedRing 
α]   [inst_3 : AddCommGroup β] …
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
（共 36 条，此处仅展示前 30 条）
-/
lemma ConcaveOn.smul' [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  dsimp
  refine (smul_le_smul (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
    (add_nonneg (smul_nonneg ha <| hf₀ hx) <| smul_nonneg hb <| hf₀ hy)
    (hg₀ <| hf.1 hx hy ha hb hab)).trans' ?_
  calc a • f x • g x + b • f y • g y
        = (a * (a + b)) • (f x • g x) + (b * (a + b)) • (f y • g y) := by simp_rw [hab, mul_one]
    _ = (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g x + f y • g y) := by
        simp only [mul_add, add_smul, smul_add, mul_comm _ a]; abel
    _ ≤ (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g y + f y • g x) := by
        gcongr _ + (a * b) • ?_; exact hfg.smul_add_smul_le_smul_add_smul hx hy
    _ = _ := ?_
  simp only [add_smul, smul_add]
  rw [← smul_smul_smul_comm a, ← smul_smul_smul_comm b, ← smul_smul_smul_comm a b,
    ← smul_smul_smul_comm b b, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_comm b a,
    add_comm ((a * b) • f x • g y), add_comm ((a * b) • f x • g y), add_add_add_comm]
/-
**ConvexOn.smul''** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.smul'' [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 s f) (hg : ConvexOn
 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄, x in s -> g x 
<= 0) (hfg : AntivaryOn f g s) : ConcaveOn 𝕜 s (f • g)
参数：hf : ConvexOn 𝕜 s f；hg : ConvexOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> f x <= 0；
hg₀ : forall ⦃x⦄, x in s -> g x <= 0；hfg : AntivaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul_neg`：neg_smul_neg : -r • -x = r • x
· 使用引理 `ConcaveOn.smul'`：ConcaveOn.smul' [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜
 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : foral
l ⦃x⦄…
· 使用定理 `ConvexOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Sem
iring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCom
mG…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AntivaryOn.neg`：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : A
ddCommGroup α] [inst_1 : PartialOrder α] [IsOrderedAddMonoid α]   [inst_3 : AddC
ommG…
-/
lemma ConvexOn.smul'' [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := by
  rw [← neg_smul_neg]
  exact hf.neg.smul' hg.neg (fun x hx ↦ neg_nonneg.2 <| hf₀ hx) (fun x hx ↦ neg_nonneg.2 <| hg₀ hx)
    hfg.neg
/-
**ConcaveOn.smul''** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.smul'' (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : fora
ll ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄, x in s -> g x <= 0) (hfg : Monova
ryOn f g s) : ConvexOn 𝕜 s (f • g)
参数：hf : ConcaveOn 𝕜 s f；hg : ConcaveOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> f x <= 
0；hg₀ : forall ⦃x⦄, x in s -> g x <= 0；hfg : MonovaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul_neg`：neg_smul_neg : -r • -x = r • x
· 使用引理 `ConvexOn.smul'`：ConvexOn.smul' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s 
g) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x)
 (hf…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MonovaryOn.neg`：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : A
ddCommGroup α] [inst_1 : PartialOrder α] [IsOrderedAddMonoid α]   [inst_3 : AddC
ommG…
-/
lemma ConcaveOn.smul'' (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : MonovaryOn f g s) : ConvexOn 𝕜 s (f • g) := by
  rw [← neg_smul_neg]
  exact hf.neg.smul' hg.neg (fun x hx ↦ neg_nonneg.2 <| hf₀ hx) (fun x hx ↦ neg_nonneg.2 <| hg₀ hx)
    hfg.neg
/-
**ConvexOn.smul_concaveOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.smul_concaveOn (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ 
: forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> g x <= 0) (hfg : 
AntivaryOn f g s) : ConcaveOn 𝕜 s (f • g)
参数：hf : ConvexOn 𝕜 s f；hg : ConcaveOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> 0 <= f x
；hg₀ : forall ⦃x⦄, x in s -> g x <= 0；hfg : AntivaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_convexOn_iff`：neg_convexOn_iff : ConvexOn 𝕜 s (-f) ↔ ConcaveOn 𝕜 s f
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `ConvexOn.smul'`：ConvexOn.smul' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s 
g) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x)
 (hf…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AntivaryOn.neg_right`：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [in
st : PartialOrder α] [inst_1 : AddCommGroup β]   [inst_2 : PartialOrder β] [IsOr
deredAddMo…
-/
lemma ConvexOn.smul_concaveOn (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := by
  rw [← neg_convexOn_iff, ← smul_neg]
  exact hf.smul' hg.neg hf₀ (fun x hx ↦ neg_nonneg.2 <| hg₀ hx) hfg.neg_right
/-
**ConcaveOn.smul_convexOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.smul_convexOn [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜 s f) (hg :
 ConvexOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in 
s -> g x <= 0) (hfg : MonovaryOn f g s) : ConvexOn 𝕜 s (f • g)
参数：hf : ConcaveOn 𝕜 s f；hg : ConvexOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> 0 <= f x
；hg₀ : forall ⦃x⦄, x in s -> g x <= 0；hfg : MonovaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_concaveOn_iff`：neg_concaveOn_iff : ConcaveOn 𝕜 s (-f) ↔ ConvexOn 𝕜 s
 f
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `ConcaveOn.smul'`：ConcaveOn.smul' [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜
 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : foral
l ⦃x⦄…
· 使用定理 `ConvexOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Sem
iring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCom
mG…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MonovaryOn.neg_right`：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [in
st : PartialOrder α] [inst_1 : AddCommGroup β]   [inst_2 : PartialOrder β] [IsOr
deredAddMo…
-/
lemma ConcaveOn.smul_convexOn [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f • g) := by
  rw [← neg_concaveOn_iff, ← smul_neg]
  exact hf.smul' hg.neg hf₀ (fun x hx ↦ neg_nonneg.2 <| hg₀ hx) hfg.neg_right
/-
**ConvexOn.smul_concaveOn'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.smul_concaveOn' [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 s f) (hg :
 ConcaveOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄, x in
 s -> 0 <= g x) (hfg : MonovaryOn f g s) : ConvexOn 𝕜 s (f • g)
参数：hf : ConvexOn 𝕜 s f；hg : ConcaveOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> f x <= 0
；hg₀ : forall ⦃x⦄, x in s -> 0 <= g x；hfg : MonovaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_concaveOn_iff`：neg_concaveOn_iff : ConcaveOn 𝕜 s (-f) ↔ ConvexOn 𝕜 s
 f
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `ConvexOn.smul''`：ConvexOn.smul'' [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 
s f) (hg : ConvexOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall 
⦃x⦄, …
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MonovaryOn.neg_right`：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [in
st : PartialOrder α] [inst_1 : AddCommGroup β]   [inst_2 : PartialOrder β] [IsOr
deredAddMo…
-/
lemma ConvexOn.smul_concaveOn' [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f • g) := by
  rw [← neg_concaveOn_iff, ← smul_neg]
  exact hf.smul'' hg.neg hf₀ (fun x hx ↦ neg_nonpos.2 <| hg₀ hx) hfg.neg_right
/-
**ConcaveOn.smul_convexOn'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.smul_convexOn' (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀
 : forall ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x) (hfg :
 AntivaryOn f g s) : ConcaveOn 𝕜 s (f • g)
参数：hf : ConcaveOn 𝕜 s f；hg : ConvexOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> f x <= 0
；hg₀ : forall ⦃x⦄, x in s -> 0 <= g x；hfg : AntivaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_convexOn_iff`：neg_convexOn_iff : ConvexOn 𝕜 s (-f) ↔ ConcaveOn 𝕜 s f
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `ConcaveOn.smul''`：ConcaveOn.smul'' (hf : ConcaveOn 𝕜 s f) (hg : ConcaveO
n 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄, x in s -> g x
 <= 0)…
· 使用定理 `ConvexOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Sem
iring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCom
mG…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AntivaryOn.neg_right`：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [in
st : PartialOrder α] [inst_1 : AddCommGroup β]   [inst_2 : PartialOrder β] [IsOr
deredAddMo…
-/
lemma ConcaveOn.smul_convexOn' (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := by
  rw [← neg_convexOn_iff, ← smul_neg]
  exact hf.smul'' hg.neg hf₀ (fun x hx ↦ neg_nonpos.2 <| hg₀ hx) hfg.neg_right

variable [IsOrderedModule 𝕜 E] [IsScalarTower 𝕜 E E] [SMulCommClass 𝕜 E E] {f g : G → E}
/-
**ConvexOn.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.mul (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : forall ⦃x⦄
, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x) (hfg : MonovaryOn f
 g s) : ConvexOn 𝕜 s (f * g)
参数：hf : ConvexOn 𝕜 s f；hg : ConvexOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> 0 <= f x；
hg₀ : forall ⦃x⦄, x in s -> 0 <= g x；hfg : MonovaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.smul'`：ConvexOn.smul' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s 
g) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x)
 (hf…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
-/
lemma ConvexOn.mul (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul' hg hf₀ hg₀ hfg
/-
**ConcaveOn.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.mul (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : forall 
⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x) (hfg : AntivaryO
n f g s) : ConcaveOn 𝕜 s (f * g)
参数：hf : ConcaveOn 𝕜 s f；hg : ConcaveOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> 0 <= f 
x；hg₀ : forall ⦃x⦄, x in s -> 0 <= g x；hfg : AntivaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConcaveOn.smul'`：ConcaveOn.smul' [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜
 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : foral
l ⦃x⦄…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
-/
lemma ConcaveOn.mul (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f * g) := hf.smul' hg hf₀ hg₀ hfg
/-
**ConvexOn.mul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.mul' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : forall ⦃x
⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄, x in s -> g x <= 0) (hfg : AntivaryOn 
f g s) : ConcaveOn 𝕜 s (f * g)
参数：hf : ConvexOn 𝕜 s f；hg : ConvexOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> f x <= 0；
hg₀ : forall ⦃x⦄, x in s -> g x <= 0；hfg : AntivaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.smul''`：ConvexOn.smul'' [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 
s f) (hg : ConvexOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall 
⦃x⦄, …
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
-/
lemma ConvexOn.mul' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f * g) := hf.smul'' hg hf₀ hg₀ hfg
/-
**ConcaveOn.mul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.mul' (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : forall
 ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄, x in s -> g x <= 0) (hfg : Monovary
On f g s) : ConvexOn 𝕜 s (f * g)
参数：hf : ConcaveOn 𝕜 s f；hg : ConcaveOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> f x <= 
0；hg₀ : forall ⦃x⦄, x in s -> g x <= 0；hfg : MonovaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConcaveOn.smul''`：ConcaveOn.smul'' (hf : ConcaveOn 𝕜 s f) (hg : ConcaveO
n 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄, x in s -> g x
 <= 0)…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
-/
lemma ConcaveOn.mul' (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul'' hg hf₀ hg₀ hfg
/-
**ConvexOn.mul_concaveOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.mul_concaveOn (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ :
 forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> g x <= 0) (hfg : A
ntivaryOn f g s) : ConcaveOn 𝕜 s (f * g)
参数：hf : ConvexOn 𝕜 s f；hg : ConcaveOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> 0 <= f x
；hg₀ : forall ⦃x⦄, x in s -> g x <= 0；hfg : AntivaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.smul_concaveOn`：ConvexOn.smul_concaveOn (hf : ConvexOn 𝕜 s f) (
hg : ConcaveOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, 
x in s -> g x…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
-/
lemma ConvexOn.mul_concaveOn (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f * g) := hf.smul_concaveOn hg hf₀ hg₀ hfg
/-
**ConcaveOn.mul_convexOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.mul_convexOn (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ :
 forall ⦃x⦄, x in s -> 0 <= f x) (hg₀ : forall ⦃x⦄, x in s -> g x <= 0) (hfg : M
onovaryOn f g s) : ConvexOn 𝕜 s (f * g)
参数：hf : ConcaveOn 𝕜 s f；hg : ConvexOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> 0 <= f x
；hg₀ : forall ⦃x⦄, x in s -> g x <= 0；hfg : MonovaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConcaveOn.smul_convexOn`：ConcaveOn.smul_convexOn [IsOrderedModule 𝕜 E] (
hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> 0 <= f 
x) (hg₀ : for…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
-/
lemma ConcaveOn.mul_convexOn (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul_convexOn hg hf₀ hg₀ hfg
/-
**ConvexOn.mul_concaveOn'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.mul_concaveOn' (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ 
: forall ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x) (hfg : 
MonovaryOn f g s) : ConvexOn 𝕜 s (f * g)
参数：hf : ConvexOn 𝕜 s f；hg : ConcaveOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> f x <= 0
；hg₀ : forall ⦃x⦄, x in s -> 0 <= g x；hfg : MonovaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.smul_concaveOn'`：ConvexOn.smul_concaveOn' [IsOrderedModule 𝕜 E]
 (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> f x <
= 0) (hg₀ : fo…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
-/
lemma ConvexOn.mul_concaveOn' (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul_concaveOn' hg hf₀ hg₀ hfg
/-
**ConcaveOn.mul_convexOn'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.mul_convexOn' (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ 
: forall ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄, x in s -> 0 <= g x) (hfg : 
AntivaryOn f g s) : ConcaveOn 𝕜 s (f • g)
参数：hf : ConcaveOn 𝕜 s f；hg : ConvexOn 𝕜 s g；hf₀ : forall ⦃x⦄, x in s -> f x <= 0
；hg₀ : forall ⦃x⦄, x in s -> 0 <= g x；hfg : AntivaryOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConcaveOn.smul_convexOn'`：ConcaveOn.smul_convexOn' (hf : ConcaveOn 𝕜 s f
) (hg : ConvexOn 𝕜 s g) (hf₀ : forall ⦃x⦄, x in s -> f x <= 0) (hg₀ : forall ⦃x⦄
, x in s -> 0 …
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
-/
lemma ConcaveOn.mul_convexOn' (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := hf.smul_convexOn' hg hf₀ hg₀ hfg
/-
**ConvexOn.pow** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {G : Type u_4} [inst : CommRing 𝕜] [inst_1
 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : CommRing E] [inst_4 : Line
arOrder E] [IsStrictOrderedRing E] [inst_6 : AddCommGroup G]   [inst_7 : _root_.
Module 𝕜 G] [inst_8 : _root_.Module 𝕜 E] {s : Set G} [IsOrderedModule 𝕜 E] [IsSc
alarTower 𝕜 E E]   [SMulCommClass 𝕜 E E] {f : G → E}, ConvexOn 𝕜 s f → (∀ ⦃x : G
⦄, x ∈ s → 0 ≤ f x) → ∀ (n : ℕ), ConvexOn 𝕜 s (f ^ n)
参数：∀ ⦃x : G⦄, x ∈ s → 0 ≤ f x；n : ℕ；f ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ConvexOn.pow (hf : ConvexOn 𝕜 s f) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) :
    ∀ n, ConvexOn 𝕜 s (f ^ n)
  | 0 => by simpa using! convexOn_const 1 hf.1
  | n + 1 => by
    rw [pow_succ']
    exact hf.mul (hf.pow hf₀ _) hf₀ (fun x hx ↦ pow_nonneg (hf₀ hx) _) <|
      (monovaryOn_self f s).pow_right₀ hf₀ n

/-- `x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n`. -/
/-
**convexOn_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：convexOn_pow : forall n, ConvexOn 𝕜 (Ici 0) fun x : 𝕜 => x ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.pow`：∀ {𝕜 : Type u_1} {E : Type u_2} {G : Type u_4} [inst : Com
mRing 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : CommRing E
] …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `convexOn_id`：convexOn_id {s : Set β} (hs : Convex 𝕜 s) : ConvexOn 𝕜 s _r
oot_.id
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …

--- 原说明 ---
`x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n`.
-/
lemma convexOn_pow : ∀ n, ConvexOn 𝕜 (Ici 0) fun x : 𝕜 ↦ x ^ n :=
  (convexOn_id <| convex_Ici _).pow fun _ ↦ id

/-- `x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even. -/
/-
**Even.convexOn_pow** 是 Mathlib 中的一个定理，位于命名空间 `Even`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : CommRing 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrd
eredRing 𝕜] {n : ℕ},   Even n → ConvexOn 𝕜 Set.univ fun x => x ^ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `ConvexOn.pow`：∀ {𝕜 : Type u_1} {E : Type u_2} {G : Type u_4} [inst : Com
mRing 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : CommRing E
] …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 73 条，此处仅展示前 30 条）

--- 原说明 ---
`x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even.
-/
protected lemma Even.convexOn_pow {n : ℕ} (hn : Even n) : ConvexOn 𝕜 univ fun x : 𝕜 ↦ x ^ n := by
  obtain ⟨n, rfl⟩ := hn
  simp_rw [← two_mul, pow_mul]
  refine ConvexOn.pow ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ sub_nonneg.1 ?_⟩
    (fun _ _ ↦ by positivity) _
  calc
    (0 : 𝕜) ≤ (a * b) * (x - y) ^ 2 := by positivity
    _ = _ := by obtain rfl := eq_sub_of_add_eq hab; simp only [smul_eq_mul]; ring

end LinearOrderedCommRing

section LinearOrderedField
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

open Int in
/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m`. -/
/-
**convexOn_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：convexOn_zpow : forall n : Int, ConvexOn 𝕜 (Ioi 0) fun x : 𝕜 => x ^ n | (n
 : Nat) => by simp_rw [zpow_natCast] exact (convexOn_pow n).subset Ioi_subset_Ic
i_self (convex_Ioi _) | -[n+1] => by simp_rw [zpow_negSucc, ← inv_pow] refine (c
onvexOn_iff_forall_pos.2 ⟨convex_Ioi _, ?_⟩).pow (fun x (hx : 0 < x) => by posit
ivity) _ rintro x (hx : 0 < x) y (hy : 0 < y) a b ha hb hab simp only [smul_eq_m
ul] field_simp have H : 0 <= a * b * (x - y) ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `ConvexOn.subset`：ConvexOn.subset {t : Set E} (hf : ConvexOn 𝕜 t f) (hst 
: s subseteq t) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s f
· 使用引理 `convexOn_pow`：convexOn_pow : forall n, ConvexOn 𝕜 (Ici 0) fun x : 𝕜 => x
 ^ n
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
· 使用定理 `convex_Ioi`：convex_Ioi (r : β) : Convex 𝕜 (Ioi r)
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `ConvexOn.pow`：∀ {𝕜 : Type u_1} {E : Type u_2} {G : Type u_4} [inst : Com
mRing 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : CommRing E
] …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `convexOn_iff_forall_pos`：convexOn_iff_forall_pos {s : Set E} {f : E -> β
} : ConvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> fo
rall ⦃a b : 𝕜…
· 使用定理 `Mathlib.Tactic.FieldSimp.le_eq_cancel_le`：le_eq_cancel_le {M : Type*} [M
onoidWithZero M] [PartialOrder M] [PosMulMono M] [PosMulReflectLE M] {e₁ e₂ f₁ f
₂ L : M} (H₁ : e₁ = L * f₁) (H…
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
（共 115 条，此处仅展示前 30 条）

--- 原说明 ---
`x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m`.
-/
lemma convexOn_zpow : ∀ n : ℤ, ConvexOn 𝕜 (Ioi 0) fun x : 𝕜 ↦ x ^ n
  | (n : ℕ) => by
    simp_rw [zpow_natCast]
    exact (convexOn_pow n).subset Ioi_subset_Ici_self (convex_Ioi _)
  | -[n+1] => by
    simp_rw [zpow_negSucc, ← inv_pow]
    refine (convexOn_iff_forall_pos.2 ⟨convex_Ioi _, ?_⟩).pow (fun x (hx : 0 < x) ↦ by positivity) _
    rintro x (hx : 0 < x) y (hy : 0 < y) a b ha hb hab
    simp only [smul_eq_mul]
    field_simp
    have H : 0 ≤ a * b * (x - y) ^ 2 := by positivity
    linear_combination H - x * y * (a + b + 1) * hab

end LinearOrderedField

