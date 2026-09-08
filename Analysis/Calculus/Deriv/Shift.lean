/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Yaël Dillies
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
### Invariance of the derivative under translation

We show that if a function `f` has derivative `f'` at a point `a + x`, then `f (a + ·)`
has derivative `f'` at `x`. Similarly for `x + a`.
-/

public section

open scoped Pointwise

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : 𝕜 → F} {f' : F}

/-- Translation in the domain does not change the derivative. -/
/-
**HasDerivAt.comp_const_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasDerivAt.comp_const_add (a x : 𝕜) (hf : HasDerivAt f f' (a + x)) : HasDe
rivAt (fun x => f (a + x)) f' x
参数：a x : 𝕜；hf : HasDerivAt f f' (a + x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasDerivAt.scomp`：HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : 
HasDerivAt h h' x) : HasDerivAt (g₁ ∘ h) (h' • g₁') x
· 使用定理 `HasDerivAt.const_add`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `hasDerivAt_id'`：hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x

--- 原说明 ---
Translation in the domain does not change the derivative.
-/
lemma HasDerivAt.comp_const_add (a x : 𝕜) (hf : HasDerivAt f f' (a + x)) :
    HasDerivAt (fun x ↦ f (a + x)) f' x := by
  simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf <| hasDerivAt_id' x |>.const_add a

/-- Translation in the domain does not change the derivative. -/
/-
**HasDerivAt.comp_add_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasDerivAt.comp_add_const (x a : 𝕜) (hf : HasDerivAt f f' (x + a)) : HasDe
rivAt (fun x => f (x + a)) f' x
参数：x a : 𝕜；hf : HasDerivAt f f' (x + a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasDerivAt.scomp`：HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : 
HasDerivAt h h' x) : HasDerivAt (g₁ ∘ h) (h' • g₁') x
· 使用定理 `HasDerivAt.add_const`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `hasDerivAt_id'`：hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x

--- 原说明 ---
Translation in the domain does not change the derivative.
-/
lemma HasDerivAt.comp_add_const (x a : 𝕜) (hf : HasDerivAt f f' (x + a)) :
    HasDerivAt (fun x ↦ f (x + a)) f' x := by
  simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf <| hasDerivAt_id' x |>.add_const a

/-- Translation in the domain does not change the derivative. -/
/-
**HasDerivAt.comp_const_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasDerivAt.comp_const_sub (a x : 𝕜) (hf : HasDerivAt f f' (a - x)) : HasDe
rivAt (fun x => f (a - x)) (-f') x
参数：a x : 𝕜；hf : HasDerivAt f f' (a - x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasDerivAt.scomp`：HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : 
HasDerivAt h h' x) : HasDerivAt (g₁ ∘ h) (h' • g₁') x
· 使用定理 `HasDerivAt.const_sub`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `hasDerivAt_id'`：hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x

--- 原说明 ---
Translation in the domain does not change the derivative.
-/
lemma HasDerivAt.comp_const_sub (a x : 𝕜) (hf : HasDerivAt f f' (a - x)) :
    HasDerivAt (fun x ↦ f (a - x)) (-f') x := by
  simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf <| hasDerivAt_id' x |>.const_sub a

/-- Translation in the domain does not change the derivative. -/
/-
**HasDerivAt.comp_sub_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasDerivAt.comp_sub_const (x a : 𝕜) (hf : HasDerivAt f f' (x - a)) : HasDe
rivAt (fun x => f (x - a)) f' x
参数：x a : 𝕜；hf : HasDerivAt f f' (x - a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasDerivAt.scomp`：HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : 
HasDerivAt h h' x) : HasDerivAt (g₁ ∘ h) (h' • g₁') x
· 使用定理 `HasDerivAt.sub_const`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `hasDerivAt_id'`：hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x

--- 原说明 ---
Translation in the domain does not change the derivative.
-/
lemma HasDerivAt.comp_sub_const (x a : 𝕜) (hf : HasDerivAt f f' (x - a)) :
    HasDerivAt (fun x ↦ f (x - a)) f' x := by
  simpa [Function.comp_def] using HasDerivAt.scomp (𝕜 := 𝕜) x hf <| hasDerivAt_id' x |>.sub_const a

variable (f)
variable (a : 𝕜) (s : Set 𝕜) (x : 𝕜)
/-
**derivWithin_comp_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：derivWithin_comp_neg : derivWithin (f <| -·) s x = -derivWithin f (-s) (-x
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `Set.neg_smul_set`：neg_smul_set : -a • t = -(a • t)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `derivWithin_comp_mul_left`：derivWithin_comp_mul_left : derivWithin (f <|
 c * ·) s x = c • derivWithin f (c • s) (c * x)
-/
lemma derivWithin_comp_neg : derivWithin (f <| -·) s x = -derivWithin f (-s) (-x) := by
  simpa using derivWithin_comp_mul_left (-1) f s x

/-- The derivative of `x ↦ f (-x)` at `a` is the negative of the derivative of `f` at `-a`. -/
/-
**deriv_comp_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_comp_neg : deriv (fun x => f (-x)) x = -deriv f (-x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `deriv_comp_mul_left`：deriv_comp_mul_left : deriv (f <| c * ·) x = c • de
riv f (c * x)

--- 原说明 ---
The derivative of `x ↦ f (-x)` at `a` is the negative of the derivative of `f` a
t `-a`.
-/
lemma deriv_comp_neg : deriv (fun x ↦ f (-x)) x = -deriv f (-x) := by
  simpa using deriv_comp_mul_left (-1) f x

/-- Translation in the domain does not change the derivative. -/
/-
**derivWithin_comp_const_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：derivWithin_comp_const_add : derivWithin (f <| a + ·) s x = derivWithin f 
(a +ᵥ s) (a + x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_comp_add_left`：fderivWithin_comp_add_left (a : E) : fderivW
ithin 𝕜 (fun x => f (a + x)) s x = fderivWithin 𝕜 f (a +ᵥ s) (a + x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Translation in the domain does not change the derivative.
-/
lemma derivWithin_comp_const_add :
    derivWithin (f <| a + ·) s x = derivWithin f (a +ᵥ s) (a + x) := by
  simp only [derivWithin, fderivWithin_comp_add_left]

/-- Translation in the domain does not change the derivative. -/
/-
**deriv_comp_const_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_comp_const_add : deriv (fun x => f (a + x)) x = deriv f (a + x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_comp_add_left`：fderiv_comp_add_left (a : E) : fderiv 𝕜 (fun x => 
f (a + x)) x = fderiv 𝕜 f (a + x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Translation in the domain does not change the derivative.
-/
lemma deriv_comp_const_add : deriv (fun x ↦ f (a + x)) x = deriv f (a + x) := by
  simp only [deriv, fderiv_comp_add_left]

/-- Translation in the domain does not change the derivative. -/
/-
**derivWithin_comp_add_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：derivWithin_comp_add_const : derivWithin (f <| · + a) s x = derivWithin f 
(a +ᵥ s) (x + a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_comp_add_right`：fderivWithin_comp_add_right (a : E) : fderi
vWithin 𝕜 (fun x => f (x + a)) s x = fderivWithin 𝕜 f (a +ᵥ s) (x + a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Translation in the domain does not change the derivative.
-/
lemma derivWithin_comp_add_const :
    derivWithin (f <| · + a) s x = derivWithin f (a +ᵥ s) (x + a) := by
  simp only [derivWithin, fderivWithin_comp_add_right]

/-- Translation in the domain does not change the derivative. -/
/-
**deriv_comp_add_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_comp_add_const : deriv (fun x => f (x + a)) x = deriv f (x + a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `deriv_comp_const_add`：deriv_comp_const_add : deriv (fun x => f (a + x)) 
x = deriv f (a + x)

--- 原说明 ---
Translation in the domain does not change the derivative.
-/
lemma deriv_comp_add_const : deriv (fun x ↦ f (x + a)) x = deriv f (x + a) := by
  simpa [add_comm] using deriv_comp_const_add f a x
/-
**derivWithin_comp_const_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：derivWithin_comp_const_sub : derivWithin (f <| a - ·) s x = -derivWithin f
 (a +ᵥ -s) (a - x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `derivWithin_comp_neg`：derivWithin_comp_neg : derivWithin (f <| -·) s x =
 -derivWithin f (-s) (-x)
· 使用引理 `derivWithin_comp_const_add`：derivWithin_comp_const_add : derivWithin (f 
<| a + ·) s x = derivWithin f (a +ᵥ s) (a + x)
-/
lemma derivWithin_comp_const_sub :
    derivWithin (f <| a - ·) s x = -derivWithin f (a +ᵥ -s) (a - x) := by
  simp only [sub_eq_add_neg]
  rw [derivWithin_comp_neg (f <| a + ·), derivWithin_comp_const_add]
/-
**deriv_comp_const_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_comp_const_sub : deriv (fun x => f (a - x)) x = -deriv f (a - x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `deriv_comp_neg`：deriv_comp_neg : deriv (fun x => f (-x)) x = -deriv f (-
x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `deriv_comp_const_add`：deriv_comp_const_add : deriv (fun x => f (a + x)) 
x = deriv f (a + x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma deriv_comp_const_sub : deriv (fun x ↦ f (a - x)) x = -deriv f (a - x) := by
  simp_rw [sub_eq_add_neg, deriv_comp_neg (f <| a + ·), deriv_comp_const_add]
/-
**derivWithin_comp_sub_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：derivWithin_comp_sub_const : derivWithin (fun x => f (x - a)) s x = derivW
ithin f (-a +ᵥ s) (x - a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `derivWithin_comp_add_const`：derivWithin_comp_add_const : derivWithin (f 
<| · + a) s x = derivWithin f (a +ᵥ s) (x + a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma derivWithin_comp_sub_const :
    derivWithin (fun x ↦ f (x - a)) s x = derivWithin f (-a +ᵥ s) (x - a) := by
  simp_rw [sub_eq_add_neg, derivWithin_comp_add_const]
/-
**deriv_comp_sub_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_comp_sub_const : deriv (fun x => f (x - a)) x = deriv f (x - a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `deriv_comp_add_const`：deriv_comp_add_const : deriv (fun x => f (x + a)) 
x = deriv f (x + a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma deriv_comp_sub_const : deriv (fun x ↦ f (x - a)) x = deriv f (x - a) := by
  simp_rw [sub_eq_add_neg, deriv_comp_add_const]
