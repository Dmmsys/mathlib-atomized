/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Quadratic forms are line (Gateaux) differentiable

In this file we prove that a quadratic form is line differentiable,
with the line derivative given by the polar bilinear form.
Note that this statement does not need topology on the domain.
In particular, it applies to discontinuous quadratic forms on infinite-dimensional spaces.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace QuadraticMap

/-
**QuadraticMap.hasLineDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：hasLineDerivAt (f : QuadraticMap 𝕜 E F) (a b : E) : HasLineDerivAt 𝕜 f (po
lar f a b) a b
参数：f : QuadraticMap 𝕜 E F；a b : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `QuadraticMap.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddCommGro
up M] [inst_1 : AddCommGroup N] (f : M → N) (x y : M),   f (x + y) = f x + f y +
 Quadratic…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.map_smul`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [i
nst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : A…
· 使用定理 `QuadraticMap.polar_smul_right`：polar_smul_right (a : R) (x y : M) : pola
r Q x (a • y) = a • polar Q x y
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HasDerivAt.add`：HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt
 g g' x) : HasDerivAt (f + g) (f' + g') x
· 使用定理 `hasDerivAt_const`：hasDerivAt_const : HasDerivAt (fun _ => c) 0 x
· 使用定理 `HasDerivAt.smul`：HasDerivAt.smul (hc : HasDerivAt c c' x) (hf : HasDeriv
At f f' x) : HasDerivAt (c • f) (c x • f' + c' • f x) x
· 使用定理 `HasDerivAt.mul`：HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt
 d d' x) : HasDerivAt (c * d) (c' * d x + c x * d') x
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
-/
theorem hasLineDerivAt (f : QuadraticMap 𝕜 E F) (a b : E) :
    HasLineDerivAt 𝕜 f (polar f a b) a b := by
  simpa [HasLineDerivAt, QuadraticMap.map_add, f.map_smul] using!
    ((hasDerivAt_const (0 : 𝕜) (f a)).add <|
      ((hasDerivAt_id 0).mul (hasDerivAt_id 0)).smul (hasDerivAt_const 0 (f b))).add
      ((hasDerivAt_id 0).smul (hasDerivAt_const 0 (polar f a b)))
/-
**QuadraticMap.lineDifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：lineDifferentiableAt (f : QuadraticMap 𝕜 E F) (a b : E) : LineDifferentiab
leAt 𝕜 f a b
参数：f : QuadraticMap 𝕜 E F；a b : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasLineDerivAt.lineDifferentiableAt`：HasLineDerivAt.lineDifferentiableAt
 (hf : HasLineDerivAt 𝕜 f f' x v) : LineDifferentiableAt 𝕜 f x v
· 使用定理 `QuadraticMap.hasLineDerivAt`：hasLineDerivAt (f : QuadraticMap 𝕜 E F) (a 
b : E) : HasLineDerivAt 𝕜 f (polar f a b) a b
-/
theorem lineDifferentiableAt (f : QuadraticMap 𝕜 E F) (a b : E) : LineDifferentiableAt 𝕜 f a b :=
  (f.hasLineDerivAt a b).lineDifferentiableAt

@[simp]
/-
**QuadraticMap.lineDeriv** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : Norme
dAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] (f : QuadraticMap 𝕜 E F),   lineDeri
v 𝕜 ⇑f = QuadraticMap.polar ⇑f
参数：f : QuadraticMap 𝕜 E F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasLineDerivAt.lineDeriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F
] {E : Type u_…
· 使用定理 `QuadraticMap.hasLineDerivAt`：hasLineDerivAt (f : QuadraticMap 𝕜 E F) (a 
b : E) : HasLineDerivAt 𝕜 f (polar f a b) a b
-/
protected theorem lineDeriv (f : QuadraticMap 𝕜 E F) : lineDeriv 𝕜 f = polar f := by
  ext a b
  exact (f.hasLineDerivAt a b).lineDeriv

end QuadraticMap

