/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# One-dimensional derivatives on pi-types.
-/

public section

variable {𝕜 ι : Type*} [DecidableEq ι] [NontriviallyNormedField 𝕜]

/-
**hasDerivAt_update** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_update (x : ι -> 𝕜) (i : ι) (y : 𝕜) : HasDerivAt (Function.upda
te x i) (Pi.single i (1 : 𝕜)) y
参数：x : ι -> 𝕜；i : ι；y : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single.eq_1`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) → Ze
ro (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x = Function
.upd…
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `HasFDerivAt.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `hasFDerivAt_update`：hasFDerivAt_update (x : forall i, E i) {i : ι} (y : 
E i) : HasFDerivAt (Function.update x i) (.pi (Pi.single i (.id 𝕜 (E i)))) y
-/
theorem hasDerivAt_update (x : ι → 𝕜) (i : ι) (y : 𝕜) :
    HasDerivAt (Function.update x i) (Pi.single i (1 : 𝕜)) y := by
  convert! (hasFDerivAt_update x y).hasDerivAt
  ext z j
  rw [Pi.single, Function.update_apply]
  split_ifs with h
  · simp [h]
  · simp [Pi.single_eq_of_ne h]
/-
**hasDerivAt_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_single (i : ι) (y : 𝕜) : HasDerivAt (Pi.single (M
参数：i : ι；y : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAt_update`：hasDerivAt_update (x : ι -> 𝕜) (i : ι) (y : 𝕜) : HasD
erivAt (Function.update x i) (Pi.single i (1 : 𝕜)) y
-/
theorem hasDerivAt_single (i : ι) (y : 𝕜) :
    HasDerivAt (Pi.single (M := fun _ ↦ 𝕜) i) (Pi.single i (1 : 𝕜)) y :=
  hasDerivAt_update 0 i y

variable [Finite ι]
/-
**deriv_update** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_update (x : ι -> 𝕜) (i : ι) (y : 𝕜) : deriv (Function.update x i) y 
= Pi.single i (1 : 𝕜)
参数：x : ι -> 𝕜；i : ι；y : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `hasDerivAt_update`：hasDerivAt_update (x : ι -> 𝕜) (i : ι) (y : 𝕜) : HasD
erivAt (Function.update x i) (Pi.single i (1 : 𝕜)) y
-/
theorem deriv_update (x : ι → 𝕜) (i : ι) (y : 𝕜) :
    deriv (Function.update x i) y = Pi.single i (1 : 𝕜) :=
  have := Fintype.ofFinite ι
  (hasDerivAt_update x i y).deriv
/-
**deriv_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_single (i : ι) (y : 𝕜) : deriv (Pi.single (M
参数：i : ι；y : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `deriv_update`：deriv_update (x : ι -> 𝕜) (i : ι) (y : 𝕜) : deriv (Functio
n.update x i) y = Pi.single i (1 : 𝕜)
-/
theorem deriv_single (i : ι) (y : 𝕜) :
    deriv (Pi.single (M := fun _ ↦ 𝕜) i) y = Pi.single i (1 : 𝕜) :=
  deriv_update 0 i y
