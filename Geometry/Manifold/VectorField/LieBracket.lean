/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.Notation

/-!
# Lie brackets of vector fields on manifolds

We define the Lie bracket of two vector fields, denoted with
`VectorField.mlieBracket I V W x`, as the pullback in the manifold of the corresponding notion
in the model space (through `extChartAt I x`).

The main results are the following:
* `VectorField.mpullback_mlieBracket` states that the pullback of the Lie bracket
  is the Lie bracket of the pullbacks.
* `VectorField.leibniz_identity_mlieBracket` is the Leibniz (or Jacobi)
  identity `[U, [V, W]] = [[U, V], W] + [V, [U, W]]`.

-/

public section

open Set Function Filter NormedSpace
open scoped Topology Manifold ContDiff

noncomputable section

/- We work in the `VectorField` namespace because pullbacks, Lie brackets, and so on, are notions
that make sense in a variety of contexts. We also prefix the notions with `m` to distinguish the
manifold notions from the vector space notions. For instance, the Lie bracket of two vector
fields in a manifold is denoted with `VectorField.mlieBracket I V W x`, where `I` is the relevant
model with corners, `V W : Π (x : M), TangentSpace I x` are the vector fields, and `x : M` is
the basepoint.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {H'' : Type*} [TopologicalSpace H''] {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f : M → M'} {s t : Set M} {x x₀ : M}

namespace VectorField

section LieBracket

/-! ### The Lie bracket of vector fields in manifolds -/

variable {V W V₁ W₁ : Π (x : M), TangentSpace I x}

variable (I I') in
/-- The Lie bracket of two vector fields in a manifold, within a set. -/
/-
**VectorField.mlieBracketWithin** 是 Mathlib 中的一个定义，位于命名空间 `VectorField`。
形式化陈述：mlieBracketWithin (V W : Π (x : M), TangentSpace I x) (s : Set M) (x₀ : M)
 : TangentSpace I x₀
参数：V W : Π (x : M), TangentSpace I x；s : Set M；x₀ : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lie bracket of two vector fields in a manifold, within a set.
-/
def mlieBracketWithin (V W : Π (x : M), TangentSpace I x) (s : Set M) (x₀ : M) :
    TangentSpace I x₀ :=
  mpullback I 𝓘(𝕜, E) (extChartAt I x₀)
    (lieBracketWithin 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W (range I))
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I)) x₀

variable (I I') in
/-- The Lie bracket of two vector fields in a manifold. -/
/-
**VectorField.mlieBracket** 是 Mathlib 中的一个定义，位于命名空间 `VectorField`。
形式化陈述：mlieBracket (V W : Π (x : M), TangentSpace I x) (x₀ : M) : TangentSpace I 
x₀
参数：V W : Π (x : M), TangentSpace I x；x₀ : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lie bracket of two vector fields in a manifold.
-/
def mlieBracket (V W : Π (x : M), TangentSpace I x) (x₀ : M) : TangentSpace I x₀ :=
  mlieBracketWithin I V W univ x₀
/-
**VectorField.mlieBracketWithin_def** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mlieBracketWithin_def : mlieBracketWithin I V W s = fun x₀ => mpullback I 
𝓘(𝕜, E) (extChartAt I x₀) (lieBracketWithin 𝕜 (mpullbackWithin 𝓘(𝕜, E) I (extCha
rtAt I x₀).symm V (range I)) (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W
 (range I)) ((extChartAt I x₀).symm ⁻¹' s inter range I)) x₀
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mlieBracketWithin_def :
    mlieBracketWithin I V W s = fun x₀ ↦
    mpullback I 𝓘(𝕜, E) (extChartAt I x₀)
    (lieBracketWithin 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W (range I))
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I)) x₀ := (rfl)
/-
**VectorField.mlieBracketWithin_apply** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mlieBracketWithin_apply : mlieBracketWithin I V W s x₀ = (mfderiv% (extCha
rtAt I x₀) x₀).inverse ((lieBracketWithin 𝕜 (mpullbackWithin 𝓘(𝕜, E) I (extChart
At I x₀).symm V (range I)) (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W (
range I)) ((extChartAt I x₀).symm ⁻¹' s inter range I)) ((extChartAt I x₀ x₀)))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mlieBracketWithin_apply :
    mlieBracketWithin I V W s x₀ = (mfderiv% (extChartAt I x₀) x₀).inverse
    ((lieBracketWithin 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W (range I))
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I)) ((extChartAt I x₀ x₀))) := (rfl)

set_option backward.isDefEq.respectTransparency false in
/-
**VectorField.mlieBracketWithin_eq_lieBracketWithin** 是 Mathlib 中的一个引理，位于命名空间 `V
ectorField`。
形式化陈述：mlieBracketWithin_eq_lieBracketWithin {V W : Π (x : E), TangentSpace 𝓘(𝕜, 
E) x} {s : Set E} : mlieBracketWithin 𝓘(𝕜, E) V W s = lieBracketWithin 𝕜 V W s
参数：x : E；𝕜, E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.mlieBracketWithin_apply`：mlieBracketWithin_apply : mlieBrack
etWithin I V W s x₀ = (mfderiv% (extChartAt I x₀) x₀).inverse ((lieBracketWithin
 𝕜 (mpullbackWithin 𝓘(𝕜, …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mfderiv_id`：mfderiv_id : mfderiv% (@id M) x = ContinuousLinearMap.id 𝕜 (
TangentSpace% x)
· 使用定理 `ContinuousLinearMap.inverse_id`：∀ {R : Type u_1} {M : Type u_2} [inst : 
TopologicalSpace M] [inst_1 : Semiring R] [inst_2 : AddCommMonoid M]   [inst_3 :
 _root_.Module R M],…
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `VectorField.mpullbackWithin_univ`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [ins
t_2 : NormedAddCommGro…
· 使用定理 `VectorField.mpullback_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 : No
rmedAddCommGro…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mlieBracketWithin_eq_lieBracketWithin {V W : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {s : Set E} :
    mlieBracketWithin 𝓘(𝕜, E) V W s = lieBracketWithin 𝕜 V W s := by
  ext x
  simp [mlieBracketWithin_apply]

/- Copy of the `lieBracket` API to manifolds -/

/-
**VectorField.mlieBracketWithin_univ** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1
 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddCommGroup E] [inst_3 
: NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {V W : (x : M) → TangentSpace I x},  
 VectorField.mlieBracketWithin I V W Set.univ = VectorField.mlieBracket I V W
参数：x : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of the `lieBracket` API to manifolds
-/
@[simp] lemma mlieBracketWithin_univ :
    mlieBracketWithin I V W univ = mlieBracket I V W := (rfl)

set_option backward.isDefEq.respectTransparency false in
/-
**VectorField.mlieBracketWithin_eq_zero_of_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Ve
ctorField`。
形式化陈述：mlieBracketWithin_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) : mlieB
racketWithin I V W s x = 0
参数：hV : V x = 0；hW : W x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.lieBracketWithin_eq_zero_of_eq_zero`：lieBracketWithin_eq_zer
o_of_eq_zero (hV : V x = 0) (hW : W x = 0) : lieBracketWithin 𝕜 V W s x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
lemma mlieBracketWithin_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) :
    mlieBracketWithin I V W s x = 0 := by
  simp only [mlieBracketWithin, mpullback_apply]
  rw [lieBracketWithin_eq_zero_of_eq_zero]
  · simp
  · simp only [mpullbackWithin_apply]
    have : (extChartAt I x).symm ((extChartAt I x) x) = x := by simp
    rw [this, hV]
    simp +instances
  · simp only [mpullbackWithin_apply]
    have : (extChartAt I x).symm ((extChartAt I x) x) = x := by simp
    rw [this, hW]
    simp +instances

set_option backward.isDefEq.respectTransparency false in
/-
**VectorField.mlieBracketWithin_swap_apply** 是 Mathlib 中的一个引理，位于命名空间 `VectorFiel
d`。
形式化陈述：mlieBracketWithin_swap_apply : mlieBracketWithin I V W s x = - mlieBracket
Within I W V s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Geometry.Manifold.VectorField.LieBracket.0.VectorField.
mlieBracketWithin.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H :
 Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddCom
mGro…
· 使用引理 `VectorField.lieBracketWithin_swap`：lieBracketWithin_swap : lieBracketWit
hin 𝕜 V W s = - lieBracketWithin 𝕜 W V s
· 使用引理 `VectorField.mpullback_neg`：mpullback_neg : mpullback I I' f (-V) = - mpu
llback I I' f V
-/
lemma mlieBracketWithin_swap_apply :
    mlieBracketWithin I V W s x = - mlieBracketWithin I W V s x := by
  rw [mlieBracketWithin, lieBracketWithin_swap, mpullback_neg]
  rfl
/-
**VectorField.mlieBracketWithin_swap** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mlieBracketWithin_swap : mlieBracketWithin I V W s = - mlieBracketWithin I
 W V s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `VectorField.mlieBracketWithin_swap_apply`：mlieBracketWithin_swap_apply :
 mlieBracketWithin I V W s x = - mlieBracketWithin I W V s x
-/
lemma mlieBracketWithin_swap :
    mlieBracketWithin I V W s = - mlieBracketWithin I W V s := by
  ext x
  exact mlieBracketWithin_swap_apply
/-
**VectorField.mlieBracket_swap_apply** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mlieBracket_swap_apply : mlieBracket I V W x = - mlieBracket I W V x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `VectorField.mlieBracketWithin_swap_apply`：mlieBracketWithin_swap_apply :
 mlieBracketWithin I V W s x = - mlieBracketWithin I W V s x
-/
lemma mlieBracket_swap_apply : mlieBracket I V W x = - mlieBracket I W V x :=
  mlieBracketWithin_swap_apply
/-
**VectorField.mlieBracket_swap** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mlieBracket_swap : mlieBracket I V W = - mlieBracket I W V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `VectorField.mlieBracketWithin_swap`：mlieBracketWithin_swap : mlieBracket
Within I V W s = - mlieBracketWithin I W V s
-/
lemma mlieBracket_swap : mlieBracket I V W = - mlieBracket I W V :=
  mlieBracketWithin_swap

set_option backward.isDefEq.respectTransparency false in
/-
**VectorField.mlieBracketWithin_self** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1
 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddCommGroup E] [inst_3 
: NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {V : (x : M) → TangentSpace I x},   V
ectorField.mlieBracketWithin I V V = 0
参数：x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `VectorField.lieBracketWithin_self`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {V : E → E} …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mlieBracketWithin_self : mlieBracketWithin I V V = 0 := by
  ext x; simp [mlieBracketWithin, mpullback]
/-
**VectorField.mlieBracket_self** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1
 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddCommGroup E] [inst_3 
: NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {V : (x : M) → TangentSpace I x},   V
ectorField.mlieBracket I V V = 0
参数：x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VectorField.mlieBracketWithin_self`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [i
nst_2 : NormedAddCommGro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mlieBracket_self : mlieBracket I V V = 0 := by
  ext x; simp_rw [mlieBracket, mlieBracketWithin_self, Pi.zero_apply]

set_option backward.isDefEq.respectTransparency false in
/-- We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set. -/
@[simp]
/-
**VectorField.mlieBracketWithin_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `VectorField
`。
形式化陈述：mlieBracketWithin_zero_left : mlieBracketWithin I 0 W s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `VectorField.mpullbackWithin_zero`：mpullbackWithin_zero : mpullbackWithin
 I I' f 0 s = 0
· 使用引理 `VectorField.lieBracketWithin_zero_left`：lieBracketWithin_zero_left : lie
BracketWithin 𝕜 0 W s = 0
· 使用引理 `VectorField.mpullback_zero`：mpullback_zero : mpullback I I' f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set.
-/
lemma mlieBracketWithin_zero_left : mlieBracketWithin I 0 W s = 0 := by
  ext x
  simp [mlieBracketWithin]

/-- We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set. -/
@[simp]
/-
**VectorField.mlieBracketWithin_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `VectorFiel
d`。
形式化陈述：mlieBracketWithin_zero_right : mlieBracketWithin I W 0 s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.mlieBracketWithin_swap`：mlieBracketWithin_swap : mlieBracket
Within I V W s = - mlieBracketWithin I W V s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `VectorField.mlieBracketWithin_zero_left`：mlieBracketWithin_zero_left : m
lieBracketWithin I 0 W s = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set.
-/
lemma mlieBracketWithin_zero_right : mlieBracketWithin I W 0 s = 0 := by
  rw [mlieBracketWithin_swap]; simp

/-- We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. -/
@[simp]
/-
**VectorField.mlieBracket_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mlieBracket_zero_left : mlieBracket I 0 W = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.mlieBracketWithin_zero_left`：mlieBracketWithin_zero_left : m
lieBracketWithin I 0 W s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable.
-/
lemma mlieBracket_zero_left : mlieBracket I 0 W = 0 := by simp [← mlieBracketWithin_univ]

/-- We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. -/
@[simp]
/-
**VectorField.mlieBracket_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mlieBracket_zero_right : mlieBracket I W 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.mlieBracketWithin_zero_right`：mlieBracketWithin_zero_right :
 mlieBracketWithin I W 0 s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable.
-/
lemma mlieBracket_zero_right : mlieBracket I W 0 = 0 := by simp [← mlieBracketWithin_univ]

/-- Variant of `mlieBracketWithin_congr_set` where one requires the sets to coincide only in
the complement of a point. -/
/-
**VectorField.mlieBracketWithin_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 `VectorFiel
d`。
形式化陈述：mlieBracketWithin_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : mlieBracket
Within I V W s x = mlieBracketWithin I V W t x
参数：y : M；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.mlieBracketWithin_apply`：mlieBracketWithin_apply : mlieBrack
etWithin I V W s x₀ = (mfderiv% (extChartAt I x₀) x₀).inverse ((lieBracketWithin
 𝕜 (mpullbackWithin 𝓘(𝕜, …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `preimage_extChartAt_eventuallyEq_compl_singleton`：preimage_extChartAt_ev
entuallyEq_compl_singleton (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : ((extChartAt I x).s
ymm ⁻¹' s inter range I : Set E) =ᶠ[𝓝[…
· 使用定理 `VectorField.lieBracketWithin_congr_set'`：lieBracketWithin_congr_set' (y 
: E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V
 W t x

--- 原说明 ---
Variant of `mlieBracketWithin_congr_set` where one requires the sets to coincide
 only in
the complement of a point.
-/
theorem mlieBracketWithin_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x := by
  simp only [mlieBracketWithin_apply]
  congr 1
  suffices A : ((extChartAt I x).symm ⁻¹' s ∩ range I : Set E)
    =ᶠ[𝓝[{(extChartAt I x) x}ᶜ] (extChartAt I x x)]
      ((extChartAt I x).symm ⁻¹' t ∩ range I : Set E) by
    apply lieBracketWithin_congr_set' _ A
  exact preimage_extChartAt_eventuallyEq_compl_singleton y h
/-
**VectorField.mlieBracketWithin_congr_set** 是 Mathlib 中的一个定理，位于命名空间 `VectorField
`。
形式化陈述：mlieBracketWithin_congr_set (h : s =ᶠ[𝓝 x] t) : mlieBracketWithin I V W s 
x = mlieBracketWithin I V W t x
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorField.mlieBracketWithin_congr_set'`：mlieBracketWithin_congr_set' (
y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : mlieBracketWithin I V W s x = mlieBracketWithin
 I V W t x
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem mlieBracketWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x :=
  mlieBracketWithin_congr_set' x <| h.filter_mono inf_le_left
/-
**VectorField.mlieBracketWithin_inter** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：mlieBracketWithin_inter (ht : t in 𝓝 x) : mlieBracketWithin I V W (s inter
 t) x = mlieBracketWithin I V W s x
参数：ht : t in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorField.mlieBracketWithin_congr_set`：mlieBracketWithin_congr_set (h 
: s =ᶠ[𝓝 x] t) : mlieBracketWithin I V W s x = mlieBracketWithin I V W t x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mlieBracketWithin_inter (ht : t ∈ 𝓝 x) :
    mlieBracketWithin I V W (s ∩ t) x = mlieBracketWithin I V W s x := by
  apply mlieBracketWithin_congr_set
  filter_upwards [ht] with y hy
  change (y ∈ s ∩ t) = (y ∈ s)
  simp_all
/-
**VectorField.mlieBracketWithin_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `VectorFie
ld`。
形式化陈述：mlieBracketWithin_of_mem_nhds (h : s in 𝓝 x) : mlieBracketWithin I V W s x
 = mlieBracket I V W x
参数：h : s in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `VectorField.mlieBracketWithin_univ`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [i
nst_2 : NormedAddCommGro…
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `VectorField.mlieBracketWithin_inter`：mlieBracketWithin_inter (ht : t in 
𝓝 x) : mlieBracketWithin I V W (s inter t) x = mlieBracketWithin I V W s x
-/
theorem mlieBracketWithin_of_mem_nhds (h : s ∈ 𝓝 x) :
    mlieBracketWithin I V W s x = mlieBracket I V W x := by
  rw [← mlieBracketWithin_univ, ← univ_inter s, mlieBracketWithin_inter h]
/-
**VectorField.mlieBracketWithin_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `VectorField
`。
形式化陈述：mlieBracketWithin_of_isOpen (hs : IsOpen s) (hx : x in s) : mlieBracketWit
hin I V W s x = mlieBracket I V W x
参数：hs : IsOpen s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorField.mlieBracketWithin_of_mem_nhds`：mlieBracketWithin_of_mem_nhds
 (h : s in 𝓝 x) : mlieBracketWithin I V W s x = mlieBracket I V W x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem mlieBracketWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) :
    mlieBracketWithin I V W s x = mlieBracket I V W x :=
  mlieBracketWithin_of_mem_nhds (hs.mem_nhds hx)

/-- Variant of `mlieBracketWithin_eventually_congr_set` where one requires the sets to coincide only
in the complement of a point. -/
/-
**VectorField.mlieBracketWithin_eventually_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 
`VectorField`。
形式化陈述：mlieBracketWithin_eventually_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : 
mlieBracketWithin I V W s =ᶠ[𝓝 x] mlieBracketWithin I V W t
参数：y : M；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhds_nhdsWithin`：eventually_nhds_nhdsWithin {a : α} {s : Set 
α} {p : α -> Prop} : (forallᶠ y in 𝓝 a, forallᶠ x in 𝓝[s] y, p x) ↔ forallᶠ x in
 𝓝[s] a, p x
· 使用定理 `VectorField.mlieBracketWithin_congr_set'`：mlieBracketWithin_congr_set' (
y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : mlieBracketWithin I V W s x = mlieBracketWithin
 I V W t x

--- 原说明 ---
Variant of `mlieBracketWithin_eventually_congr_set` where one requires the sets 
to coincide only
in the complement of a point.
-/
theorem mlieBracketWithin_eventually_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mlieBracketWithin I V W s =ᶠ[𝓝 x] mlieBracketWithin I V W t :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => mlieBracketWithin_congr_set' y
/-
**VectorField.mlieBracketWithin_eventually_congr_set** 是 Mathlib 中的一个定理，位于命名空间 `
VectorField`。
形式化陈述：mlieBracketWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) : mlieBracketWith
in I V W s =ᶠ[𝓝 x] mlieBracketWithin I V W t
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorField.mlieBracketWithin_eventually_congr_set'`：mlieBracketWithin_e
ventually_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : mlieBracketWithin I V W s
 =ᶠ[𝓝 x] mlieBracketWithin I V W t
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem mlieBracketWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    mlieBracketWithin I V W s =ᶠ[𝓝 x] mlieBracketWithin I V W t :=
  mlieBracketWithin_eventually_congr_set' x <| h.filter_mono inf_le_left

set_option backward.isDefEq.respectTransparency false in
/-
**VectorField._root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_eq** 是 Ma
thlib 中的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_eq
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hxV : V₁ x = V x) (hW : W₁ =ᶠ[𝓝[s] x] W) (hxW : W₁ x = W x) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x := by
  simp only [mlieBracketWithin_apply]
  congr 1
  let I1 : NormedAddCommGroup (TangentSpace 𝓘(𝕜, E) (extChartAt I x x)) :=
    inferInstanceAs (NormedAddCommGroup E)
  let _I2 : NormedSpace 𝕜 (TangentSpace 𝓘(𝕜, E) (extChartAt I x x)) :=
    ‹NormedSpace 𝕜 E›
  apply Filter.EventuallyEq.lieBracketWithin_vectorField_eq
  · apply nhdsWithin_mono _ inter_subset_left
    filter_upwards [(continuousAt_extChartAt_symm x).continuousWithinAt.preimage_mem_nhdsWithin''
      hV (by simp)] with y hy
    simp only [mpullbackWithin_apply]
    congr 1
  · simp only [mpullbackWithin_apply]
    congr 1
    convert! hxV <;> exact extChartAt_to_inv x
  · apply nhdsWithin_mono _ inter_subset_left
    filter_upwards [(continuousAt_extChartAt_symm x).continuousWithinAt.preimage_mem_nhdsWithin''
      hW (by simp)] with y hy
    simp only [mpullbackWithin_apply]
    congr 1
  · simp only [mpullbackWithin_apply]
    congr 1
    convert! hxW <;> exact extChartAt_to_inv x
/-
**VectorField._root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem
** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (hx : x ∈ s) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  hV.mlieBracketWithin_vectorField_eq (mem_of_mem_nhdsWithin hx hV :)
    hW (mem_of_mem_nhdsWithin hx hW :)

/-- If vector fields coincide on a neighborhood of a point within a set, then the Lie brackets
also coincide on a neighborhood of this point within this set. Version where one considers the Lie
bracket within a subset. -/
/-
**VectorField._root_.Filter.EventuallyEq.mlieBracketWithin_vectorField'** 是 Math
lib 中的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If vector fields coincide on a neighborhood of a point within a set, then the Li
e brackets
also coincide on a neighborhood of this point within this set. Version where one
 considers the Lie
bracket within a subset.
-/
theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField'
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (ht : t ⊆ s) :
    mlieBracketWithin I V₁ W₁ t =ᶠ[𝓝[s] x] mlieBracketWithin I V W t := by
  filter_upwards [hV, hW, eventually_eventually_nhdsWithin.2 hV,
    eventually_eventually_nhdsWithin.2 hW] with y hVy hWy hVy' hWy'
  apply Filter.EventuallyEq.mlieBracketWithin_vectorField_eq
  · apply nhdsWithin_mono _ ht
    exact hVy'
  · exact hVy
  · apply nhdsWithin_mono _ ht
    exact hWy'
  · exact hWy
/-
**VectorField._root_.Filter.EventuallyEq.mlieBracketWithin_vectorField** 是 Mathl
ib 中的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) :
    mlieBracketWithin I V₁ W₁ s =ᶠ[𝓝[s] x] mlieBracketWithin I V W s :=
  hV.mlieBracketWithin_vectorField' hW Subset.rfl
/-
**VectorField._root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_of_insert
** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_of_insert
    (hV : V₁ =ᶠ[𝓝[insert x s] x] V) (hW : W₁ =ᶠ[𝓝[insert x s] x] W) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x := by
  apply mem_of_mem_nhdsWithin (mem_insert x s)
    (hV.mlieBracketWithin_vectorField' hW (subset_insert x s))
/-
**VectorField._root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_nhds**
 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_nhds
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  (hV.filter_mono nhdsWithin_le_nhds).mlieBracketWithin_vectorField_eq hV.self_of_nhds
    (hW.filter_mono nhdsWithin_le_nhds) hW.self_of_nhds
/-
**VectorField.mlieBracketWithin_congr** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：mlieBracketWithin_congr (hV : EqOn V₁ V s) (hVx : V₁ x = V x) (hW : EqOn W
₁ W s) (hWx : W₁ x = W x) : mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I 
V W s x
参数：hV : EqOn V₁ V s；hVx : V₁ x = V x；hW : EqOn W₁ W s；hWx : W₁ x = W x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.mlieBracketWithin_vectorField_eq`：∀ {𝕜 : Type u_1} [
inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {
E : Type u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `Set.EqOn.eventuallyEq`：Set.EqOn.eventuallyEq {α β} {s : Set α} {f g : α 
-> β} (h : EqOn f g s) : f =ᶠ[𝓟 s] g
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem mlieBracketWithin_congr
    (hV : EqOn V₁ V s) (hVx : V₁ x = V x) (hW : EqOn W₁ W s) (hWx : W₁ x = W x) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  (hV.eventuallyEq.filter_mono inf_le_right).mlieBracketWithin_vectorField_eq hVx
    (hW.eventuallyEq.filter_mono inf_le_right) hWx

/-- Version of `mlieBracketWithin_congr` in which one assumes that the point belongs to the
given set. -/
/-
**VectorField.mlieBracketWithin_congr'** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：mlieBracketWithin_congr' (hV : EqOn V₁ V s) (hW : EqOn W₁ W s) (hx : x in 
s) : mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x
参数：hV : EqOn V₁ V s；hW : EqOn W₁ W s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorField.mlieBracketWithin_congr`：mlieBracketWithin_congr (hV : EqOn 
V₁ V s) (hVx : V₁ x = V x) (hW : EqOn W₁ W s) (hWx : W₁ x = W x) : mlieBracketWi
thin I V₁ W₁ s x = mlieBr…

--- 原说明 ---
Version of `mlieBracketWithin_congr` in which one assumes that the point belongs
 to the
given set.
-/
theorem mlieBracketWithin_congr' (hV : EqOn V₁ V s) (hW : EqOn W₁ W s) (hx : x ∈ s) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  mlieBracketWithin_congr hV (hV hx) hW (hW hx)
/-
**VectorField._root_.Filter.EventuallyEq.mlieBracket_vectorField_eq** 是 Mathlib 
中的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.EventuallyEq.mlieBracket_vectorField_eq
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    mlieBracket I V₁ W₁ x = mlieBracket I V W x := by
  rw [← mlieBracketWithin_univ, ← mlieBracketWithin_univ,
    hV.mlieBracketWithin_vectorField_eq_nhds hW]
/-
**VectorField._root_.Filter.EventuallyEq.mlieBracket_vectorField** 是 Mathlib 中的一
个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Filter.EventuallyEq.mlieBracket_vectorField
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) : mlieBracket I V₁ W₁ =ᶠ[𝓝 x] mlieBracket I V W := by
  filter_upwards [hV.eventuallyEq_nhds, hW.eventuallyEq_nhds] with y hVy hWy
  exact hVy.mlieBracket_vectorField_eq hWy

section

variable {c : 𝕜}
variable [IsManifold I 2 M]

/-
**VectorField._root_.MDifferentiableWithinAt.differentiableWithinAt_mpullbackWit
hin_vectorField** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField
    [CompleteSpace E]
    (hV : MDiffAt[s] (fun x ↦ (V x : TangentBundle I M)) x) :
    DifferentiableWithinAt 𝕜 (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  apply MDifferentiableWithinAt.differentiableWithinAt
  have := MDifferentiableWithinAt.mpullbackWithin_vectorField_inter_of_eq hV
    (contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target x))
    (isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target x)) (mem_range_self _)
    I.uniqueMDiffOn le_rfl (extChartAt_to_inv x).symm
  rw [inter_comm]
  exact (contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).contMDiffAt.mdifferentiableAt one_ne_zero
    |>.comp_mdifferentiableWithinAt _ this

set_option backward.isDefEq.respectTransparency false in
/-
**VectorField.mfderiv_extChartAt_inverse_comp_mfderivWithin_extChartAT_symm** 是 
Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mfderiv_extChartAt_inverse_comp_mfderivWithin_extChartAT_symm (Y : Tangent
Space I x) : letI φ
参数：Y : TangentSpace I x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extChartAt_to_inv`：extChartAt_to_inv (x : M) : (extChartAt I x).symm ((e
xtChartAt I x) x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.IsInvertible.inverse_comp_of_left`：∀ {R : Type u_1} 
{M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [inst : TopologicalSpace M]   [in
st_1 : TopologicalSpace M₂] [inst_2 : Topol…
· 使用引理 `isInvertible_mfderivWithin_extChartAt_symm`：isInvertible_mfderivWithin_e
xtChartAt_symm {y : E} (hy : y in (extChartAt I x).target) : (mfderiv[range I] (
extChartAt I x).symm y).IsInvert…
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `mem_extChartAt_target`：mem_extChartAt_target (x : M) : extChartAt I x x 
in (extChartAt I x).target
· 使用定理 `ContinuousLinearMap.inverse_id`：∀ {R : Type u_1} {M : Type u_2} [inst : 
TopologicalSpace M] [inst_1 : Semiring R] [inst_2 : AddCommMonoid M]   [inst_3 :
 _root_.Module R M],…
· 使用引理 `mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'`：mfderivWithin_ex
tChartAt_symm_comp_mfderiv_extChartAt' {y : M} (hy : y in (extChartAt I x).sourc
e) : (mfderiv[range I] (extChartAt I x).symm…
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mfderiv_extChartAt_inverse_comp_mfderivWithin_extChartAT_symm (Y : TangentSpace I x) :
    letI φ := extChartAt I x
    ((mfderiv% φ x).inverse.comp ((mfderiv[range I] φ.symm (φ x)).inverse) Y) = Y := by
  set φ := extChartAt I x
  trans (ContinuousLinearMap.id 𝕜 _) Y; swap; · simp
  rw [extChartAt_to_inv x, ← ContinuousLinearMap.IsInvertible.inverse_comp_of_left,
    ← ContinuousLinearMap.inverse_id,
    mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (mem_extChartAt_source x)]
  exact isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target x)

set_option backward.isDefEq.respectTransparency false in
variable (x W) in
/-
**VectorField.mfderiv_extChart_inverse_comp_aux** 是 Mathlib 中的一个引理，位于命名空间 `Vecto
rField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mfderiv_extChart_inverse_comp_aux :
    letI φ := extChartAt I x
    (mfderiv% φ x).inverse.comp
      ((mfderiv[range I] φ.symm (φ x)).inverse) (W (φ.symm (φ x))) = W x := by
  rw [mfderiv_extChartAt_inverse_comp_mfderivWithin_extChartAT_symm, extChartAt_to_inv]

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back through `extChartAt` the scalar multiplication of a vector field by
the derivative of a scalar function equals the scalar multiplication by the manifold derivative. -/
/-
**VectorField.mpullback_mfderivWithin_apply_smul** 是 Mathlib 中的一个引理，位于命名空间 `Vect
orField`。
形式化陈述：mpullback_mfderivWithin_apply_smul {f : M -> 𝕜} (hf : MDiffAt[s] f x) : le
t V'
参数：hf : MDiffAt[s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Geometry.Manifold.VectorField.LieBracket.0.VectorField.
mfderiv_extChart_inverse_comp_aux`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 : N
ormedAddCommGro…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `extChartAt_to_inv`：extChartAt_to_inv (x : M) : (extChartAt I x).symm ((e
xtChartAt I x) x) = x
· 使用引理 `mfderivWithin_extChartAt_symm_inverse_apply`：mfderivWithin_extChartAt_sy
mm_inverse_apply (v : TangentSpace I x) : (mfderiv[range I] (extChartAt I x).sym
m (extChartAt I x x)).inverse v =…
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…

--- 原说明 ---
Pulling back through `extChartAt` the scalar multiplication of a vector field by
the derivative of a scalar function equals the scalar multiplication by the mani
fold derivative.
-/
lemma mpullback_mfderivWithin_apply_smul {f : M → 𝕜}
    (hf : MDiffAt[s] f x) :
    let V' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)
    let W' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (range I)
    letI s' : Set E := (extChartAt I x).symm ⁻¹' s ∩ range I
    mpullback I 𝓘(𝕜, E) (extChartAt I x)
        (fun x₀ ↦ (fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) s' x₀) (V' x₀) • W' x₀) x =
      (mfderiv[s] f x) (V x) • W x := by
  simp only [mpullback, mfderivWithin, hf, map_smul, ← mfderiv_extChart_inverse_comp_aux x W,
    mpullbackWithin]
  congr 2
  rw [extChartAt_to_inv]
  exact mfderivWithin_extChartAt_symm_inverse_apply (v := V x)

variable [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in
/--
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a function
`f : M → 𝕜`, we have `[V, f • W] = (df V) • W + f • [V, W]`. Version within a set.
-/
/-
**VectorField.mlieBracketWithin_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `VectorFiel
d`。
形式化陈述：mlieBracketWithin_smul_right {f : M -> 𝕜} (hf : MDiffAt[s] f x) (hW : MDif
fAt[s] (fun x => (W x : TangentBundle I M)) x) (hs : UniqueMDiffAt[s] x) : mlieB
racketWithin I V (f • W) s x = d[s] f x (V x) • (W x) + (f x) • mlieBracketWithi
n I V W s x
参数：hf : MDiffAt[s] f x；hW : MDiffAt[s] (fun x => (W x : TangentBundle I M)) x；hs
 : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `VectorField.mpullbackWithin_smul`：mpullbackWithin_smul {g : M' -> 𝕜} : m
pullbackWithin I I' f (g • V) s = (g ∘ f) • mpullbackWithin I I' f V s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `VectorField.lieBracketWithin_smul_right`：lieBracketWithin_smul_right {f 
: E -> 𝕜} (hf : DifferentiableWithinAt 𝕜 f s x) (hW : DifferentiableWithinAt 𝕜 W
 s x) (hs : UniqueDiffWithinA…
· 使用定理 `MDifferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm`：MDi
fferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm (hf : MDiffAt[s
] f x) : letI φ
· 使用定理 `MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorFie
ld`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 :
 TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.add_def`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add (M
 i)] (f g : (i : ι) → M i), f + g = fun i => f i + g i
· 使用引理 `VectorField.mpullback_add_apply`：mpullback_add_apply : mpullback I I' f 
(V + V₁) x = mpullback I I' f V x + mpullback I I' f V₁ x
· 使用引理 `VectorField.mpullback_mfderivWithin_apply_smul`：mpullback_mfderivWithin_
apply_smul {f : M -> 𝕜} (hf : MDiffAt[s] f x) : let V'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `VectorField.mpullback_smul`：mpullback_smul {g : M' -> 𝕜} : mpullback I I
' f (g • V) = (g ∘ f) • mpullback I I' f V
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a 
function
`f : M → 𝕜`, we have `[V, f • W] = (df V) • W + f • [V, W]`. Version within a se
t.
-/
lemma mlieBracketWithin_smul_right {f : M → 𝕜} (hf : MDiffAt[s] f x)
    (hW : MDiffAt[s] (fun x ↦ (W x : TangentBundle I M)) x)
    (hs : UniqueMDiffAt[s] x) :
    mlieBracketWithin I V (f • W) s x =
      d[s] f x (V x) • (W x) + (f x) • mlieBracketWithin I V W s x := by
  simp only [mlieBracketWithin, mpullbackWithin_smul]
  -- Simplify local notation a bit.
  set V' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)
  set W' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (range I)
  set f' := f ∘ (extChartAt I x).symm
  set s' := (extChartAt I x).symm ⁻¹' s ∩ range I
  -- We begin by rewriting using `lieBracketWithin_smul_right`.
  -- We need the coercion since on the nose `B` is a map `E → E`,
  -- whereas we need a map between tangent spaces.
  let A (x₀) := (fderivWithin 𝕜 f' s' x₀) (V' x₀) • W' x₀
  let B (x₀) : TangentSpace 𝓘(𝕜, E) x₀ := f' x₀ • lieBracketWithin 𝕜 V' W' s' x₀
  trans mpullback I 𝓘(𝕜, E) ((extChartAt I x)) (fun y ↦ A y + B y) x
  · simp only [mpullback_apply]
    congr
    exact lieBracketWithin_smul_right (V := V') hf.differentiableWithinAt_comp_extChartAt_symm
      hW.differentiableWithinAt_mpullbackWithin_vectorField hs
  -- We prove the equality of each summand separately.
  rw [← Pi.add_def, mpullback_add_apply]; congr
  · simpa only [A] using! mpullback_mfderivWithin_apply_smul hf
  · simp [B, ← Pi.smul_def', mpullback_smul (V := lieBracketWithin 𝕜 V' W' s'), f']

/--
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a function
`f : M → 𝕜`, we have `[V, f • W] = (df V) • W + f • [V, W]`.
-/
/-
**VectorField.mlieBracket_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mlieBracket_smul_right {f : M -> 𝕜} (hf : MDiffAt f x) (hW : MDiffAt (fun 
x => (W x : TangentBundle I M)) x) : mlieBracket I V (f • W) x = d% f x (V x) • 
(W x) + (f x) • mlieBracket I V W x
参数：hf : MDiffAt f x；hW : MDiffAt (fun x => (W x : TangentBundle I M)) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `VectorField.mlieBracketWithin_univ`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [i
nst_2 : NormedAddCommGro…
· 使用定理 `mvfderivWithin_univ`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H 
: Type u_…
· 使用引理 `VectorField.mlieBracketWithin_smul_right`：mlieBracketWithin_smul_right {
f : M -> 𝕜} (hf : MDiffAt[s] f x) (hW : MDiffAt[s] (fun x => (W x : TangentBundl
e I M)) x) (hs : UniqueMDiffAt…
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用定理 `uniqueMDiffWithinAt_univ`：uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ
 : Set M)] x

--- 原说明 ---
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a 
function
`f : M → 𝕜`, we have `[V, f • W] = (df V) • W + f • [V, W]`.
-/
lemma mlieBracket_smul_right {f : M → 𝕜} (hf : MDiffAt f x)
    (hW : MDiffAt (fun x ↦ (W x : TangentBundle I M)) x) :
    mlieBracket I V (f • W) x = d% f x (V x) • (W x) + (f x) • mlieBracket I V W x := by
  rw [← mdifferentiableWithinAt_univ] at hf hW
  rw [← mlieBracketWithin_univ, ← mvfderivWithin_univ]
  exact mlieBracketWithin_smul_right hf hW (uniqueMDiffWithinAt_univ I)

/--
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a function
`f : M → 𝕜`, we have `[f • V, W] = -(df W) • V + f • [V, W]`. Version within a set.
-/
/-
**VectorField.mlieBracketWithin_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `VectorField
`。
形式化陈述：mlieBracketWithin_smul_left {f : M -> 𝕜} (hf : MDiffAt[s] f x) (hV : MDiff
At[s] (fun x => (V x : TangentBundle I M)) x) (hs : UniqueMDiffAt[s] x) : mlieBr
acketWithin I (f • V) W s x = - d[s] f x (W x) • (V x) + (f x) • mlieBracketWith
in I V W s x
参数：hf : MDiffAt[s] f x；hV : MDiffAt[s] (fun x => (V x : TangentBundle I M)) x；hs
 : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.mlieBracketWithin_swap`：mlieBracketWithin_swap : mlieBracket
Within I V W s = - mlieBracketWithin I W V s
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
· 使用引理 `VectorField.mlieBracketWithin_smul_right`：mlieBracketWithin_smul_right {
f : M -> 𝕜} (hf : MDiffAt[s] f x) (hW : MDiffAt[s] (fun x => (W x : TangentBundl
e I M)) x) (hs : UniqueMDiffAt…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `_private.Mathlib.Geometry.Manifold.VectorField.LieBracket.0.VectorField.
mlieBracketWithin_smul_left._abel_1_1`：∀ {𝕜 : Type u_2} [inst : NontriviallyNorm
edField 𝕜] {H : Type u_3} [inst_1 : TopologicalSpace H] {E : Type u_1}   [inst_2
 : NormedAddCommGro…

--- 原说明 ---
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a 
function
`f : M → 𝕜`, we have `[f • V, W] = -(df W) • V + f • [V, W]`. Version within a s
et.
-/
lemma mlieBracketWithin_smul_left {f : M → 𝕜} (hf : MDiffAt[s] f x)
    (hV : MDiffAt[s] (fun x ↦ (V x : TangentBundle I M)) x)
    (hs : UniqueMDiffAt[s] x) :
    mlieBracketWithin I (f • V) W s x =
      - d[s] f x (W x) • (V x) + (f x) • mlieBracketWithin I V W s x := by
  rw [mlieBracketWithin_swap, Pi.neg_apply, mlieBracketWithin_smul_right hf hV (V := W) hs,
    mlieBracketWithin_swap]
  simp; abel

/--
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a function
`f : M → 𝕜`, we have `[f • V, W] = -(df W) • V + f • [V, W]`.
-/
/-
**VectorField.mlieBracket_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mlieBracket_smul_left {f : M -> 𝕜} (hf : MDiffAt f x) (hV : MDiffAt (fun x
 => (V x : TangentBundle I M)) x) : mlieBracket I (f • V) W x = - d% f x (W x) •
 (V x) + (f x) • mlieBracket I V W x
参数：hf : MDiffAt f x；hV : MDiffAt (fun x => (V x : TangentBundle I M)) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `VectorField.mlieBracketWithin_univ`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [i
nst_2 : NormedAddCommGro…
· 使用定理 `mvfderiv.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : 
Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type
 u_…
· 使用定理 `mfderivWithin_univ`：mfderivWithin_univ : mfderiv[univ] f = mfderiv% f
· 使用引理 `VectorField.mlieBracketWithin_smul_left`：mlieBracketWithin_smul_left {f 
: M -> 𝕜} (hf : MDiffAt[s] f x) (hV : MDiffAt[s] (fun x => (V x : TangentBundle 
I M)) x) (hs : UniqueMDiffAt[…
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用定理 `uniqueMDiffWithinAt_univ`：uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ
 : Set M)] x

--- 原说明 ---
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a 
function
`f : M → 𝕜`, we have `[f • V, W] = -(df W) • V + f • [V, W]`.
-/
lemma mlieBracket_smul_left {f : M → 𝕜} (hf : MDiffAt f x)
    (hV : MDiffAt (fun x ↦ (V x : TangentBundle I M)) x) :
    mlieBracket I (f • V) W x = - d% f x (W x) • (V x) + (f x) • mlieBracket I V W x := by
  rw [← mdifferentiableWithinAt_univ] at hf hV
  rw [← mlieBracketWithin_univ, mvfderiv, ← mfderivWithin_univ]
  exact mlieBracketWithin_smul_left hf hV (uniqueMDiffWithinAt_univ I)
/-
**VectorField.mlieBracketWithin_const_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `Vecto
rField`。
形式化陈述：mlieBracketWithin_const_smul_left (hV : MDiffAt[s] (T% V) x) (hs : UniqueM
DiffAt[s] x) : mlieBracketWithin I (c • V) W s x = c • mlieBracketWithin I V W s
 x
参数：hV : MDiffAt[s] (T% V) x；hs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `mfderivWithin_const`：mfderivWithin_const : mfderiv[s] (fun _ : M => c) x
 = (0 : TangentSpace% x ->L[𝕜] TangentSpace% c)
· 使用定理 `ContinuousLinearMap.comp_zero`：comp_zero (g : M₂ ->SL[σ₂₃] M₃) : g ∘SL (
0 : M₁ ->SL[σ₁₂] M₂) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `VectorField.mlieBracketWithin_smul_left`：mlieBracketWithin_smul_left {f 
: M -> 𝕜} (hf : MDiffAt[s] f x) (hV : MDiffAt[s] (fun x => (V x : TangentBundle 
I M)) x) (hs : UniqueMDiffAt[…
· 使用定理 `mdifferentiableWithinAt_const`：mdifferentiableWithinAt_const : MDiffAt[s
] (fun _ : M => c) x
-/
lemma mlieBracketWithin_const_smul_left
    (hV : MDiffAt[s] (T% V) x) (hs : UniqueMDiffAt[s] x) :
    mlieBracketWithin I (c • V) W s x = c • mlieBracketWithin I V W s x := by
  simpa [mfderivWithin_const, mvfderivWithin] using!
    mlieBracketWithin_smul_left (mdifferentiableWithinAt_const (c := c)) (W := W) hV hs
/-
**VectorField.mlieBracket_const_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `VectorField
`。
形式化陈述：mlieBracket_const_smul_left (hV : MDiffAt (T% V) x) : mlieBracket I (c • V
) W x = c • mlieBracket I V W x
参数：hV : MDiffAt (T% V) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `VectorField.mlieBracketWithin_const_smul_left`：mlieBracketWithin_const_s
mul_left (hV : MDiffAt[s] (T% V) x) (hs : UniqueMDiffAt[s] x) : mlieBracketWithi
n I (c • V) W s x = c • mlieBracket…
· 使用定理 `uniqueMDiffWithinAt_univ`：uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ
 : Set M)] x
-/
lemma mlieBracket_const_smul_left (hV : MDiffAt (T% V) x) :
    mlieBracket I (c • V) W x = c • mlieBracket I V W x := by
  simp only [← mlieBracketWithin_univ] at hV ⊢
  exact mlieBracketWithin_const_smul_left hV (uniqueMDiffWithinAt_univ _)
/-
**VectorField.mlieBracketWithin_const_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `Vect
orField`。
形式化陈述：mlieBracketWithin_const_smul_right (hW : MDiffAt[s] (T% W) x) (hs : Unique
MDiffAt[s] x) : mlieBracketWithin I V (c • W) s x = c • mlieBracketWithin I V W 
s x
参数：hW : MDiffAt[s] (T% W) x；hs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `mfderivWithin_const`：mfderivWithin_const : mfderiv[s] (fun _ : M => c) x
 = (0 : TangentSpace% x ->L[𝕜] TangentSpace% c)
· 使用定理 `ContinuousLinearMap.comp_zero`：comp_zero (g : M₂ ->SL[σ₂₃] M₃) : g ∘SL (
0 : M₁ ->SL[σ₁₂] M₂) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `VectorField.mlieBracketWithin_smul_right`：mlieBracketWithin_smul_right {
f : M -> 𝕜} (hf : MDiffAt[s] f x) (hW : MDiffAt[s] (fun x => (W x : TangentBundl
e I M)) x) (hs : UniqueMDiffAt…
· 使用定理 `mdifferentiableWithinAt_const`：mdifferentiableWithinAt_const : MDiffAt[s
] (fun _ : M => c) x
-/
lemma mlieBracketWithin_const_smul_right
    (hW : MDiffAt[s] (T% W) x) (hs : UniqueMDiffAt[s] x) :
    mlieBracketWithin I V (c • W) s x = c • mlieBracketWithin I V W s x := by
  simpa [mfderivWithin_const, mvfderivWithin] using!
    mlieBracketWithin_smul_right (mdifferentiableWithinAt_const (c := c)) (V := V) hW hs
/-
**VectorField.mlieBracket_const_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `VectorFiel
d`。
形式化陈述：mlieBracket_const_smul_right (hW : MDiffAt (T% W) x) : mlieBracket I V (c 
• W) x = c • mlieBracket I V W x
参数：hW : MDiffAt (T% W) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `VectorField.mlieBracketWithin_const_smul_right`：mlieBracketWithin_const_
smul_right (hW : MDiffAt[s] (T% W) x) (hs : UniqueMDiffAt[s] x) : mlieBracketWit
hin I V (c • W) s x = c • mlieBracke…
· 使用定理 `uniqueMDiffWithinAt_univ`：uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ
 : Set M)] x
-/
lemma mlieBracket_const_smul_right (hW : MDiffAt (T% W) x) :
    mlieBracket I V (c • W) x = c • mlieBracket I V W x := by
  simp only [← mlieBracketWithin_univ] at hW ⊢
  exact mlieBracketWithin_const_smul_right hW (uniqueMDiffWithinAt_univ _)

set_option backward.isDefEq.respectTransparency false in
/-
**VectorField.mlieBracketWithin_add_left** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`
。
形式化陈述：mlieBracketWithin_add_left (hV : MDiffAt[s] (T% V) x) (hV₁ : MDiffAt[s] (T
% V₁) x) (hs : UniqueMDiffAt[s] x) : mlieBracketWithin I (V + V₁) W s x = mlieBr
acketWithin I V W s x + mlieBracketWithin I V₁ W s x
参数：hV : MDiffAt[s] (T% V) x；hV₁ : MDiffAt[s] (T% V₁) x；hs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.mlieBracketWithin_apply`：mlieBracketWithin_apply : mlieBrack
etWithin I V W s x₀ = (mfderiv% (extChartAt I x₀) x₀).inverse ((lieBracketWithin
 𝕜 (mpullbackWithin 𝓘(𝕜, …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用引理 `VectorField.mpullbackWithin_add`：mpullbackWithin_add : mpullbackWithin I
 I' f (V + V₁) s = mpullbackWithin I I' f V s + mpullbackWithin I I' f V₁ s
· 使用引理 `VectorField.lieBracketWithin_add_left`：lieBracketWithin_add_left (hV : D
ifferentiableWithinAt 𝕜 V s x) (hV₁ : DifferentiableWithinAt 𝕜 V₁ s x) (hs : Uni
queDiffWithinAt 𝕜 s x) : li…
· 使用定理 `MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorFie
ld`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 :
 TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniqueMDiffWithinAt_iff_inter_range`：uniqueMDiffWithinAt_iff_inter_range
 {s : Set M} {x : M} : UniqueMDiffAt[s] x ↔ UniqueDiffWithinAt 𝕜 ((extChartAt I 
x).symm ⁻¹' s inter range…
-/
lemma mlieBracketWithin_add_left
    (hV : MDiffAt[s] (T% V) x) (hV₁ : MDiffAt[s] (T% V₁) x) (hs : UniqueMDiffAt[s] x) :
    mlieBracketWithin I (V + V₁) W s x =
      mlieBracketWithin I V W s x + mlieBracketWithin I V₁ W s x := by
  simp only [mlieBracketWithin_apply]
  rw [← map_add, mpullbackWithin_add, lieBracketWithin_add_left]
  · exact hV.differentiableWithinAt_mpullbackWithin_vectorField
  · exact hV₁.differentiableWithinAt_mpullbackWithin_vectorField
  · exact uniqueMDiffWithinAt_iff_inter_range.1 hs
/-
**VectorField.mlieBracket_add_left** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mlieBracket_add_left (hV : MDiffAt (T% V) x) (hV₁ : MDiffAt (T% V₁) x) : m
lieBracket I (V + V₁) W x = mlieBracket I V W x + mlieBracket I V₁ W x
参数：hV : MDiffAt (T% V) x；hV₁ : MDiffAt (T% V₁) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `VectorField.mlieBracketWithin_add_left`：mlieBracketWithin_add_left (hV :
 MDiffAt[s] (T% V) x) (hV₁ : MDiffAt[s] (T% V₁) x) (hs : UniqueMDiffAt[s] x) : m
lieBracketWithin I (V + V₁) …
· 使用定理 `uniqueMDiffWithinAt_univ`：uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ
 : Set M)] x
-/
lemma mlieBracket_add_left (hV : MDiffAt (T% V) x) (hV₁ : MDiffAt (T% V₁) x) :
    mlieBracket I (V + V₁) W x = mlieBracket I V W x + mlieBracket I V₁ W x := by
  simp only [← mlieBracketWithin_univ] at hV hV₁ ⊢
  exact mlieBracketWithin_add_left hV hV₁ (uniqueMDiffWithinAt_univ _)
/-
**VectorField.mlieBracketWithin_add_right** 是 Mathlib 中的一个引理，位于命名空间 `VectorField
`。
形式化陈述：mlieBracketWithin_add_right (hW : MDiffAt[s] (T% W) x) (hW₁ : MDiffAt[s] (
T% W₁) x) (hs : UniqueMDiffAt[s] x) : mlieBracketWithin I V (W + W₁) s x = mlieB
racketWithin I V W s x + mlieBracketWithin I V W₁ s x
参数：hW : MDiffAt[s] (T% W) x；hW₁ : MDiffAt[s] (T% W₁) x；hs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.mlieBracketWithin_swap`：mlieBracketWithin_swap : mlieBracket
Within I V W s = - mlieBracketWithin I W V s
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
· 使用引理 `VectorField.mlieBracketWithin_add_left`：mlieBracketWithin_add_left (hV :
 MDiffAt[s] (T% V) x) (hV₁ : MDiffAt[s] (T% V₁) x) (hs : UniqueMDiffAt[s] x) : m
lieBracketWithin I (V + V₁) …
· 使用定理 `_private.Mathlib.Geometry.Manifold.VectorField.LieBracket.0.VectorField.
mlieBracketWithin_add_right._abel_1_1`：∀ {𝕜 : Type u_2} [inst : NontriviallyNorm
edField 𝕜] {H : Type u_3} [inst_1 : TopologicalSpace H] {E : Type u_1}   [inst_2
 : NormedAddCommGro…
-/
lemma mlieBracketWithin_add_right
    (hW : MDiffAt[s] (T% W) x) (hW₁ : MDiffAt[s] (T% W₁) x) (hs : UniqueMDiffAt[s] x) :
    mlieBracketWithin I V (W + W₁) s x =
      mlieBracketWithin I V W s x + mlieBracketWithin I V W₁ s x := by
  rw [mlieBracketWithin_swap, Pi.neg_apply, mlieBracketWithin_add_left hW hW₁ hs,
    mlieBracketWithin_swap (V := V), mlieBracketWithin_swap (V := V), Pi.neg_apply, Pi.neg_apply]
  abel
/-
**VectorField.mlieBracket_add_right** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mlieBracket_add_right (hW : MDiffAt (T% W) x) (hW₁ : MDiffAt (T% W₁) x) : 
mlieBracket I V (W + W₁) x = mlieBracket I V W x + mlieBracket I V W₁ x
参数：hW : MDiffAt (T% W) x；hW₁ : MDiffAt (T% W₁) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `VectorField.mlieBracketWithin_add_right`：mlieBracketWithin_add_right (hW
 : MDiffAt[s] (T% W) x) (hW₁ : MDiffAt[s] (T% W₁) x) (hs : UniqueMDiffAt[s] x) :
 mlieBracketWithin I V (W + W…
· 使用定理 `uniqueMDiffWithinAt_univ`：uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ
 : Set M)] x
-/
lemma mlieBracket_add_right (hW : MDiffAt (T% W) x) (hW₁ : MDiffAt (T% W₁) x) :
    mlieBracket I V (W + W₁) x = mlieBracket I V W x + mlieBracket I V W₁ x := by
  simp only [← mlieBracketWithin_univ] at hW hW₁ ⊢
  exact mlieBracketWithin_add_right hW hW₁ (uniqueMDiffWithinAt_univ _)

set_option backward.isDefEq.respectTransparency false in
/-
**VectorField.mlieBracketWithin_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `Vec
torField`。
形式化陈述：mlieBracketWithin_of_mem_nhdsWithin (st : t in 𝓝[s] x) (hs : UniqueMDiffAt
[s] x) (hV : MDiffAt[t] (T% V) x) (hW : MDiffAt[t] (T% W) x) : mlieBracketWithin
 I V W s x = mlieBracketWithin I V W t x
参数：st : t in 𝓝[s] x；hs : UniqueMDiffAt[s] x；hV : MDiffAt[t] (T% V) x；hW : MDiffA
t[t] (T% W) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.mlieBracketWithin_apply`：mlieBracketWithin_apply : mlieBrack
etWithin I V W s x₀ = (mfderiv% (extChartAt I x₀) x₀).inverse ((lieBracketWithin
 𝕜 (mpullbackWithin 𝓘(𝕜, …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `VectorField.lieBracketWithin_of_mem_nhdsWithin`：lieBracketWithin_of_mem_
nhdsWithin (st : t in 𝓝[s] x) (hs : UniqueDiffWithinAt 𝕜 s x) (hV : Differentiab
leWithinAt 𝕜 V t x) (hW : Differenti…
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin''`：ContinuousWithinAt.preimag
e_mem_nhdsWithin'' {y : β} {s t : Set β} (h : ContinuousWithinAt f (f ⁻¹' s) x) 
(ht : t in 𝓝[s] y) (hxy : y = f x)…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `continuousAt_extChartAt_symm`：continuousAt_extChartAt_symm (x : M) : Con
tinuousAt (extChartAt I x).symm ((extChartAt I x) x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniqueMDiffWithinAt_iff_inter_range`：uniqueMDiffWithinAt_iff_inter_range
 {s : Set M} {x : M} : UniqueMDiffAt[s] x ↔ UniqueDiffWithinAt 𝕜 ((extChartAt I 
x).symm ⁻¹' s inter range…
· 使用定理 `MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorFie
ld`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 :
 TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddCommGro…
-/
theorem mlieBracketWithin_of_mem_nhdsWithin (st : t ∈ 𝓝[s] x) (hs : UniqueMDiffAt[s] x)
    (hV : MDiffAt[t] (T% V) x) (hW : MDiffAt[t] (T% W) x) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x := by
  simp only [mlieBracketWithin_apply]
  congr 1
  rw [lieBracketWithin_of_mem_nhdsWithin]
  · apply Filter.inter_mem
    · apply nhdsWithin_mono _ inter_subset_left <|
        (continuousAt_extChartAt_symm x).continuousWithinAt.preimage_mem_nhdsWithin'' st (by simp)
    · exact nhdsWithin_mono _ inter_subset_right self_mem_nhdsWithin
  · exact uniqueMDiffWithinAt_iff_inter_range.1 hs
  · exact hV.differentiableWithinAt_mpullbackWithin_vectorField
  · exact hW.differentiableWithinAt_mpullbackWithin_vectorField
/-
**VectorField.mlieBracketWithin_subset** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：mlieBracketWithin_subset (st : s subseteq t) (ht : UniqueMDiffAt[s] x) (hV
 : MDiffAt[t] (T% V) x) (hW : MDiffAt[t] (T% W) x) : mlieBracketWithin I V W s x
 = mlieBracketWithin I V W t x
参数：st : s subseteq t；ht : UniqueMDiffAt[s] x；hV : MDiffAt[t] (T% V) x；hW : MDiff
At[t] (T% W) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `VectorField.mlieBracketWithin_of_mem_nhdsWithin`：mlieBracketWithin_of_me
m_nhdsWithin (st : t in 𝓝[s] x) (hs : UniqueMDiffAt[s] x) (hV : MDiffAt[t] (T% V
) x) (hW : MDiffAt[t] (T% W) x) : mli…
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem mlieBracketWithin_subset (st : s ⊆ t) (ht : UniqueMDiffAt[s] x)
    (hV : MDiffAt[t] (T% V) x) (hW : MDiffAt[t] (T% W) x) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x :=
  mlieBracketWithin_of_mem_nhdsWithin (nhdsWithin_mono _ st self_mem_nhdsWithin) ht hV hW
/-
**VectorField.mlieBracketWithin_eq_mlieBracket** 是 Mathlib 中的一个定理，位于命名空间 `Vector
Field`。
形式化陈述：mlieBracketWithin_eq_mlieBracket (hs : UniqueMDiffAt[s] x) (hV : MDiffAt (
T% V) x) (hW : MDiffAt (T% W) x) : mlieBracketWithin I V W s x = mlieBracket I V
 W x
参数：hs : UniqueMDiffAt[s] x；hV : MDiffAt (T% V) x；hW : MDiffAt (T% W) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `VectorField.mlieBracketWithin_subset`：mlieBracketWithin_subset (st : s s
ubseteq t) (ht : UniqueMDiffAt[s] x) (hV : MDiffAt[t] (T% V) x) (hW : MDiffAt[t]
 (T% W) x) : mlieBracketWi…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem mlieBracketWithin_eq_mlieBracket (hs : UniqueMDiffAt[s] x)
    (hV : MDiffAt (T% V) x) (hW : MDiffAt (T% W) x) :
    mlieBracketWithin I V W s x = mlieBracket I V W x := by
  simp only [← mlieBracketWithin_univ, ← mdifferentiableWithinAt_univ] at hV hW ⊢
  exact mlieBracketWithin_subset (subset_univ _) hs hV hW
/-
**VectorField._root_.DifferentiableWithinAt.mlieBracketWithin_congr_mono** 是 Mat
hlib 中的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.DifferentiableWithinAt.mlieBracketWithin_congr_mono
    (hV : MDiffAt[s] (T% V) x) (hVs : EqOn V₁ V t) (hVx : V₁ x = V x)
    (hW : MDiffAt[s] (T% W) x) (hWs : EqOn W₁ W t) (hWx : W₁ x = W x)
    (hxt : UniqueMDiffAt[t] x) (h₁ : t ⊆ s) :
    mlieBracketWithin I V₁ W₁ t x = mlieBracketWithin I V W s x := by
  rw [mlieBracketWithin_congr hVs hVx hWs hWx]
  exact mlieBracketWithin_subset h₁ hxt hV hW

end

section Invariance_IsSymmSndFDerivWithinAt

variable [IsManifold I 2 M] [IsManifold I' 2 M'] [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in
/- The Lie bracket of vector fields on manifolds is well defined, i.e., it is invariant under
diffeomorphisms. Auxiliary version where one assumes that all relevant sets are contained
in chart domains. -/
/-
**VectorField.mpullbackWithin_mlieBracketWithin_aux** 是 Mathlib 中的一个引理，位于命名空间 `V
ectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lie bracket of vector fields on manifolds is well defined, i.e., it is invar
iant under
diffeomorphisms. Auxiliary version where one assumes that all relevant sets are 
contained
in chart domains.
-/
private lemma mpullbackWithin_mlieBracketWithin_aux [CompleteSpace E']
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀))
    (hu : UniqueMDiff[s]) (hf : CMDiff[s] 2 f) (hx₀ : x₀ ∈ s)
    (ht : t ⊆ (extChartAt I' (f x₀)).source) (hst : MapsTo f s t)
    (hsymm : IsSymmSndFDerivWithinAt 𝕜 ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I) (extChartAt I x₀ x₀)) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ =
      mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ := by
  have A : (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ := by simp
  have A' : x₀ = (extChartAt I x₀).symm (extChartAt I x₀ x₀) := by simp
  have h'f : MDiffAt[s] f x₀ := (hf x₀ hx₀).mdifferentiableWithinAt two_ne_zero
  simp only [mlieBracketWithin_apply, mpullbackWithin_apply]
  -- first, rewrite the pullback of the Lie bracket as a pullback in `E` under the map
  -- `F = extChartAt I' (f x₀) ∘ f ∘ (extChartAt I x₀).symm` of a Lie bracket computed in `E'`,
  -- of two vector fields `V'` and `W'`.
  rw [← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_left
    (isInvertible_mfderiv_extChartAt (mem_extChartAt_source (f x₀)))]
  rw [← mfderiv_comp_mfderivWithin _ (mdifferentiableAt_extChartAt
    (ChartedSpace.mem_chart_source (f x₀))) h'f (hu x₀ hx₀)]
  rw [eq_comm, (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x₀)).inverse_apply_eq]
  have : (mfderiv[range I] (extChartAt I x₀).symm (extChartAt I x₀ x₀)).inverse =
      mfderiv% (extChartAt I x₀) x₀ := by
    apply ContinuousLinearMap.inverse_eq
    · convert!
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) (x := x₀) (y :=
        extChartAt I x₀ x₀) (by simp)
    · convert!
      mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x₀) (y :=
        extChartAt I x₀ x₀) (by simp)
  rw [← this, ← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_right]; swap
  · exact isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target x₀)
  have : mfderiv[range I] (extChartAt I x₀).symm (extChartAt I x₀ x₀) =
      mfderiv[(extChartAt I x₀).symm ⁻¹' s ∩ range I] (extChartAt I x₀).symm (extChartAt I x₀ x₀) :=
    (MDifferentiableWithinAt.mfderivWithin_mono
      (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x₀))
      (UniqueDiffWithinAt.uniqueMDiffWithinAt (hu x₀ hx₀)) inter_subset_right).symm
  rw [this]; clear this
  rw [← mfderivWithin_comp_of_eq]; rotate_left
  · apply MDifferentiableAt.comp_mdifferentiableWithinAt (I' := I') _ _ h'f
    exact mdifferentiableAt_extChartAt (ChartedSpace.mem_chart_source (f x₀))
  · exact (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x₀)).mono
      inter_subset_right
  · exact inter_subset_left
  · exact UniqueDiffWithinAt.uniqueMDiffWithinAt (hu x₀ hx₀)
  · simp
  set V' := mpullbackWithin 𝓘(𝕜, E') I' (extChartAt I' (f x₀)).symm V (range I') with hV'
  set W' := mpullbackWithin 𝓘(𝕜, E') I' (extChartAt I' (f x₀)).symm W (range I') with hW'
  set F := ((extChartAt I' (f x₀)) ∘ f) ∘ ↑(extChartAt I x₀).symm with hF
  have hFx₀ : extChartAt I' (f x₀) (f x₀) = F (extChartAt I x₀ x₀) := by simp [F]
  rw [hFx₀, ← mpullbackWithin_apply]
  -- second rewrite, the Lie bracket of the pullback as the Lie bracket of the pullback of the
  -- vector fields `V'` and `W'` in `E'`.
  have P (Y : (x : M') → TangentSpace I' x) :
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (mpullbackWithin I I' f Y s)
      (range I)) =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' s ∩ range I] (extChartAt I x₀ x₀)]
        mpullbackWithin 𝓘(𝕜, E) 𝓘(𝕜, E') F
          (mpullbackWithin 𝓘(𝕜, E') I' ((extChartAt I' (f x₀)).symm) Y (range I'))
          ((extChartAt I x₀).symm ⁻¹' s ∩ range I) := by
    have : (extChartAt I x₀).target
        ∈ 𝓝[(extChartAt I x₀).symm ⁻¹' s ∩ range I] (extChartAt I x₀ x₀) :=
      nhdsWithin_mono _ inter_subset_right (extChartAt_target_mem_nhdsWithin x₀)
    filter_upwards [self_mem_nhdsWithin, this] with y hy h'''y
    have h'y : f ((extChartAt I x₀).symm y) ∈ (extChartAt I' (f x₀)).source := ht (hst hy.1)
    have h''y : f ((extChartAt I x₀).symm y) ∈ (chartAt H' (f x₀)).source := by simpa using h'y
    have huy : UniqueMDiffAt[(extChartAt I x₀).symm ⁻¹' s ∩ range I] y := by
      apply UniqueDiffWithinAt.uniqueMDiffWithinAt
      rw [inter_comm]
      apply hu.uniqueDiffWithinAt_range_inter
      exact ⟨h'''y, hy.1⟩
    simp only [mpullbackWithin_apply, hF, comp_apply]
    rw [mfderivWithin_comp (I' := I) (u := s)]; rotate_left
    · apply (mdifferentiableAt_extChartAt h''y).comp_mdifferentiableWithinAt (I' := I')
      exact (hf _ hy.1).mdifferentiableWithinAt two_ne_zero
    · exact (mdifferentiableWithinAt_extChartAt_symm h'''y).mono inter_subset_right
    · exact inter_subset_left
    · exact huy
    rw [mfderiv_comp_mfderivWithin (I' := I')]; rotate_left
    · exact mdifferentiableAt_extChartAt h''y
    · exact (hf _ hy.1).mdifferentiableWithinAt two_ne_zero
    · exact hu _ hy.1
    rw [← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_right]; swap
    · exact isInvertible_mfderivWithin_extChartAt_symm h'''y
    rw [← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_left]; swap
    · exact isInvertible_mfderivWithin_extChartAt_symm (PartialEquiv.map_source _ h'y)
    have : f ((extChartAt I x₀).symm y)
        = (extChartAt I' (f x₀)).symm ((extChartAt I' (f x₀)) (f ((extChartAt I x₀).symm y))) :=
      (PartialEquiv.left_inv (extChartAt I' (f x₀)) h'y).symm
    congr 2
    have : (mfderiv[range I'] ((extChartAt I' (f x₀)).symm)
        (extChartAt I' (f x₀) (f ((extChartAt I x₀).symm y)))) ∘L
        (mfderiv% (extChartAt I' (f x₀)) (f ((extChartAt I x₀).symm y))) =
        ContinuousLinearMap.id _ _ := by
      convert!
        mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt ((PartialEquiv.map_source _ h'y))
    simp only [← ContinuousLinearMap.comp_assoc, this, ContinuousLinearMap.id_comp]
    congr 1
    exact ((mdifferentiableWithinAt_extChartAt_symm h'''y).mfderivWithin_mono huy
      inter_subset_right).symm
  rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem (P V) (P W) (by simp [hx₀]),
    ← hV', ← hW']
  simp only [mpullbackWithin_eq_pullbackWithin]
  -- finally, use the fact that for `C^2` maps between vector spaces with symmetric second
  -- derivative, the pullback and the Lie bracket commute.
  rw [pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt_of_eventuallyEq
      (u := (extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target)]
  · exact hsymm
  · rw [hF, comp_assoc]
    apply ContMDiffWithinAt.contDiffWithinAt
    apply ContMDiffAt.comp_contMDiffWithinAt (I' := I')
    · exact contMDiffAt_extChartAt' (by simp)
    apply ContMDiffWithinAt.comp_of_eq (I' := I) (hf _ hx₀) _ _ A
    · exact (contMDiffWithinAt_extChartAt_symm_range _ (mem_extChartAt_target x₀)).mono
        inter_subset_right
    · exact (mapsTo_preimage _ _).mono_left inter_subset_left
  · rw [← hFx₀]
    exact hV.differentiableWithinAt_mpullbackWithin_vectorField
  · rw [← hFx₀]
    exact hW.differentiableWithinAt_mpullbackWithin_vectorField
  · rw [inter_comm]
    exact UniqueMDiffOn.uniqueDiffOn_target_inter hu x₀
  · simp [hx₀]
  · intro z hz
    simp only [comp_apply, mem_inter_iff, mem_preimage, mem_range, F]
    refine ⟨?_, mem_range_self _⟩
    convert! hst hz.1
    exact PartialEquiv.left_inv (extChartAt I' (f x₀)) (ht (hst hz.1))
  · rw [← nhdsWithin_eq_iff_eventuallyEq]
    apply le_antisymm
    · exact nhdsWithin_mono _ (inter_subset_inter_right _ (extChartAt_target_subset_range x₀))
    · rw [nhdsWithin_le_iff, nhdsWithin_inter]
      exact Filter.inter_mem_inf self_mem_nhdsWithin (extChartAt_target_mem_nhdsWithin x₀)

set_option backward.isDefEq.respectTransparency false in
/- The Lie bracket of vector fields on manifolds is well defined, i.e., it is invariant under
diffeomorphisms. -/
/-
**VectorField.mpullbackWithin_mlieBracketWithin_of_isSymmSndFDerivWithinAt** 是 M
athlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullbackWithin_mlieBracketWithin_of_isSymmSndFDerivWithinAt {f : M -> M'}
 {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'} (hV : M
DiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀)) (hu : UniqueMDiff[s]) (
hf : CMDiffAt[s] 2 f x₀) (hx₀ : x₀ in s) (hst : f ⁻¹' t in 𝓝[s] x₀) (hsymm : IsS
ymmSndFDerivWithinAt 𝕜 ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm) ((e
xtChartAt I x₀).symm ⁻¹' s inter range I) (extChartAt I x₀ x₀)) : mpullbackWithi
n I I' f (mlieBracketWithi
参数：x : M'；hV : MDiffAt[t] (T% V) (f x₀)；hW : MDiffAt[t] (T% W) (f x₀)；hu : Uniqu
eMDiff[s]；hf : CMDiffAt[s] 2 f x₀；hx₀ : x₀ in s；hst : f ⁻¹' t in 𝓝[s] x₀；hsymm :
 IsSymmSndFDerivWithinAt 𝕜 ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm)
 ((extChartAt I x₀).symm ⁻¹' s inter range I) (extChartAt I x₀ x₀)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `completeSpace_congr`：completeSpace_congr {e : α ≃ β} (he : IsUniformEmbe
dding e) : CompleteSpace α ↔ CompleteSpace β
· 使用引理 `ContinuousLinearEquiv.isUniformEmbedding`：isUniformEmbedding {E₁ E₂ : Ty
pe*} [UniformSpace E₁] [UniformSpace E₂] [AddCommGroup E₁] [AddCommGroup E₂] [Mo
dule R₁ E₁] [Module R₂ E₂] [Is…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `ContMDiffWithinAt.contMDiffOn'`：ContMDiffWithinAt.contMDiffOn' [IsManifo
ld I n M] [IsManifold I' n M'] (hm : m <= n) (h' : m = ∞ -> n = ω) (h : ContMDif
fWithinAt I I' n f s…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin`：ContinuousWithinAt.preimage_
mem_nhdsWithin {t : Set β} (h : ContinuousWithinAt f s x) (ht : t in 𝓝 (f x)) : 
f ⁻¹' t in 𝓝[s] x
· 使用定理 `ContMDiffWithinAt.continuousWithinAt`：ContMDiffWithinAt.continuousWithin
At (hf : ContMDiffWithinAt I I' n f s x) : ContinuousWithinAt f s x
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
The Lie bracket of vector fields on manifolds is well defined, i.e., it is invar
iant under
diffeomorphisms.
-/
lemma mpullbackWithin_mlieBracketWithin_of_isSymmSndFDerivWithinAt
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀))
    (hu : UniqueMDiff[s]) (hf : CMDiffAt[s] 2 f x₀) (hx₀ : x₀ ∈ s)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hsymm : IsSymmSndFDerivWithinAt 𝕜 ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I) (extChartAt I x₀ x₀)) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ =
      mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ := by
  have A : (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ := by simp
  by_cases hfi : (mfderiv[s] f x₀).IsInvertible; swap
  · simp only [mlieBracketWithin_apply, mpullbackWithin_apply,
      ContinuousLinearMap.inverse_of_not_isInvertible hfi, zero_apply]
    rw [lieBracketWithin_eq_zero_of_eq_zero]
    · simp [-extChartAt]
    · simp only [mpullbackWithin_apply]
      rw [A, ContinuousLinearMap.inverse_of_not_isInvertible hfi]
      simp [-extChartAt]
    · simp only [mpullbackWithin_apply]
      rw [A, ContinuousLinearMap.inverse_of_not_isInvertible hfi]
      simp [-extChartAt]
  -- Now, interesting case where the derivative of `f` is invertible
  have : CompleteSpace E' := by
    rcases hfi with ⟨M, -⟩
    let M' : E ≃L[𝕜] E' := M
    exact (completeSpace_congr (e := M'.toEquiv) M'.isUniformEmbedding).1 (by assumption)
  -- choose a small open set `v` around `x₀` where `f` is `C^2`
  obtain ⟨u, u_open, x₀u, ut, maps_u, u_smooth⟩ :
      ∃ u, IsOpen u ∧ x₀ ∈ u ∧ s ∩ u ⊆ f ⁻¹' t ∧
        s ∩ u ⊆ f ⁻¹' (extChartAt I' (f x₀)).source ∧ CMDiff[s ∩ u] 2 f := by
    obtain ⟨u, u_open, x₀u, hu⟩ : ∃ u, IsOpen u ∧ x₀ ∈ u ∧ CMDiff[insert x₀ s ∩ u] 2 f :=
      hf.contMDiffOn' le_rfl (by simp)
    have : f ⁻¹' (extChartAt I' (f x₀)).source ∈ 𝓝[s] x₀ :=
      hf.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (f x₀))
    rcases mem_nhdsWithin.1 (Filter.inter_mem hst this) with ⟨w, w_open, x₀w, hw⟩
    refine ⟨u ∩ w, u_open.inter w_open, by simp [x₀u, x₀w], ?_, ?_, ?_⟩
    · apply Subset.trans _ (hw.trans inter_subset_left)
      exact fun y hy ↦ ⟨hy.2.2, hy.1⟩
    · apply Subset.trans _ (hw.trans inter_subset_right)
      exact fun y hy ↦ ⟨hy.2.2, hy.1⟩
    · apply hu.mono
      exact fun y hy ↦ ⟨subset_insert _ _ hy.1, hy.2.1⟩
  have u_mem : u ∈ 𝓝 x₀ := u_open.mem_nhds x₀u
  -- apply the auxiliary version to `s ∩ u`
  set s' := s ∩ u with hs'
  have s'_eq : s' =ᶠ[𝓝 x₀] s := by
    filter_upwards [u_mem] with y hy
    change (y ∈ s ∩ u) = (y ∈ s)
    simp [hy]
  set t' := t ∩ (extChartAt I' (f x₀)).source with ht'
  calc mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀
  _ = mpullbackWithin I I' f (mlieBracketWithin I' V W t) s' x₀ := by
    simp only [mpullbackWithin, hs', mfderivWithin_inter u_mem]
  _ = mpullbackWithin I I' f (mlieBracketWithin I' V W t') s' x₀ := by
    simp only [mpullbackWithin, ht', mlieBracketWithin_inter (extChartAt_source_mem_nhds (f x₀))]
  _ = mlieBracketWithin I (mpullbackWithin I I' f V s') (mpullbackWithin I I' f W s') s' x₀ := by
    apply mpullbackWithin_mlieBracketWithin_aux (t := t') (hV.mono inter_subset_left)
      (hW.mono inter_subset_left) (hu.inter u_open) u_smooth ⟨hx₀, x₀u⟩ inter_subset_right
      (fun y hy ↦ ⟨ut hy, maps_u hy⟩)
    apply hsymm.congr_set
    have : (extChartAt I x₀).symm ⁻¹' u ∈ 𝓝 (extChartAt I x₀ x₀) := by
      apply (continuousAt_extChartAt_symm x₀).preimage_mem_nhds
      apply u_open.mem_nhds (by simpa using x₀u)
    filter_upwards [this] with y hy
    change (y ∈ (extChartAt I x₀).symm ⁻¹' s ∩ range I) =
      (y ∈ (extChartAt I x₀).symm ⁻¹' (s ∩ u) ∩ range I)
    simp [-extChartAt, hy]
  _ = mlieBracketWithin I (mpullbackWithin I I' f V s') (mpullbackWithin I I' f W s') s x₀ := by
    simp only [hs', mlieBracketWithin_inter u_mem]
  _ = mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ := by
    apply Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem _ _ hx₀
    · apply nhdsWithin_le_nhds
      filter_upwards [mfderivWithin_eventually_congr_set (I := I) (I' := I') (f := f) s'_eq]
        with y hy using by simp [mpullbackWithin, hy]
    · apply nhdsWithin_le_nhds
      filter_upwards [mfderivWithin_eventually_congr_set (I := I) (I' := I') (f := f) s'_eq]
        with y hy using by simp [mpullbackWithin, hy]

end Invariance_IsSymmSndFDerivWithinAt

section Invariance

variable [IsManifold I (minSmoothness 𝕜 2) M] [IsManifold I' (minSmoothness 𝕜 2) M']
  [CompleteSpace E] {n : ℕ∞ω}

/-- The pullback commutes with the Lie bracket of vector fields on manifolds. Version where one
assumes that the map is smooth on a larger set `u` (so that the
condition `x₀ ∈ closure (interior u)`, needed to guarantee the symmetry of the second derivative,
becomes easier to check.) -/
/-
**VectorField.mpullbackWithin_mlieBracketWithin'** 是 Mathlib 中的一个引理，位于命名空间 `Vect
orField`。
形式化陈述：mpullbackWithin_mlieBracketWithin' {f : M -> M'} {V W : Π (x : M'), Tangen
tSpace I' x} {x₀ : M} {s u : Set M} {t : Set M'} (hV : MDiffAt[t] (T% V) (f x₀))
 (hW : MDiffAt[t] (T% W) (f x₀)) (hs : UniqueMDiff[s]) (hu : UniqueMDiff[u]) (hf
 : CMDiffAt[u] n f x₀) (hx₀ : x₀ in s) (hn : minSmoothness 𝕜 2 <= n) (hst : f ⁻¹
' t in 𝓝[s] x₀) (h'x₀ : x₀ in closure (interior u)) (hsu : s subseteq u) : mpull
backWithin I I' f (mlieBracketWithin I' V W t) s x₀ = mlieBracketWithin I (mpull
backWithin I I' f V s) (mp
参数：x : M'；hV : MDiffAt[t] (T% V) (f x₀)；hW : MDiffAt[t] (T% W) (f x₀)；hs : Uniqu
eMDiff[s]；hu : UniqueMDiff[u]；hf : CMDiffAt[u] n f x₀；hx₀ : x₀ in s；hn : minSmoo
thness 𝕜 2 <= n；hst : f ⁻¹' t in 𝓝[s] x₀；h'x₀ : x₀ in closure (interior u)；hsu :
 s subseteq u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsManifoldOfNatWithTopENatOfMinSmoothness_1`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : T
ype u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : 
NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Typ
e u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `ContDiffWithinAt.congr_set`：ContDiffWithinAt.congr_set (h : ContDiffWith
inAt 𝕜 n f s x) {t : Set E} (hst : s =ᶠ[𝓝 x] t) : ContDiffWithinAt 𝕜 n f t x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contMDiffWithinAt_iff`：contMDiffWithinAt_iff : ContMDiffWithinAt I I' n 
f s x ↔ ContinuousWithinAt f s x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f
 ∘ (extChar…
· 使用定理 `Filter.EventuallyEq.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∩ s' =ᶠ[l] t ∩ t'
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `extChartAt_target_eventuallyEq`：extChartAt_target_eventuallyEq {x : M} :
 (extChartAt I x).target =ᶠ[𝓝 (extChartAt I x x)] range I
· 使用引理 `VectorField.mpullbackWithin_mlieBracketWithin_of_isSymmSndFDerivWithinAt
`：mpullbackWithin_mlieBracketWithin_of_isSymmSndFDerivWithinAt {f : M -> M'} {V 
W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : S…
· 使用定理 `instIsManifoldOfNatWithTopENatOfMinSmoothness`：∀ {𝕜 : Type u_1} [inst : 
NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Typ
e u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `ContMDiffWithinAt.of_le`：ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt
 I I' n f s x) (le : m <= n) : ContMDiffWithinAt I I' m f s x
· 使用定理 `ContMDiffWithinAt.mono`：ContMDiffWithinAt.mono (hf : ContMDiffWithinAt I
 I' n f s x) (hts : t subseteq s) : ContMDiffWithinAt I I' n f t x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_minSmoothness`：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n
· 使用定理 `IsSymmSndFDerivWithinAt.congr_set`：IsSymmSndFDerivWithinAt.congr_set (h 
: IsSymmSndFDerivWithinAt 𝕜 f s x) (hst : s =ᶠ[𝓝 x] t) : IsSymmSndFDerivWithinAt
 𝕜 f t x
· 使用定理 `ContDiffWithinAt.isSymmSndFDerivWithinAt`：ContDiffWithinAt.isSymmSndFDer
ivWithinAt {n : Nat∞ω} (hf : ContDiffWithinAt 𝕜 n f s x) (hn : minSmoothness 𝕜 2
 <= n) (hs : UniqueDiffOn 𝕜 s)…
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `UniqueMDiffOn.uniqueDiffOn_target_inter`：UniqueMDiffOn.uniqueDiffOn_targ
et_inter (hs : UniqueMDiff[s]) (x : M) : UniqueDiffOn 𝕜 ((extChartAt I x).target
 inter (extChartAt I x).symm …
· 使用引理 `extChartAt_mem_closure_interior`：extChartAt_mem_closure_interior {x₀ x :
 M} (hx : x in closure (interior s)) (h'x : x in (extChartAt I x₀).source) : ext
ChartAt I x₀ x in clo…
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The pullback commutes with the Lie bracket of vector fields on manifolds. Versio
n where one
assumes that the map is smooth on a larger set `u` (so that the
condition `x₀ ∈ closure (interior u)`, needed to guarantee the symmetry of the s
econd derivative,
becomes easier to check.)
-/
lemma mpullbackWithin_mlieBracketWithin'
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s u : Set M} {t : Set M'}
    (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀))
    (hs : UniqueMDiff[s]) (hu : UniqueMDiff[u])
    (hf : CMDiffAt[u] n f x₀) (hx₀ : x₀ ∈ s) (hn : minSmoothness 𝕜 2 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (h'x₀ : x₀ ∈ closure (interior u)) (hsu : s ⊆ u) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ =
      mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ := by
  have B : ContDiffWithinAt 𝕜 n ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).symm ⁻¹' u ∩ (extChartAt I x₀).target) (extChartAt I x₀ x₀) := by
    apply (contMDiffWithinAt_iff.1 hf).2.congr_set
    exact EventuallyEq.inter (by rfl) extChartAt_target_eventuallyEq.symm
  apply mpullbackWithin_mlieBracketWithin_of_isSymmSndFDerivWithinAt hV hW hs
    ((hf.mono hsu).of_le (le_minSmoothness.trans hn)) hx₀ hst
  have : ((extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target : Set E)
      =ᶠ[𝓝 (extChartAt I x₀ x₀)] ((extChartAt I x₀).symm ⁻¹' s ∩ range I : Set E) :=
    EventuallyEq.inter (by rfl) extChartAt_target_eventuallyEq
  apply IsSymmSndFDerivWithinAt.congr_set _ this
  have : IsSymmSndFDerivWithinAt 𝕜 ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).symm ⁻¹' u ∩ (extChartAt I x₀).target) (extChartAt I x₀ x₀) := by
    apply ContDiffWithinAt.isSymmSndFDerivWithinAt (n := minSmoothness 𝕜 2) _ le_rfl
    · rw [inter_comm]
      exact UniqueMDiffOn.uniqueDiffOn_target_inter hu x₀
    · apply extChartAt_mem_closure_interior h'x₀ (mem_extChartAt_source x₀)
    · simp [hsu hx₀]
    · exact B.of_le hn
  apply IsSymmSndFDerivWithinAt.mono_of_mem_nhdsWithin this
  · apply mem_of_superset self_mem_nhdsWithin (inter_subset_inter_left _ (preimage_mono hsu))
  · exact (B.of_le hn).of_le le_minSmoothness
  · rw [inter_comm]
    exact UniqueMDiffOn.uniqueDiffOn_target_inter hs x₀
  · rw [inter_comm]
    exact UniqueMDiffOn.uniqueDiffOn_target_inter hu x₀
  · simp [hx₀]

/-- The pullback commutes with the Lie bracket of vector fields on manifolds. -/
/-
**VectorField.mpullbackWithin_mlieBracketWithin** 是 Mathlib 中的一个引理，位于命名空间 `Vecto
rField`。
形式化陈述：mpullbackWithin_mlieBracketWithin {f : M -> M'} {V W : Π (x : M'), Tangent
Space I' x} {x₀ : M} {s : Set M} {t : Set M'} (hV : MDiffAt[t] (T% V) (f x₀)) (h
W : MDiffAt[t] (T% W) (f x₀)) (hu : UniqueMDiff[s]) (hf : CMDiffAt[s] n f x₀) (h
x₀ : x₀ in s) (hn : minSmoothness 𝕜 2 <= n) (hst : f ⁻¹' t in 𝓝[s] x₀) (h'x₀ : x
₀ in closure (interior s)) : mpullbackWithin I I' f (mlieBracketWithin I' V W t)
 s x₀ = mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f
 W s) s x₀
参数：x : M'；hV : MDiffAt[t] (T% V) (f x₀)；hW : MDiffAt[t] (T% W) (f x₀)；hu : Uniqu
eMDiff[s]；hf : CMDiffAt[s] n f x₀；hx₀ : x₀ in s；hn : minSmoothness 𝕜 2 <= n；hst 
: f ⁻¹' t in 𝓝[s] x₀；h'x₀ : x₀ in closure (interior s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsManifoldOfNatWithTopENatOfMinSmoothness_1`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : T
ype u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : 
NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Typ
e u_3}   [inst_2 : NormedAddCommGro…
· 使用引理 `VectorField.mpullbackWithin_mlieBracketWithin'`：mpullbackWithin_mlieBrac
ketWithin' {f : M -> M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s u : S
et M} {t : Set M'} (hV : MDiffAt[t] …
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
The pullback commutes with the Lie bracket of vector fields on manifolds.
-/
lemma mpullbackWithin_mlieBracketWithin
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀))
    (hu : UniqueMDiff[s]) (hf : CMDiffAt[s] n f x₀) (hx₀ : x₀ ∈ s)
    (hn : minSmoothness 𝕜 2 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (h'x₀ : x₀ ∈ closure (interior s)) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ =
      mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ :=
  mpullbackWithin_mlieBracketWithin' hV hW hu hu hf hx₀ hn hst h'x₀ Subset.rfl

/-- The pullback commutes with the Lie bracket of vector fields on manifolds. -/
/-
**VectorField.mpullback_mlieBracketWithin** 是 Mathlib 中的一个引理，位于命名空间 `VectorField
`。
形式化陈述：mpullback_mlieBracketWithin {f : M -> M'} {V W : Π (x : M'), TangentSpace 
I' x} {x₀ : M} {s : Set M} {t : Set M'} (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MD
iffAt[t] (T% W) (f x₀)) (hu : UniqueMDiff[s]) (hf : CMDiffAt n f x₀) (hx₀ : x₀ i
n s) (hn : minSmoothness 𝕜 2 <= n) (hst : f ⁻¹' t in 𝓝[s] x₀) : mpullback I I' f
 (mlieBracketWithin I' V W t) x₀ = mlieBracketWithin I (mpullback I I' f V) (mpu
llback I I' f W) s x₀
参数：x : M'；hV : MDiffAt[t] (T% V) (f x₀)；hW : MDiffAt[t] (T% W) (f x₀)；hu : Uniqu
eMDiff[s]；hf : CMDiffAt n f x₀；hx₀ : x₀ in s；hn : minSmoothness 𝕜 2 <= n；hst : f
 ⁻¹' t in 𝓝[s] x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsManifoldOfNatWithTopENatOfMinSmoothness_1`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : T
ype u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : 
NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Typ
e u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mfderivWithin_eq_mfderiv`：mfderivWithin_eq_mfderiv (hs : UniqueMDiffAt[s
] x) (h : MDiffAt f x) : mfderiv[s] f x = mfderiv% f x
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_minSmoothness`：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.mpullbackWithin_mlieBracketWithin'`：mpullbackWithin_mlieBrac
ketWithin' {f : M -> M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s u : S
et M} {t : Set M'} (hV : MDiffAt[t] …
· 使用定理 `uniqueMDiffOn_univ`：uniqueMDiffOn_univ : UniqueMDiff[(univ : Set M)]
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Filter.EventuallyEq.mlieBracketWithin_vectorField_of_insert`：∀ {𝕜 : Type
 u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpa
ce H] {E : Type u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The pullback commutes with the Lie bracket of vector fields on manifolds.
-/
lemma mpullback_mlieBracketWithin
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀))
    (hu : UniqueMDiff[s]) (hf : CMDiffAt n f x₀) (hx₀ : x₀ ∈ s)
    (hn : minSmoothness 𝕜 2 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀) :
    mpullback I I' f (mlieBracketWithin I' V W t) x₀ =
      mlieBracketWithin I (mpullback I I' f V) (mpullback I I' f W) s x₀ := by
  have : mpullback I I' f (mlieBracketWithin I' V W t) x₀ =
      mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ := by
    simp only [mpullback, mpullbackWithin]
    congr
    apply (mfderivWithin_eq_mfderiv (hu _ hx₀) _).symm
    exact hf.mdifferentiableAt (two_pos.trans_le (le_minSmoothness.trans hn)).ne'
  rw [this, mpullbackWithin_mlieBracketWithin' hV hW hu uniqueMDiffOn_univ hf.contMDiffWithinAt
    hx₀ hn hst (by simp) (subset_univ _)]
  apply Filter.EventuallyEq.mlieBracketWithin_vectorField_of_insert
  · rw [insert_eq_of_mem hx₀]
    filter_upwards [nhdsWithin_le_nhds ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1
      (hf.of_le (le_minSmoothness.trans hn))), self_mem_nhdsWithin] with y hy h'y
    simp only [mpullback, mpullbackWithin]
    congr
    apply mfderivWithin_eq_mfderiv (hu _ h'y)
    exact hy.mdifferentiableAt two_ne_zero
  · rw [insert_eq_of_mem hx₀]
    filter_upwards [nhdsWithin_le_nhds ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1
      (hf.of_le (le_minSmoothness.trans hn))), self_mem_nhdsWithin] with y hy h'y
    simp only [mpullback, mpullbackWithin]
    congr
    apply mfderivWithin_eq_mfderiv (hu _ h'y)
    exact hy.mdifferentiableAt two_ne_zero
/-
**VectorField.mpullback_mlieBracket** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullback_mlieBracket {f : M -> M'} {V W : Π (x : M'), TangentSpace I' x} 
{x₀ : M} (hV : MDiffAt (T% V) (f x₀)) (hW : MDiffAt (T% W) (f x₀)) (hf : CMDiffA
t n f x₀) (hn : minSmoothness 𝕜 2 <= n) : mpullback I I' f (mlieBracket I' V W) 
x₀ = mlieBracket I (mpullback I I' f V) (mpullback I I' f W) x₀
参数：x : M'；hV : MDiffAt (T% V) (f x₀)；hW : MDiffAt (T% W) (f x₀)；hf : CMDiffAt n 
f x₀；hn : minSmoothness 𝕜 2 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsManifoldOfNatWithTopENatOfMinSmoothness_1`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : T
ype u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : 
NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Typ
e u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `VectorField.mpullback_mlieBracketWithin`：mpullback_mlieBracketWithin {f 
: M -> M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M
'} (hV : MDiffAt[t] (T% V) (f…
· 使用定理 `uniqueMDiffOn_univ`：uniqueMDiffOn_univ : UniqueMDiff[(univ : Set M)]
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
-/
lemma mpullback_mlieBracket
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M}
    (hV : MDiffAt (T% V) (f x₀)) (hW : MDiffAt (T% W) (f x₀))
    (hf : CMDiffAt n f x₀) (hn : minSmoothness 𝕜 2 ≤ n) :
    mpullback I I' f (mlieBracket I' V W) x₀ =
      mlieBracket I (mpullback I I' f V) (mpullback I I' f W) x₀ := by
  simp only [← mlieBracketWithin_univ, ← mdifferentiableWithinAt_univ] at hV hW ⊢
  exact mpullback_mlieBracketWithin hV hW uniqueMDiffOn_univ hf (mem_univ _) hn (by simp)

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
/-
**VectorField._root_.ContMDiffWithinAt.mlieBracketWithin_vectorField** 是 Mathlib
 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`
.
-/
protected lemma _root_.ContMDiffWithinAt.mlieBracketWithin_vectorField
    [IsManifold I (n + 1) M] {m : ℕ∞ω}
    {U V : Π (x : M), TangentSpace I x} {s : Set M} {x : M}
    (hU : CMDiffAt[s] n (T% U) x) (hV : CMDiffAt[s] n (T% V) x)
    (hs : UniqueMDiff[s]) (hx : x ∈ s) (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    CMDiffAt[s] m (T% (mlieBracketWithin I U V s)) x := by
  /- The statement is not obvious, since at different points the Lie bracket is defined using
  different charts. However, since we know that the Lie bracket is invariant under diffeos, we can
  use a single chart to prove the statement. Let `U'` and `V'` denote the pullbacks of `U` and `V`
  in the chart around `x`. Then the Lie bracket there is smooth (as it coincides with the vector
  space Lie bracket, given by an explicit formula). Pulling back this Lie bracket in `M` gives
  locally a smooth function, which coincides with the initial Lie bracket by invariance
  under diffeos. -/
  have min2 : minSmoothness 𝕜 2 ≤ n + 1 := by
    grw [← hmn, ← minSmoothness_add, add_assoc]
    exact minSmoothness_monotone le_add_self
  apply contMDiffWithinAt_iff_le_ne_infty.2 (fun m' hm' h'm' ↦ ?_)
  have hn : 1 ≤ m' + 1 := le_add_self
  have hm'n : m' + 1 ≤ n := by grw [hm', ← hmn, ← le_minSmoothness]
  have pre_mem : (extChartAt I x) ⁻¹' ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)
      ∈ 𝓝[s] x := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := I) x)] with y hy h'y
    exact ⟨(extChartAt I x).map_source h'y,
      by simpa only [mem_preimage, (extChartAt I x).left_inv h'y] using hy⟩
  let U' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm U (range I)
  let V' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)
  have A : ContDiffWithinAt 𝕜 m' (lieBracketWithin 𝕜 U' V'
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) :=
    ContDiffWithinAt.lieBracketWithin_vectorField
      (contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.1
        (contMDiffWithinAt_mpullbackWithin_extChartAt_symm hU hs hx le_rfl))
      (contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.1
        (contMDiffWithinAt_mpullbackWithin_extChartAt_symm hV hs hx le_rfl))
      (hs.uniqueDiffOn_target_inter x) hm'n (by simp [hx])
  have B : CMDiffAt[((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)] m'
      (T% (mlieBracketWithin 𝓘(𝕜, E) U' V' ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)))
      (extChartAt I x x) := by
    rw [← mlieBracketWithin_eq_lieBracketWithin] at A
    exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.2 A
  have C : CMDiffAt[s] m' (T% ((mpullback I 𝓘(𝕜, E) (extChartAt I x)
      ((mlieBracketWithin 𝓘(𝕜, E) U' V'
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)))))) x :=
    ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin_of_eq B (n := m' + 1)
      contMDiffAt_extChartAt
      (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)) le_rfl pre_mem rfl
  apply C.congr_of_eventuallyEq_of_mem _ hx
  filter_upwards [eventually_eventually_nhdsWithin.2 pre_mem,
    eventually_eventually_nhdsWithin.2 (eventuallyEq_mpullback_mpullbackWithin_extChartAt U),
    eventually_eventually_nhdsWithin.2 (eventuallyEq_mpullback_mpullbackWithin_extChartAt V),
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm (hU.of_le hm'n) hs hx
      (by gcongr) (by simp [h'm']),
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm (hV.of_le hm'n) hs hx
      (by gcongr) (by simp [h'm']),
    nhdsWithin_le_nhds (chart_source_mem_nhds H x), self_mem_nhdsWithin]
    with y hy hyU hyV h'yU h'yV hy_chart hys
  simp only [Bundle.TotalSpace.mk_inj]
  rw [mpullback_mlieBracketWithin (h'yU.mdifferentiableWithinAt <| by positivity)
    (h'yV.mdifferentiableWithinAt <| by positivity) hs (contMDiffAt_extChartAt' hy_chart)
    hys min2 hy]
  exact Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem hyU hyV hys

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
/-
**VectorField._root_.ContMDiffAt.mlieBracket_vectorField** 是 Mathlib 中的一个引理，位于命名
空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`
.
-/
lemma _root_.ContMDiffAt.mlieBracket_vectorField {m n : ℕ∞}
    [IsManifold I (n + 1) M] {U V : Π (x : M), TangentSpace I x} {x : M}
    (hU : CMDiffAt n (T% U) x) (hV : CMDiffAt n (T% V) x)
    (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    CMDiffAt m (T% (mlieBracket I U V)) x := by
  simp only [← contMDiffWithinAt_univ, ← mlieBracketWithin_univ] at hU hV ⊢
  exact hU.mlieBracketWithin_vectorField hV uniqueMDiffOn_univ (mem_univ _) hmn

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
/-
**VectorField._root_.ContMDiffOn.mlieBracketWithin_vectorField** 是 Mathlib 中的一个引
理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`
.
-/
lemma _root_.ContMDiffOn.mlieBracketWithin_vectorField {m n : ℕ∞}
    [IsManifold I (n + 1) M] {U V : Π (x : M), TangentSpace I x}
    (hU : CMDiff[s] n (T% U)) (hV : CMDiff[s] n (T% V))
    (hs : UniqueMDiff[s]) (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    CMDiff[s] m (T% (mlieBracketWithin I U V s)) :=
  fun x hx ↦ (hU x hx).mlieBracketWithin_vectorField (hV x hx) hs hx hmn

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
/-
**VectorField._root_.ContDiff.mlieBracket_vectorField** 是 Mathlib 中的一个引理，位于命名空间 
`VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`
.
-/
lemma _root_.ContDiff.mlieBracket_vectorField {m n : ℕ∞}
    [IsManifold I (n + 1) M] {U V : Π (x : M), TangentSpace I x}
    (hU : CMDiff n (T% U)) (hV : CMDiff n (T% V)) (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    CMDiff m (T% (mlieBracket I U V)) := by
  simp only [← contMDiffOn_univ] at hU hV ⊢
  exact hU.mlieBracketWithin_vectorField hV uniqueMDiffOn_univ hmn

end Invariance

section Leibniz

variable [IsManifold I (minSmoothness 𝕜 3) M] [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in
/-- The Lie bracket of vector fields in manifolds satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]` (also called Jacobi identity). -/
/-
**VectorField.leibniz_identity_mlieBracketWithin_apply** 是 Mathlib 中的一个定理，位于命名空间
 `VectorField`。
形式化陈述：leibniz_identity_mlieBracketWithin_apply {U V W : Π (x : M), TangentSpace 
I x} {s : Set M} {x : M} (hs : UniqueMDiff[s]) (h's : x in closure (interior s))
 (hx : x in s) (hU : CMDiffAt[s] (minSmoothness 𝕜 2) (T% U) x) (hV : CMDiffAt[s]
 (minSmoothness 𝕜 2) (T% V) x) (hW : CMDiffAt[s] (minSmoothness 𝕜 2) (T% W) x) :
 mlieBracketWithin I U (mlieBracketWithin I V W s) s x = mlieBracketWithin I (ml
ieBracketWithin I U V s) W s x + mlieBracketWithin I V (mlieBracketWithin I U W 
s) s x
参数：x : M；hs : UniqueMDiff[s]；h's : x in closure (interior s)；hx : x in s；hU : CM
DiffAt[s] (minSmoothness 𝕜 2) (T% U) x；hV : CMDiffAt[s] (minSmoothness 𝕜 2) (T% 
V) x；hW : CMDiffAt[s] (minSmoothness 𝕜 2) (T% W) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsManifoldOfNatWithTopENatOfMinSmoothness_1`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : T
ype u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : 
NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Typ
e u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type 
u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContMDiffAdd.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
· 使用引理 `VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm`：contMDiff
WithinAt_mpullbackWithin_extChartAt_symm {V : Π (x : M), TangentSpace I x} (hV :
 CMDiffAt[s] m (T% V) x) (hs : UniqueMDiff[s]) (hx …
· 使用引理 `VectorField.eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm
`：eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm {V : Π (x : M), T
angentSpace I x} (hV : CMDiffAt[s] m (T% V) x) (hs : UniqueMDi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `VectorField.eventuallyEq_mpullback_mpullbackWithin_extChartAt`：eventuall
yEq_mpullback_mpullbackWithin_extChartAt (V : Π (x : M), TangentSpace I x) : V =
ᶠ[𝓝[s] x] mpullback I 𝓘(𝕜, E) (extChartAt I x) (mpu…
· 使用定理 `Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem`：∀ {𝕜 : Type
 u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpa
ce H] {E : Type u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `Filter.EventuallyEq.mlieBracketWithin_vectorField`：∀ {𝕜 : Type u_1} [ins
t : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E :
 Type u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `chart_source_mem_nhds`：chart_source_mem_nhds (x : M) : (chartAt H x).sou
rce in 𝓝 x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
The Lie bracket of vector fields in manifolds satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]` (also called Jacobi identity).
-/
theorem leibniz_identity_mlieBracketWithin_apply
    {U V W : Π (x : M), TangentSpace I x} {s : Set M} {x : M}
    (hs : UniqueMDiff[s]) (h's : x ∈ closure (interior s)) (hx : x ∈ s)
    (hU : CMDiffAt[s] (minSmoothness 𝕜 2) (T% U) x)
    (hV : CMDiffAt[s] (minSmoothness 𝕜 2) (T% V) x)
    (hW : CMDiffAt[s] (minSmoothness 𝕜 2) (T% W) x) :
    mlieBracketWithin I U (mlieBracketWithin I V W s) s x =
      mlieBracketWithin I (mlieBracketWithin I U V s) W s x
      + mlieBracketWithin I V (mlieBracketWithin I U W s) s x := by
  have A : minSmoothness 𝕜 2 + 1 ≤ minSmoothness 𝕜 3 := by
    simp only [← minSmoothness_add]
    exact le_rfl
  have s_inter_mem : s ∩ (extChartAt I x).source ∈ 𝓝[s] x :=
    inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (extChartAt_source_mem_nhds x))
  have pre_mem : (extChartAt I x) ⁻¹' ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)
      ∈ 𝓝[s] x := by
    filter_upwards [s_inter_mem] with y hy
    exact ⟨(extChartAt I x).map_source hy.2,
      by simpa only [mem_preimage, (extChartAt I x).left_inv hy.2] using hy.1⟩
  -- write everything as pullbacks of vector fields in `E` (denoted with primes), for which
  -- the identity can be checked via direct calculation.
  let U' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm U (range I)
  let V' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)
  let W' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (range I)
  -- register basic facts on the pullbacks in the vector space
  have J0U : CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s] (minSmoothness 𝕜 2)
      (T% U') (extChartAt I x x) :=
    contMDiffWithinAt_mpullbackWithin_extChartAt_symm hU hs hx A
  have J0V : CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s] (minSmoothness 𝕜 2)
      (T% V') (extChartAt I x x) :=
    contMDiffWithinAt_mpullbackWithin_extChartAt_symm hV hs hx A
  have J0W : CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s] (minSmoothness 𝕜 2)
      (T% W') (extChartAt I x x) :=
    contMDiffWithinAt_mpullbackWithin_extChartAt_symm hW hs hx A
  have J1U : ∀ᶠ y in 𝓝[s] x, CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s]
      (minSmoothness 𝕜 2) (T% U') (extChartAt I x y) :=
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm hU hs hx A (by simp)
  have J1V : ∀ᶠ y in 𝓝[s] x, CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s]
      (minSmoothness 𝕜 2) (T% V') (extChartAt I x y) :=
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm hV hs hx A (by simp)
  have J1W : ∀ᶠ y in 𝓝[s] x, CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s]
      (minSmoothness 𝕜 2) (T% W') (extChartAt I x y) :=
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm hW hs hx A (by simp)
  have JU : U =ᶠ[𝓝[s] x] mpullback I 𝓘(𝕜, E) (extChartAt I x) U' :=
    eventuallyEq_mpullback_mpullbackWithin_extChartAt U
  have JV : V =ᶠ[𝓝[s] x] mpullback I 𝓘(𝕜, E) (extChartAt I x) V' :=
    eventuallyEq_mpullback_mpullbackWithin_extChartAt V
  have JW : W =ᶠ[𝓝[s] x] mpullback I 𝓘(𝕜, E) (extChartAt I x) W' :=
    eventuallyEq_mpullback_mpullbackWithin_extChartAt W
  rw [JU.mlieBracketWithin_vectorField_eq_of_mem (JV.mlieBracketWithin_vectorField JW) hx,
    (JU.mlieBracketWithin_vectorField JV).mlieBracketWithin_vectorField_eq_of_mem JW hx,
    JV.mlieBracketWithin_vectorField_eq_of_mem (JU.mlieBracketWithin_vectorField JW) hx]
  /- Rewrite the first term as a pullback-/
  have : ∀ᶠ y in 𝓝[s] x, mlieBracketWithin I
        (mpullback I 𝓘(𝕜, E) (extChartAt I x) V') (mpullback I 𝓘(𝕜, E) (extChartAt I x) W') s y
      = mpullback I 𝓘(𝕜, E) (extChartAt I x) (mlieBracketWithin 𝓘(𝕜, E) V' W'
        ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)) y := by
    filter_upwards [eventually_eventually_nhdsWithin.2 pre_mem, J1V, J1W,
      nhdsWithin_le_nhds (chart_source_mem_nhds H x), self_mem_nhdsWithin] with y hy hyV hyW h'y ys
    symm
    exact mpullback_mlieBracketWithin (n := minSmoothness 𝕜 2)
      (hyV.mdifferentiableWithinAt (two_pos.trans_le le_minSmoothness).ne')
      (hyW.mdifferentiableWithinAt (two_pos.trans_le le_minSmoothness).ne') hs
      (contMDiffAt_extChartAt' h'y) ys le_rfl hy
  rw [Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem EventuallyEq.rfl this hx,
    ← mpullback_mlieBracketWithin (J0U.mdifferentiableWithinAt
      (two_pos.trans_le le_minSmoothness).ne') _ hs contMDiffAt_extChartAt hx le_rfl pre_mem]; swap
  · apply ContMDiffWithinAt.mdifferentiableWithinAt _ one_ne_zero
    apply J0V.mlieBracketWithin_vectorField J0W (m := 1)
    · exact hs.uniqueMDiffOn_target_inter x
    · exact ⟨mem_extChartAt_target x, by simp [hx]⟩
    · exact le_rfl
  /- Rewrite the second term as a pullback-/
  have : ∀ᶠ y in 𝓝[s] x, mlieBracketWithin I
        (mpullback I 𝓘(𝕜, E) (extChartAt I x) U') (mpullback I 𝓘(𝕜, E) (extChartAt I x) V') s y
      = mpullback I 𝓘(𝕜, E) (extChartAt I x) (mlieBracketWithin 𝓘(𝕜, E) U' V'
        ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)) y := by
    filter_upwards [eventually_eventually_nhdsWithin.2 pre_mem, J1U, J1V,
      nhdsWithin_le_nhds (chart_source_mem_nhds H x), self_mem_nhdsWithin] with y hy hyU hyV h'y ys
    symm
    exact mpullback_mlieBracketWithin (n := minSmoothness 𝕜 2)
      (hyU.mdifferentiableWithinAt (two_pos.trans_le le_minSmoothness).ne')
      (hyV.mdifferentiableWithinAt (two_pos.trans_le le_minSmoothness).ne') hs
      (contMDiffAt_extChartAt' h'y) ys le_rfl hy
  rw [Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem this EventuallyEq.rfl hx,
    ← mpullback_mlieBracketWithin _ (J0W.mdifferentiableWithinAt
      (two_pos.trans_le le_minSmoothness).ne') hs contMDiffAt_extChartAt hx le_rfl pre_mem]; swap
  · apply ContMDiffWithinAt.mdifferentiableWithinAt _ one_ne_zero
    apply J0U.mlieBracketWithin_vectorField J0V (m := 1)
    · exact hs.uniqueMDiffOn_target_inter x
    · exact ⟨mem_extChartAt_target x, by simp [hx]⟩
    · exact le_rfl
  /- Rewrite the third term as a pullback-/
  have : ∀ᶠ y in 𝓝[s] x, mlieBracketWithin I
        (mpullback I 𝓘(𝕜, E) (extChartAt I x) U') (mpullback I 𝓘(𝕜, E) (extChartAt I x) W') s y
      = mpullback I 𝓘(𝕜, E) (extChartAt I x) (mlieBracketWithin 𝓘(𝕜, E) U' W'
        ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)) y := by
    filter_upwards [eventually_eventually_nhdsWithin.2 pre_mem, J1U, J1W,
      nhdsWithin_le_nhds (chart_source_mem_nhds H x), self_mem_nhdsWithin] with y hy hyU hyW h'y ys
    symm
    exact mpullback_mlieBracketWithin (n := minSmoothness 𝕜 2)
      (hyU.mdifferentiableWithinAt (two_pos.trans_le le_minSmoothness).ne')
      (hyW.mdifferentiableWithinAt (two_pos.trans_le le_minSmoothness).ne') hs
      (contMDiffAt_extChartAt' h'y) ys le_rfl hy
  rw [Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem EventuallyEq.rfl this hx,
    ← mpullback_mlieBracketWithin (J0V.mdifferentiableWithinAt
      (two_pos.trans_le le_minSmoothness).ne') _ hs contMDiffAt_extChartAt hx le_rfl pre_mem]; swap
  · apply ContMDiffWithinAt.mdifferentiableWithinAt _ one_ne_zero
    apply J0U.mlieBracketWithin_vectorField J0W (m := 1)
    · exact hs.uniqueMDiffOn_target_inter x
    · exact ⟨mem_extChartAt_target x, by simp [hx]⟩
    · exact le_rfl
  /- Now that everything is in pullback form, use the leibniz identity in the vector space -/
  rw [← mpullback_add_apply, mpullback_apply, mpullback_apply]
  congr 1
  simp_rw [mlieBracketWithin_eq_lieBracketWithin]
  apply leibniz_identity_lieBracketWithin (E := E) le_rfl
  · exact hs.uniqueDiffOn_target_inter x
  · rw [inter_comm]
    exact extChartAt_mem_closure_interior h's (mem_extChartAt_source x)
  · exact ⟨mem_extChartAt_target x, by simp [hx]⟩
  · exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp J0U
  · exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp J0V
  · exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp J0W

/-- The Lie bracket of vector fields in manifolds satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]` (also called Jacobi identity). -/
/-
**VectorField.leibniz_identity_mlieBracket_apply** 是 Mathlib 中的一个引理，位于命名空间 `Vect
orField`。
形式化陈述：leibniz_identity_mlieBracket_apply {U V W : Π (x : M), TangentSpace I x} {
x : M} (hU : CMDiffAt (minSmoothness 𝕜 2) (T% U) x) (hV : CMDiffAt (minSmoothnes
s 𝕜 2) (T% V) x) (hW : CMDiffAt (minSmoothness 𝕜 2) (T% W) x) : mlieBracket I U 
(mlieBracket I V W) x = mlieBracket I (mlieBracket I U V) W x + mlieBracket I V 
(mlieBracket I U W) x
参数：x : M；hU : CMDiffAt (minSmoothness 𝕜 2) (T% U) x；hV : CMDiffAt (minSmoothness
 𝕜 2) (T% V) x；hW : CMDiffAt (minSmoothness 𝕜 2) (T% W) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsManifoldOfNatWithTopENatOfMinSmoothness_1`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : T
ype u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : 
NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Typ
e u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type 
u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `VectorField.leibniz_identity_mlieBracketWithin_apply`：leibniz_identity_m
lieBracketWithin_apply {U V W : Π (x : M), TangentSpace I x} {s : Set M} {x : M}
 (hs : UniqueMDiff[s]) (h's : x in closure…
· 使用定理 `uniqueMDiffOn_univ`：uniqueMDiffOn_univ : UniqueMDiff[(univ : Set M)]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The Lie bracket of vector fields in manifolds satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]` (also called Jacobi identity).
-/
lemma leibniz_identity_mlieBracket_apply
    {U V W : Π (x : M), TangentSpace I x} {x : M}
    (hU : CMDiffAt (minSmoothness 𝕜 2) (T% U) x)
    (hV : CMDiffAt (minSmoothness 𝕜 2) (T% V) x)
    (hW : CMDiffAt (minSmoothness 𝕜 2) (T% W) x) :
    mlieBracket I U (mlieBracket I V W) x =
      mlieBracket I (mlieBracket I U V) W x + mlieBracket I V (mlieBracket I U W) x := by
  simp only [← mlieBracketWithin_univ, ← contMDiffWithinAt_univ] at hU hV hW ⊢
  exact leibniz_identity_mlieBracketWithin_apply uniqueMDiffOn_univ (by simp) (mem_univ _) hU hV hW

/-- The Lie bracket of vector fields in manifolds satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]` (also called Jacobi identity). -/
/-
**VectorField.leibniz_identity_mlieBracket** 是 Mathlib 中的一个引理，位于命名空间 `VectorFiel
d`。
形式化陈述：leibniz_identity_mlieBracket {U V W : Π (x : M), TangentSpace I x} (hU : C
MDiff (minSmoothness 𝕜 2) (T% U)) (hV : CMDiff (minSmoothness 𝕜 2) (T% V)) (hW :
 CMDiff (minSmoothness 𝕜 2) (T% W)) : mlieBracket I U (mlieBracket I V W) = mlie
Bracket I (mlieBracket I U V) W + mlieBracket I V (mlieBracket I U W)
参数：x : M；hU : CMDiff (minSmoothness 𝕜 2) (T% U)；hV : CMDiff (minSmoothness 𝕜 2) 
(T% V)；hW : CMDiff (minSmoothness 𝕜 2) (T% W)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsManifoldOfNatWithTopENatOfMinSmoothness_1`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : T
ype u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : 
NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Typ
e u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type 
u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `VectorField.leibniz_identity_mlieBracket_apply`：leibniz_identity_mlieBra
cket_apply {U V W : Π (x : M), TangentSpace I x} {x : M} (hU : CMDiffAt (minSmoo
thness 𝕜 2) (T% U) x) (hV : CMDiffAt…

--- 原说明 ---
The Lie bracket of vector fields in manifolds satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]` (also called Jacobi identity).
-/
lemma leibniz_identity_mlieBracket
    {U V W : Π (x : M), TangentSpace I x}
    (hU : CMDiff (minSmoothness 𝕜 2) (T% U))
    (hV : CMDiff (minSmoothness 𝕜 2) (T% V))
    (hW : CMDiff (minSmoothness 𝕜 2) (T% W)) :
    mlieBracket I U (mlieBracket I V W) =
      mlieBracket I (mlieBracket I U V) W + mlieBracket I V (mlieBracket I U W) := by
  ext x
  exact leibniz_identity_mlieBracket_apply (hU x) (hV x) (hW x)

end Leibniz

end LieBracket

end VectorField

