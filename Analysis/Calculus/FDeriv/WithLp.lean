/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Derivatives on `WithLp`
-/

public section

open ContinuousLinearMap PiLp WithLp

section PiLp

variable {𝕜 ι : Type*} {E : ι → Type*} {H : Type*}
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup H] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] [NormedSpace 𝕜 H] [Finite ι] (p) [Fact (1 ≤ p)]
  {f : H → PiLp p E} {f' : H →L[𝕜] PiLp p E} {t : Set H} {y : H}

/-
**differentiableWithinAt_piLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_piLp : DifferentiableWithinAt 𝕜 f t y ↔ forall i, D
ifferentiableWithinAt 𝕜 (fun x => f x i) t y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.comp_differentiableWithinAt_iff`：comp_differentiab
leWithinAt_iff {f : G -> E} {s : Set G} {x : G} : DifferentiableWithinAt 𝕜 (iso 
∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableWithinAt_pi`：differentiableWithinAt_pi : DifferentiableWit
hinAt 𝕜 Φ s x ↔ forall i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem differentiableWithinAt_piLp :
    DifferentiableWithinAt 𝕜 f t y ↔ ∀ i, DifferentiableWithinAt 𝕜 (fun x => f x i) t y := by
  have := Fintype.ofFinite ι
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_differentiableWithinAt_iff,
    differentiableWithinAt_pi]
  rfl
/-
**differentiableAt_piLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_piLp : DifferentiableAt 𝕜 f y ↔ forall i, DifferentiableA
t 𝕜 (fun x => f x i) y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.comp_differentiableAt_iff`：comp_differentiableAt_i
ff {f : G -> E} {x : G} : DifferentiableAt 𝕜 (iso ∘ f) x ↔ DifferentiableAt 𝕜 f 
x
· 使用定理 `differentiableAt_pi`：differentiableAt_pi : DifferentiableAt 𝕜 Φ x ↔ fora
ll i, DifferentiableAt 𝕜 (fun x => Φ x i) x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem differentiableAt_piLp :
    DifferentiableAt 𝕜 f y ↔ ∀ i, DifferentiableAt 𝕜 (fun x => f x i) y := by
  have := Fintype.ofFinite ι
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_differentiableAt_iff, differentiableAt_pi]
  rfl
/-
**differentiableOn_piLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_piLp : DifferentiableOn 𝕜 f t ↔ forall i, DifferentiableO
n 𝕜 (fun x => f x i) t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.comp_differentiableOn_iff`：comp_differentiableOn_i
ff {f : G -> E} {s : Set G} : DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 
𝕜 f s
· 使用定理 `differentiableOn_pi`：differentiableOn_pi : DifferentiableOn 𝕜 Φ s ↔ fora
ll i, DifferentiableOn 𝕜 (fun x => Φ x i) s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem differentiableOn_piLp :
    DifferentiableOn 𝕜 f t ↔ ∀ i, DifferentiableOn 𝕜 (fun x => f x i) t := by
  have := Fintype.ofFinite ι
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_differentiableOn_iff, differentiableOn_pi]
  rfl
/-
**differentiable_piLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_piLp : Differentiable 𝕜 f ↔ forall i, Differentiable 𝕜 fun 
x => f x i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.comp_differentiable_iff`：comp_differentiable_iff {
f : G -> E} : Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f
· 使用定理 `differentiable_pi`：differentiable_pi : Differentiable 𝕜 Φ ↔ forall i, Di
fferentiable 𝕜 fun x => Φ x i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem differentiable_piLp : Differentiable 𝕜 f ↔ ∀ i, Differentiable 𝕜 fun x => f x i := by
  have := Fintype.ofFinite ι
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_differentiable_iff, differentiable_pi]
  rfl
/-
**hasStrictFDerivAt_piLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_piLp : HasStrictFDerivAt f f' y ↔ forall i, HasStrictFDe
rivAt (fun x => f x i) (PiLp.proj _ _ i ∘L f') y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.comp_hasStrictFDerivAt_iff`：comp_hasStrictFDerivAt
_iff {f : G -> E} {x : G} {f' : G ->L[𝕜] E} : HasStrictFDerivAt (iso ∘ f) ((iso 
: E ->L[𝕜] F).comp f') x ↔ HasStrictFD…
· 使用定理 `hasStrictFDerivAt_pi'`：hasStrictFDerivAt_pi' : HasStrictFDerivAt Φ Φ' x 
↔ forall i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasStrictFDerivAt_piLp :
    HasStrictFDerivAt f f' y ↔
      ∀ i, HasStrictFDerivAt (fun x => f x i) (PiLp.proj _ _ i ∘L f') y := by
  have := Fintype.ofFinite ι
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_hasStrictFDerivAt_iff, hasStrictFDerivAt_pi']
  rfl
/-
**hasFDerivWithinAt_piLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_piLp : HasFDerivWithinAt f f' t y ↔ forall i, HasFDerivW
ithinAt (fun x => f x i) (PiLp.proj _ _ i ∘L f') t y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.comp_hasFDerivWithinAt_iff`：comp_hasFDerivWithinAt
_iff {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜] E} : HasFDerivWithinAt (iso
 ∘ f) ((iso : E ->L[𝕜] F).comp f') s x…
· 使用定理 `hasFDerivWithinAt_pi'`：hasFDerivWithinAt_pi' : HasFDerivWithinAt Φ Φ' s 
x ↔ forall i, HasFDerivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasFDerivWithinAt_piLp :
    HasFDerivWithinAt f f' t y ↔
      ∀ i, HasFDerivWithinAt (fun x => f x i) (PiLp.proj _ _ i ∘L f') t y := by
  have := Fintype.ofFinite ι
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_hasFDerivWithinAt_iff, hasFDerivWithinAt_pi']
  rfl

namespace PiLp

/-
**PiLp.hasStrictFDerivAt_ofLp** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：hasStrictFDerivAt_ofLp (f : PiLp p E) : HasStrictFDerivAt ofLp (continuous
LinearEquiv p 𝕜 _).toContinuousLinearMap f
参数：f : PiLp p E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.of_isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Typ…
· 使用定理 `Asymptotics.IsLittleO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ :
 α → E}, f₁ =o[l] g → …
· 使用定理 `Asymptotics.isLittleO_zero`：isLittleO_zero : (fun _x => (0 : E')) =o[l] 
g'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem hasStrictFDerivAt_ofLp (f : PiLp p E) :
    HasStrictFDerivAt ofLp (continuousLinearEquiv p 𝕜 _).toContinuousLinearMap f :=
  have := Fintype.ofFinite ι
  .of_isLittleO <| (Asymptotics.isLittleO_zero _ _).congr_left fun _ => (sub_self _).symm
/-
**PiLp.hasStrictFDerivAt_toLp** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：hasStrictFDerivAt_toLp (f : forall i, E i) : HasStrictFDerivAt (toLp p) (c
ontinuousLinearEquiv p 𝕜 _).symm.toContinuousLinearMap f
参数：f : forall i, E i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.of_isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Typ…
· 使用定理 `Asymptotics.IsLittleO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ :
 α → E}, f₁ =o[l] g → …
· 使用定理 `Asymptotics.isLittleO_zero`：isLittleO_zero : (fun _x => (0 : E')) =o[l] 
g'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem hasStrictFDerivAt_toLp (f : ∀ i, E i) :
    HasStrictFDerivAt (toLp p) (continuousLinearEquiv p 𝕜 _).symm.toContinuousLinearMap f :=
  have := Fintype.ofFinite ι
  .of_isLittleO <| (Asymptotics.isLittleO_zero _ _).congr_left fun _ => (sub_self _).symm

nonrec theorem hasStrictFDerivAt_apply (f : PiLp p E) (i : ι) :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun f : PiLp p E => f i) (proj p E i) f :=
  have := Fintype.ofFinite ι
  (hasStrictFDerivAt_apply i f).comp f (hasStrictFDerivAt_ofLp (𝕜 := 𝕜) p f)
/-
**PiLp.hasFDerivAt_ofLp** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：hasFDerivAt_ofLp (f : PiLp p E) : HasFDerivAt ofLp (continuousLinearEquiv 
p 𝕜 _).toContinuousLinearMap f
参数：f : PiLp p E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `PiLp.hasStrictFDerivAt_ofLp`：hasStrictFDerivAt_ofLp (f : PiLp p E) : Has
StrictFDerivAt ofLp (continuousLinearEquiv p 𝕜 _).toContinuousLinearMap f
-/
theorem hasFDerivAt_ofLp (f : PiLp p E) :
    HasFDerivAt ofLp (continuousLinearEquiv p 𝕜 _).toContinuousLinearMap f :=
  have := Fintype.ofFinite ι
  (hasStrictFDerivAt_ofLp p f).hasFDerivAt
/-
**PiLp.hasFDerivAt_toLp** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：hasFDerivAt_toLp (f : forall i, E i) : HasFDerivAt (toLp p) (continuousLin
earEquiv p 𝕜 _).symm.toContinuousLinearMap f
参数：f : forall i, E i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `PiLp.hasStrictFDerivAt_toLp`：hasStrictFDerivAt_toLp (f : forall i, E i) 
: HasStrictFDerivAt (toLp p) (continuousLinearEquiv p 𝕜 _).symm.toContinuousLine
arMap f
-/
theorem hasFDerivAt_toLp (f : ∀ i, E i) :
    HasFDerivAt (toLp p) (continuousLinearEquiv p 𝕜 _).symm.toContinuousLinearMap f :=
  have := Fintype.ofFinite ι
  (hasStrictFDerivAt_toLp p f).hasFDerivAt

nonrec theorem hasFDerivAt_apply (f : PiLp p E) (i : ι) :
    HasFDerivAt (𝕜 := 𝕜) (fun f : PiLp p E => f i) (proj p E i) f :=
  have := Fintype.ofFinite ι
  (hasStrictFDerivAt_apply p f i).hasFDerivAt

end PiLp

end PiLp

