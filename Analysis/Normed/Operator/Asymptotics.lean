/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Asymptotics.Defs
/-!
# Asymptotic statements about the operator norm

This file contains lemmas about how operator norm on continuous linear maps interacts with `IsBigO`.

-/

public section

open Asymptotics


variable {𝕜 𝕜₂ 𝕜₃ E F G : Type*}
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃}

namespace ContinuousLinearMap

variable [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) (l : Filter E)

/-
**ContinuousLinearMap.isBigOWith_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：isBigOWith_id : IsBigOWith ‖f‖ l f fun x => x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigOWith_of_le'`：isBigOWith_of_le' (hfg : forall x, ‖f x‖ 
<= c * ‖g x‖) : IsBigOWith c l f g
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem isBigOWith_id : IsBigOWith ‖f‖ l f fun x => x :=
  isBigOWith_of_le' _ f.le_opNorm
/-
**ContinuousLinearMap.isBigO_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：isBigO_id : f =O[l] fun x => x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `ContinuousLinearMap.isBigOWith_id`：isBigOWith_id : IsBigOWith ‖f‖ l f fu
n x => x
-/
theorem isBigO_id : f =O[l] fun x => x :=
  (f.isBigOWith_id l).isBigO
/-
**ContinuousLinearMap.isBigOWith_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：isBigOWith_comp [RingHomIsometric σ₂₃] {α : Type*} (g : F ->SL[σ₂₃] G) (f 
: α -> F) (l : Filter α) : IsBigOWith ‖g‖ l (fun x' => g (f x')) f
参数：g : F ->SL[σ₂₃] G；f : α -> F；l : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E 
: Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E}
   {g : α → F} {l : Filte…
· 使用定理 `ContinuousLinearMap.isBigOWith_id`：isBigOWith_id : IsBigOWith ‖f‖ l f fu
n x => x
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem isBigOWith_comp [RingHomIsometric σ₂₃] {α : Type*} (g : F →SL[σ₂₃] G) (f : α → F)
    (l : Filter α) : IsBigOWith ‖g‖ l (fun x' => g (f x')) f :=
  (g.isBigOWith_id ⊤).comp_tendsto le_top
/-
**ContinuousLinearMap.isBigO_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：isBigO_comp [RingHomIsometric σ₂₃] {α : Type*} (g : F ->SL[σ₂₃] G) (f : α 
-> F) (l : Filter α) : (fun x' => g (f x')) =O[l] f
参数：g : F ->SL[σ₂₃] G；f : α -> F；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `ContinuousLinearMap.isBigOWith_comp`：isBigOWith_comp [RingHomIsometric σ
₂₃] {α : Type*} (g : F ->SL[σ₂₃] G) (f : α -> F) (l : Filter α) : IsBigOWith ‖g‖
 l (fun x' => g (f x')) f
-/
theorem isBigO_comp [RingHomIsometric σ₂₃] {α : Type*} (g : F →SL[σ₂₃] G) (f : α → F)
    (l : Filter α) : (fun x' => g (f x')) =O[l] f :=
  (g.isBigOWith_comp f l).isBigO
/-
**ContinuousLinearMap.isBigOWith_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：isBigOWith_sub (x : E) : IsBigOWith ‖f‖ l (fun x' => f (x' - x)) fun x' =>
 x' - x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isBigOWith_comp`：isBigOWith_comp [RingHomIsometric σ
₂₃] {α : Type*} (g : F ->SL[σ₂₃] G) (f : α -> F) (l : Filter α) : IsBigOWith ‖g‖
 l (fun x' => g (f x')) f
-/
theorem isBigOWith_sub (x : E) :
    IsBigOWith ‖f‖ l (fun x' => f (x' - x)) fun x' => x' - x :=
  f.isBigOWith_comp _ l
/-
**ContinuousLinearMap.isBigO_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：isBigO_sub (x : E) : (fun x' => f (x' - x)) =O[l] fun x' => x' - x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isBigO_comp`：isBigO_comp [RingHomIsometric σ₂₃] {α :
 Type*} (g : F ->SL[σ₂₃] G) (f : α -> F) (l : Filter α) : (fun x' => g (f x')) =
O[l] f
-/
theorem isBigO_sub (x : E) :
    (fun x' => f (x' - x)) =O[l] fun x' => x' - x :=
  f.isBigO_comp _ l

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (e : E ≃SL[σ₁₂] F)

section

variable [RingHomIsometric σ₁₂]

/-
**ContinuousLinearEquiv.isBigO_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearE
quiv`。
形式化陈述：isBigO_comp {α : Type*} (f : α -> E) (l : Filter α) : (fun x' => e (f x'))
 =O[l] f
参数：f : α -> E；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isBigO_comp`：isBigO_comp [RingHomIsometric σ₂₃] {α :
 Type*} (g : F ->SL[σ₂₃] G) (f : α -> F) (l : Filter α) : (fun x' => g (f x')) =
O[l] f
-/
theorem isBigO_comp {α : Type*} (f : α → E) (l : Filter α) : (fun x' => e (f x')) =O[l] f :=
  (e : E →SL[σ₁₂] F).isBigO_comp f l
/-
**ContinuousLinearEquiv.isBigO_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：isBigO_sub (l : Filter E) (x : E) : (fun x' => e (x' - x)) =O[l] fun x' =>
 x' - x
参数：l : Filter E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isBigO_sub`：isBigO_sub (x : E) : (fun x' => f (x' - 
x)) =O[l] fun x' => x' - x
-/
theorem isBigO_sub (l : Filter E) (x : E) : (fun x' => e (x' - x)) =O[l] fun x' => x' - x :=
  (e : E →SL[σ₁₂] F).isBigO_sub l x

end

section

variable [RingHomIsometric σ₂₁]

/-
**ContinuousLinearEquiv.isBigO_comp_rev** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：isBigO_comp_rev {α : Type*} (f : α -> E) (l : Filter α) : f =O[l] fun x' =
> e (f x')
参数：f : α -> E；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ : α 
→ E}, f₁ =O[l] g → …
· 使用定理 `ContinuousLinearEquiv.isBigO_comp`：isBigO_comp {α : Type*} (f : α -> E) 
(l : Filter α) : (fun x' => e (f x')) =O[l] f
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
-/
theorem isBigO_comp_rev {α : Type*} (f : α → E) (l : Filter α) : f =O[l] fun x' => e (f x') :=
  (e.symm.isBigO_comp _ l).congr_left fun _ => e.symm_apply_apply _
/-
**ContinuousLinearEquiv.isBigO_sub_rev** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arEquiv`。
形式化陈述：isBigO_sub_rev (l : Filter E) (x : E) : (fun x' => x' - x) =O[l] fun x' =>
 e (x' - x)
参数：l : Filter E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.isBigO_comp_rev`：isBigO_comp_rev {α : Type*} (f : 
α -> E) (l : Filter α) : f =O[l] fun x' => e (f x')
-/
theorem isBigO_sub_rev (l : Filter E) (x : E) : (fun x' => x' - x) =O[l] fun x' => e (x' - x) :=
  e.isBigO_comp_rev _ _

end

end ContinuousLinearEquiv

