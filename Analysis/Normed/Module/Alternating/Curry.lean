/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Currying continuous alternating forms

In this file we define `ContinuousAlternatingMap.curryLeft`
which interprets a continuous alternating map in `n + 1` variables
as a continuous linear map in the 0th variable
taking values in the continuous alternating maps in `n` variables.
-/

@[expose] public section

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ}

namespace ContinuousAlternatingMap

/-- Given a continuous alternating map `f` in `n+1` variables, split the first variable to obtain
a continuous linear map into continuous alternating maps in `n` variables,
given by `x ↦ (m ↦ f (Matrix.vecCons x m))`.
It can be thought of as a map $Hom(\bigwedge^{n+1} M, N) \to Hom(M, Hom(\bigwedge^n M, N))$.

This is `ContinuousMultilinearMap.curryLeft` for `AlternatingMap`. See also
`ContinuousAlternatingMap.curryLeftLI`. -/
/-
**ContinuousAlternatingMap.curryLeft** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAltern
atingMap`。
形式化陈述：curryLeft (f : E [⋀^Fin (n + 1)]->L[𝕜] F) : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F
参数：f : E [⋀^Fin (n + 1)]->L[𝕜] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous alternating map `f` in `n+1` variables, split the first varia
ble to obtain
a continuous linear map into continuous alternating maps in `n` variables,
given by `x ↦ (m ↦ f (Matrix.vecCons x m))`.
It can be thought of as a map $Hom(\bigwedge^{n+1} M, N) \to Hom(M, Hom(\bigwedg
e^n M, N))$.

This is `ContinuousMultilinearMap.curryLeft` for `AlternatingMap`. See also
`ContinuousAlternatingMap.curryLeftLI`.
-/
noncomputable def curryLeft (f : E [⋀^Fin (n + 1)]→L[𝕜] F) : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F :=
  AlternatingMap.mkContinuousLinear f.toAlternatingMap.curryLeft ‖f‖
    f.toContinuousMultilinearMap.norm_map_cons_le

@[simp]
/-
**ContinuousAlternatingMap.toContinuousMultilinearMap_curryLeft** 是 Mathlib 中的一个
引理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：toContinuousMultilinearMap_curryLeft (f : E [⋀^Fin (n + 1)]->L[𝕜] F) (x : 
E) : (f.curryLeft x).toContinuousMultilinearMap = f.toContinuousMultilinearMap.c
urryLeft x
参数：f : E [⋀^Fin (n + 1)]->L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma toContinuousMultilinearMap_curryLeft (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) :
    (f.curryLeft x).toContinuousMultilinearMap = f.toContinuousMultilinearMap.curryLeft x :=
  rfl

@[simp]
/-
**ContinuousAlternatingMap.toAlternatingMap_curryLeft** 是 Mathlib 中的一个引理，位于命名空间 
`ContinuousAlternatingMap`。
形式化陈述：toAlternatingMap_curryLeft (f : E [⋀^Fin (n + 1)]->L[𝕜] F) (x : E) : (f.cu
rryLeft x).toAlternatingMap = f.toAlternatingMap.curryLeft x
参数：f : E [⋀^Fin (n + 1)]->L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma toAlternatingMap_curryLeft (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) :
    (f.curryLeft x).toAlternatingMap = f.toAlternatingMap.curryLeft x :=
  rfl

@[simp]
/-
**ContinuousAlternatingMap.norm_curryLeft** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousA
lternatingMap`。
形式化陈述：norm_curryLeft (f : E [⋀^Fin (n + 1)]->L[𝕜] F) : ‖f.curryLeft‖ = ‖f‖
参数：f : E [⋀^Fin (n + 1)]->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.curryLeft_norm`：ContinuousMultilinearMap.curryL
eft_norm (f : ContinuousMultilinearMap 𝕜 Ei G) : ‖f.curryLeft‖ = ‖f‖
-/
lemma norm_curryLeft (f : E [⋀^Fin (n + 1)]→L[𝕜] F) : ‖f.curryLeft‖ = ‖f‖ :=
  f.toContinuousMultilinearMap.curryLeft_norm

@[simp]
/-
**ContinuousAlternatingMap.curryLeft_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousAlternatingMap`。
形式化陈述：curryLeft_apply_apply (f : E [⋀^Fin (n + 1)]->L[𝕜] F) (x : E) (v : Fin n -
> E) : curryLeft f x v = f (Matrix.vecCons x v)
参数：f : E [⋀^Fin (n + 1)]->L[𝕜] F；x : E；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem curryLeft_apply_apply (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) (v : Fin n → E) :
    curryLeft f x v = f (Matrix.vecCons x v) :=
  rfl

@[simp]
/-
**ContinuousAlternatingMap.curryLeft_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousA
lternatingMap`。
形式化陈述：curryLeft_zero : curryLeft (0 : E [⋀^Fin (n + 1)]->L[𝕜] F) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem curryLeft_zero : curryLeft (0 : E [⋀^Fin (n + 1)]→L[𝕜] F) = 0 :=
  rfl

@[simp]
/-
**ContinuousAlternatingMap.curryLeft_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAl
ternatingMap`。
形式化陈述：curryLeft_add (f g : E [⋀^Fin (n + 1)]->L[𝕜] F) : curryLeft (f + g) = curr
yLeft f + curryLeft g
参数：f g : E [⋀^Fin (n + 1)]->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem curryLeft_add (f g : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    curryLeft (f + g) = curryLeft f + curryLeft g :=
  rfl

@[simp]
/-
**ContinuousAlternatingMap.curryLeft_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousA
lternatingMap`。
形式化陈述：curryLeft_smul (r : 𝕜) (f : E [⋀^Fin (n + 1)]->L[𝕜] F) : curryLeft (r • f)
 = r • curryLeft f
参数：r : 𝕜；f : E [⋀^Fin (n + 1)]->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem curryLeft_smul (r : 𝕜) (f : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    curryLeft (r • f) = r • curryLeft f :=
  rfl

/-- `ContinuousAlternatingMap.curryLeft` as a `LinearIsometry`. -/
@[simps]
/-
**ContinuousAlternatingMap.curryLeftLI** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlte
rnatingMap`。
形式化陈述：curryLeftLI : (E [⋀^Fin (n + 1)]->L[𝕜] F) ->ₗᵢ[𝕜] (E ->L[𝕜] E [⋀^Fin n]->L
[𝕜] F) where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.curryLeft_add`：curryLeft_add (f g : E [⋀^Fin (n
 + 1)]->L[𝕜] F) : curryLeft (f + g) = curryLeft f + curryLeft g
· 使用定理 `ContinuousAlternatingMap.curryLeft_smul`：curryLeft_smul (r : 𝕜) (f : E [
⋀^Fin (n + 1)]->L[𝕜] F) : curryLeft (r • f) = r • curryLeft f
· 使用引理 `ContinuousAlternatingMap.norm_curryLeft`：norm_curryLeft (f : E [⋀^Fin (n
 + 1)]->L[𝕜] F) : ‖f.curryLeft‖ = ‖f‖

--- 原说明 ---
`ContinuousAlternatingMap.curryLeft` as a `LinearIsometry`.
-/
noncomputable def curryLeftLI :
    (E [⋀^Fin (n + 1)]→L[𝕜] F) →ₗᵢ[𝕜] (E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) where
  toFun f := f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul
  norm_map' := norm_curryLeft

/-- Currying with the same element twice gives the zero map. -/
@[simp]
/-
**ContinuousAlternatingMap.curryLeft_same** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousA
lternatingMap`。
形式化陈述：curryLeft_same (f : E [⋀^Fin (n + 2)]->L[𝕜] F) (x : E) : (f.curryLeft x).c
urryLeft x = 0
参数：f : E [⋀^Fin (n + 2)]->L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.ext`：ext {f g : M [⋀^ι]->L[R] N} (H : forall x,
 f x = g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousAlternatingMap.map_eq_zero_of_eq`：map_eq_zero_of_eq (v : ι -> 
M) {i j : ι} (h : v i = v j) (hij : i != j) : f v = 0
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Fin.cons_one`：cons_one {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall 
i : Fin n.succ, α i.succ) : cons x p 1 = p 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.zero_ne_one`：∀ {n : ℕ}, 0 ≠ 1

--- 原说明 ---
Currying with the same element twice gives the zero map.
-/
theorem curryLeft_same (f : E [⋀^Fin (n + 2)]→L[𝕜] F) (x : E) :
    (f.curryLeft x).curryLeft x = 0 :=
  ext fun _ ↦ f.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one

@[simp]
/-
**ContinuousAlternatingMap.curryLeft_compContinuousAlternatingMap** 是 Mathlib 中的
一个定理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：curryLeft_compContinuousAlternatingMap (g : F ->L[𝕜] G) (f : E [⋀^Fin (n +
 1)]->L[𝕜] F) (x : E) : (g.compContinuousAlternatingMap f).curryLeft x = g.compC
ontinuousAlternatingMap (f.curryLeft x)
参数：g : F ->L[𝕜] G；f : E [⋀^Fin (n + 1)]->L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem curryLeft_compContinuousAlternatingMap (g : F →L[𝕜] G) (f : E [⋀^Fin (n + 1)]→L[𝕜] F)
    (x : E) :
    (g.compContinuousAlternatingMap f).curryLeft x =
      g.compContinuousAlternatingMap (f.curryLeft x) :=
  rfl

@[simp]
/-
**ContinuousAlternatingMap.curryLeft_compContinuousLinearMap** 是 Mathlib 中的一个定理，
位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：curryLeft_compContinuousLinearMap (g : F [⋀^Fin (n + 1)]->L[𝕜] G) (f : E -
>L[𝕜] F) (x : E) : (g.compContinuousLinearMap f).curryLeft x = (g.curryLeft (f x
)).compContinuousLinearMap f
参数：g : F [⋀^Fin (n + 1)]->L[𝕜] G；f : E ->L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.ext`：ext {f g : M [⋀^ι]->L[R] N} (H : forall x,
 f x = g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
-/
theorem curryLeft_compContinuousLinearMap (g : F [⋀^Fin (n + 1)]→L[𝕜] G) (f : E →L[𝕜] F) (x : E) :
    (g.compContinuousLinearMap f).curryLeft x = (g.curryLeft (f x)).compContinuousLinearMap f :=
  ext fun v ↦ congr_arg g <| funext fun i ↦ by cases i using Fin.cases <;> simp

end ContinuousAlternatingMap

