/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Notation

/-!
# `C^n` bundled maps

In this file we define the type `ContMDiffMap` of `n` times continuously differentiable
bundled maps.
-/

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners 𝕜 E H}
  {I' : ModelWithCorners 𝕜 E' H'} (M : Type*) [TopologicalSpace M] [ChartedSpace H M] (M' : Type*)
  [TopologicalSpace M'] [ChartedSpace H' M'] {E'' : Type*} [NormedAddCommGroup E'']
  [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare a manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N] (n : WithTop ℕ∞)

open scoped Manifold

variable (I I') in
/-- Bundled `n` times continuously differentiable maps,
denoted as `C^n(I, M; I', M')` and `C^n(I, M; k)` (when the target is a normed space `k` with
the trivial model) in the `Manifold` namespace. -/
/-
**ContMDiffMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContMDiffMap
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled `n` times continuously differentiable maps,
denoted as `C^n(I, M; I', M')` and `C^n(I, M; k)` (when the target is a normed s
pace `k` with
the trivial model) in the `Manifold` namespace.
-/
def ContMDiffMap :=
  { f : M → M' // CMDiff n f }

@[inherit_doc]
scoped[Manifold] notation "C^" n "⟮" I ", " M "; " I' ", " M' "⟯" => ContMDiffMap I I' M M' n

@[inherit_doc]
scoped[Manifold]
  notation "C^" n "⟮" I ", " M "; " k "⟯" => ContMDiffMap I (modelWithCornersSelf k k) M k n

open scoped Manifold ContDiff

namespace ContMDiffMap

variable {M} {M'} {n}

/-
**ContMDiffMap.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
形式化陈述：instFunLike : FunLike C^n⟮I, M; I', M'⟯ M M' where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike C^n⟮I, M; I', M'⟯ M M' where
  coe := Subtype.val
  coe_injective := Subtype.coe_injective
/-
**ContMDiffMap.contMDiff** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_3} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E'] {H : Type u_4}   [inst_5 : To
pologicalSpace H] {H' : Type u_5} [inst_6 : TopologicalSpace H'] {I : ModelWithC
orners 𝕜 E H}   {I' : ModelWithCorners 𝕜 E' H'} {M : Type u_6} [inst_7 : Topolog
icalSpace M] [inst_8 : ChartedSpace H M]   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {n : WithTop ℕ∞}   (f : ContMDiffMap I 
I' M M' n), ContMDiff I I' n ⇑f
参数：f : ContMDiffMap I I' M M' n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
protected theorem contMDiff (f : C^n⟮I, M; I', M'⟯) : CMDiff n f := f.prop

attribute [to_additive_ignore_args 21] ContMDiffMap ContMDiffMap.instFunLike

variable {f g : C^n⟮I, M; I', M'⟯}

@[simp]
/-
**ContMDiffMap.coeFn_mk** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：coeFn_mk (f : M -> M') (hf : CMDiff n f) : DFunLike.coe (F
参数：f : M -> M'；hf : CMDiff n f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_mk (f : M → M') (hf : CMDiff n f) :
    DFunLike.coe (F := C^n⟮I, M; I', M'⟯) ⟨f, hf⟩ = f :=
  rfl
/-
**ContMDiffMap.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：coe_injective ⦃f g : C^n⟮I, M; I', M'⟯⦄ (h : (f : M -> M') = g) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem coe_injective ⦃f g : C^n⟮I, M; I', M'⟯⦄ (h : (f : M → M') = g) : f = g :=
  DFunLike.ext' h

@[ext]
/-
**ContMDiffMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：ext (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h
/-
**ContMDiffMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousMapClass C^n⟮I, M; I', M'⟯ M M' where
  map_continuous f := f.contMDiff.continuous

/-- The identity as a `C^n` map. -/
nonrec def id : C^n⟮I, M; I, M⟯ :=
  ⟨id, contMDiff_id⟩

/-- The composition of `C^n` maps, as a `C^n` map. -/
/-
**ContMDiffMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：comp (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) : C^n⟮I, M; I'', 
M''⟯ where val a
参数：f : C^n⟮I', M'; I'', M''⟯；g : C^n⟮I, M; I', M'⟯。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of `C^n` maps, as a `C^n` map.
-/
def comp (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) : C^n⟮I, M; I'', M''⟯ where
  val a := f (g a)
  property := f.contMDiff.comp g.contMDiff

@[simp]
/-
**ContMDiffMap.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：comp_apply (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) (x : M) : f
.comp g x = f (g x)
参数：f : C^n⟮I', M'; I'', M''⟯；g : C^n⟮I, M; I', M'⟯；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) (x : M) :
    f.comp g x = f (g x) :=
  rfl
/-
**ContMDiffMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited M'] : Inhabited C^n⟮I, M; I', M'⟯ :=
  ⟨⟨fun _ => default, contMDiff_const⟩⟩

/-- Constant map as a `C^n` map -/
/-
**ContMDiffMap.const** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：const (y : M') : C^n⟮I, M; I', M'⟯
参数：y : M'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c

--- 原说明 ---
Constant map as a `C^n` map
-/
def const (y : M') : C^n⟮I, M; I', M'⟯ :=
  ⟨fun _ => y, contMDiff_const⟩

/-- The first projection of a product, as a `C^n` map. -/
/-
**ContMDiffMap.fst** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：fst : C^n⟮I.prod I', M × M'; I, M⟯
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiff_fst`：contMDiff_fst : ContMDiff (I.prod J) I n (@Prod.fst M N)

--- 原说明 ---
The first projection of a product, as a `C^n` map.
-/
def fst : C^n⟮I.prod I', M × M'; I, M⟯ :=
  ⟨Prod.fst, contMDiff_fst⟩

/-- The second projection of a product, as a `C^n` map. -/
/-
**ContMDiffMap.snd** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：snd : C^n⟮I.prod I', M × M'; I', M'⟯
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiff_snd`：contMDiff_snd : ContMDiff (I.prod J) J n (@Prod.snd M N)

--- 原说明 ---
The second projection of a product, as a `C^n` map.
-/
def snd : C^n⟮I.prod I', M × M'; I', M'⟯ :=
  ⟨Prod.snd, contMDiff_snd⟩

/-- Given two `C^n` maps `f` and `g`, this is the `C^n` map `x ↦ (f x, g x)`. -/
/-
**ContMDiffMap.prodMk** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：prodMk (f : C^n⟮J, N; I, M⟯) (g : C^n⟮J, N; I', M'⟯) : C^n⟮J, N; I.prod I'
, M × M'⟯
参数：f : C^n⟮J, N; I, M⟯；g : C^n⟮J, N; I', M'⟯。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two `C^n` maps `f` and `g`, this is the `C^n` map `x ↦ (f x, g x)`.
-/
def prodMk (f : C^n⟮J, N; I, M⟯) (g : C^n⟮J, N; I', M'⟯) : C^n⟮J, N; I.prod I', M × M'⟯ :=
  ⟨fun x => (f x, g x), f.2.prodMk g.2⟩

end ContMDiffMap

/-
**ContinuousLinearMap.hasCoeToContMDiffMap** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.hasCoeToContMDiffMap : Coe (E ->L[𝕜] E') C^n⟮𝓘(𝕜, E), 
E; 𝓘(𝕜, E'), E'⟯
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.contMDiff`：ContinuousLinearMap.contMDiff (L : E ->L[
𝕜] F) : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n L
-/
instance ContinuousLinearMap.hasCoeToContMDiffMap :
    Coe (E →L[𝕜] E') C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, E'), E'⟯ :=
  ⟨fun f => ⟨f, f.contMDiff⟩⟩
