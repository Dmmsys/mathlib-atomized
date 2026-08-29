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
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N] (n : WithTop Nat∞)

open scoped Manifold

variable (I I') in
/--
Definition of `ContMDiffMap` / `ContMDiffMap` 的定义

English:
definition ContMDiffMap
  body: { f : M -> M' // CMDiff n f }

@[inherit_doc]
scoped[Manifold] notation "C^" n "⟮" I ", " M "; " I' ", " M' "⟯" => ContMDiffMap I I' M M' n

@[inherit_doc]
scoped[Manifold]
  notation "C^" n "⟮" I ", " M "; " k "⟯" => ContMDiffMap I (modelWithCornersSelf k k) M k n

中文:
定义 ContMDiffMap
  定义体: { f : M -> M' // CMDiff n f }

@[inherit_doc]
scoped[Manifold] notation "C^" n "⟮" I ", " M "; " I' ", " M' "⟯" => ContMDiffMap I I' M M' n

@[inherit_doc]
scoped[Manifold]
  notation "C^" n "⟮" I ", " M "; " k "⟯" => ContMDiffMap I (modelWithCornersSelf k k) M k n

Depends on / 依赖: CMDiff
-/
def ContMDiffMap :=
  { f : M -> M' // CMDiff n f }

@[inherit_doc]
scoped[Manifold] notation "C^" n "⟮" I ", " M "; " I' ", " M' "⟯" => ContMDiffMap I I' M M' n

@[inherit_doc]
scoped[Manifold]
  notation "C^" n "⟮" I ", " M "; " k "⟯" => ContMDiffMap I (modelWithCornersSelf k k) M k n

open scoped Manifold ContDiff

namespace ContMDiffMap

variable {M} {M'} {n}

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike C^n⟮I, M; I', M'⟯ M M' where
  body: Subtype.val
  coe_injective := Subtype.coe_injective

中文:
实例 instFunLike
  签名: : 函数状 C^n⟮I, M; I', M'⟯ M M' where
  定义体: Subtype.val
  coe_injective := Subtype.coe_injective

Depends on / 依赖: Subtype, Subtype.val
-/
instance instFunLike : FunLike C^n⟮I, M; I', M'⟯ M M' where
  coe := Subtype.val
  coe_injective := Subtype.coe_injective

/--
theorem `contMDiff` / 定理 `contMDiff`

English:
theorem contMDiff
  given: (f : C^n⟮I, M; I', M'⟯)
  statement: CMDiff n f
  proof: f.prop

中文:
定理 contMDiff
  条件: (f : C^n⟮I, M; I', M'⟯)
  结论: CMDiff n f
  证明: f.prop
-/
protected theorem contMDiff (f : C^n⟮I, M; I', M'⟯) : CMDiff n f := f.prop

attribute [to_additive_ignore_args 21] ContMDiffMap ContMDiffMap.instFunLike

variable {f g : C^n⟮I, M; I', M'⟯}

@[simp]
/--
theorem `coeFn_mk` / 定理 `coeFn_mk`

English:
theorem coeFn_mk
  given: (f : M -> M') (hf : CMDiff n f)
  proof: rfl

中文:
定理 coeFn_mk
  条件: (f : M -> M') (hf : CMDiff n f)
  证明: rfl
-/
theorem coeFn_mk (f : M -> M') (hf : CMDiff n f) :
    DFunLike.coe (F := C^n⟮I, M; I', M'⟯) ⟨f, hf⟩ = f :=
  rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  given: ⦃f g
  statement: C^n⟮I, M; I', M'⟯⦄ (h : (f : M -> M') = g) : f = g
  proof: DFunLike.ext' h

@[ext]

中文:
定理 coe_injective
  条件: ⦃f g
  结论: C^n⟮I, M; I', M'⟯⦄ (h : (f : M -> M') = g) : f = g
  证明: DFunLike.ext' h

@[ext]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem coe_injective ⦃f g : C^n⟮I, M; I', M'⟯⦄ (h : (f : M -> M') = g) : f = g :=
  DFunLike.ext' h

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext (h : forall x, f x = g x) : f = g := DFunLike.ext _ _ h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousMapClass C^n⟮I, M; I', M'⟯ M M'
  body: f.contMDiff.continuous

中文:
实例 :
  签名: 连续映射类 C^n⟮I, M; I', M'⟯ M M'
  定义体: f.contMDiff.continuous

Depends on / 依赖: contMDiff, continuous, f.contMDiff.continuous
-/
instance : ContinuousMapClass C^n⟮I, M; I', M'⟯ M M' where
  map_continuous f := f.contMDiff.continuous

/-- The identity as a `C^n` map. -/
nonrec def id : C^n⟮I, M; I, M⟯ :=
  ⟨id, contMDiff_id⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯)
  body: f (g a)
  property := f.contMDiff.comp g.contMDiff

@[simp]

中文:
定义 comp
  签名: (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯)
  定义体: f (g a)
  property := f.contMDiff.comp g.contMDiff

@[simp]
-/
def comp (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) : C^n⟮I, M; I'', M''⟯ where
  val a := f (g a)
  property := f.contMDiff.comp g.contMDiff

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) (x : M)
  proof: rfl

中文:
定理 comp_apply
  条件: (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) (x : M)
  证明: rfl
-/
theorem comp_apply (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) (x : M) :
    f.comp g x = f (g x) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: M'] : Inhabited C^n⟮I, M; I', M'⟯
  body: ⟨⟨fun _ => default, contMDiff_const⟩⟩

中文:
实例 [可居
  签名: M'] : 可居 C^n⟮I, M; I', M'⟯
  定义体: ⟨⟨fun _ => default, contMDiff_const⟩⟩

Depends on / 依赖: contMDiff_const
-/
instance [Inhabited M'] : Inhabited C^n⟮I, M; I', M'⟯ :=
  ⟨⟨fun _ => default, contMDiff_const⟩⟩

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (y : M')
  body: ⟨fun _ => y, contMDiff_const⟩

中文:
定义 const
  签名: (y : M')
  定义体: ⟨fun _ => y, contMDiff_const⟩

Depends on / 依赖: contMDiff_const
-/
def const (y : M') : C^n⟮I, M; I', M'⟯ :=
  ⟨fun _ => y, contMDiff_const⟩

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : C^n⟮I.prod I', M × M'; I, M⟯
  body: ⟨Prod.fst, contMDiff_fst⟩

中文:
定义 fst
  签名: : C^n⟮I.乘积 I', M × M'; I, M⟯
  定义体: ⟨Prod.fst, contMDiff_fst⟩

Depends on / 依赖: Prod.fst, contMDiff_fst
-/
def fst : C^n⟮I.prod I', M × M'; I, M⟯ :=
  ⟨Prod.fst, contMDiff_fst⟩

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : C^n⟮I.prod I', M × M'; I', M'⟯
  body: ⟨Prod.snd, contMDiff_snd⟩

中文:
定义 snd
  签名: : C^n⟮I.乘积 I', M × M'; I', M'⟯
  定义体: ⟨Prod.snd, contMDiff_snd⟩

Depends on / 依赖: Prod.snd, contMDiff_snd
-/
def snd : C^n⟮I.prod I', M × M'; I', M'⟯ :=
  ⟨Prod.snd, contMDiff_snd⟩

/--
Definition of `prodMk` / `prodMk` 的定义

English:
definition prodMk
  signature: (f : C^n⟮J, N; I, M⟯) (g : C^n⟮J, N; I', M'⟯)
  body: ⟨fun x => (f x, g x), f.2.prodMk g.2⟩

中文:
定义 prodMk
  签名: (f : C^n⟮J, N; I, M⟯) (g : C^n⟮J, N; I', M'⟯)
  定义体: ⟨fun x => (f x, g x), f.2.prodMk g.2⟩

Depends on / 依赖: prodMk
-/
def prodMk (f : C^n⟮J, N; I, M⟯) (g : C^n⟮J, N; I', M'⟯) : C^n⟮J, N; I.prod I', M × M'⟯ :=
  ⟨fun x => (f x, g x), f.2.prodMk g.2⟩

end ContMDiffMap

/--
Instance `ContinuousLinearMap.hasCoeToContMDiffMap` / 实例 `ContinuousLinearMap.hasCoeToContMDiffMap`

English:
instance ContinuousLinearMap.hasCoeToContMDiffMap
  signature: :
  body: ⟨fun f => ⟨f, f.contMDiff⟩⟩

中文:
实例 连续线性映射.hasCoeToContMDiffMap
  签名: :
  定义体: ⟨fun f => ⟨f, f.contMDiff⟩⟩

Depends on / 依赖: contMDiff, f.contMDiff
-/
instance ContinuousLinearMap.hasCoeToContMDiffMap :
    Coe (E ->L[𝕜] E') C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, E'), E'⟯ :=
  ⟨fun f => ⟨f, f.contMDiff⟩⟩
