/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# Local diffeomorphisms between manifolds

In this file, we define `C^n` local diffeomorphisms between manifolds.

A `C^n` map `f : M → N` is a **local diffeomorphism at `x`** iff there are neighbourhoods `s`
and `t` of `x` and `f x`, respectively, such that `f` restricts to a diffeomorphism
between `s` and `t`. `f` is called a **local diffeomorphism on `s`** iff it is a local
diffeomorphism at every `x ∈ s`, and a **local diffeomorphism** iff it is a local diffeomorphism on
`univ`.

## Main definitions
* `IsLocalDiffeomorphAt I J n f x`: `f` is a `C^n` local diffeomorphism at `x`
* `IsLocalDiffeomorphOn I J n f s`: `f` is a `C^n` local diffeomorphism on `s`
* `IsLocalDiffeomorph I J n f`: `f` is a `C^n` local diffeomorphism

## Main results
* Each of `Diffeomorph`, `IsLocalDiffeomorph`, `IsLocalDiffeomorphOn` and `IsLocalDiffeomorphAt`
  implies the next condition.
* `IsLocalDiffeomorph.isLocalHomeomorph`: a local diffeomorphism is a local homeomorphism,
  and similarly for a local diffeomorphism on `s`.
* `IsLocalDiffeomorph.isOpen_range`: the image of a local diffeomorphism is open
* `IsLocalDiffeomorph.diffeomorphOfBijective`:
  a bijective local diffeomorphism is a diffeomorphism

* `Diffeomorph.mfderivToContinuousLinearEquiv`: each differential of a `C^n` diffeomorphism
  (`n ≠ 0`) is a linear equivalence.
* `LocalDiffeomorphAt.mfderivToContinuousLinearEquiv`: if `f` is a local diffeomorphism
  at `x`, the differential `mfderiv I J n f x` is a continuous linear equivalence.
* `LocalDiffeomorph.mfderivToContinuousLinearEquiv`: if `f` is a local diffeomorphism,
  each differential `mfderiv I J n f x` is a continuous linear equivalence.

## TODO
* an injective local diffeomorphism is a diffeomorphism to its image
* if `f` is `C^n` at `x` and `mfderiv I J n f x` is a linear isomorphism,
  `f` is a local diffeomorphism at `x` (using the inverse function theorem).

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of local structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

## Tags
local diffeomorphism, manifold

-/

public noncomputable section

open Manifold Set TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H₁ : Type*} [TopologicalSpace H₁]
  {H₂ : Type*} [TopologicalSpace H₂]
  {H₃ : Type*} [TopologicalSpace H₃]
  (I : ModelWithCorners 𝕜 E H₁) (J : ModelWithCorners 𝕜 F H₂) (K : ModelWithCorners 𝕜 F' H₃)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H₁ M]
  (N : Type*) [TopologicalSpace N] [ChartedSpace H₂ N]
  (P : Type*) [TopologicalSpace P] [ChartedSpace H₃ P] (n : WithTop ℕ∞)

section PartialDiffeomorph
/-- A partial diffeomorphism on `s` is a function `f : M → N` such that `f` restricts to a
diffeomorphism `s → t` between open subsets of `M` and `N`, respectively.
This is an auxiliary definition and should not be used outside of this file. -/
/-
**PartialDiffeomorph** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {F : Type u_3} →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace 𝕜 F] →                 {H₁ : Type u_5} →           
        [inst_5 : TopologicalSpace H₁] →                     {H₂ : Type u_6} →  
                     [inst_6 : TopologicalSpace H₂] →                         Mo
delWithCorners 𝕜 E H₁ →                           ModelWithCorners 𝕜 F H₂ →     
                        (M : Type u_8) →                               [inst : T
opologicalSpace M] →                                 [ChartedSpace H₁ M] →      
                             (N : Type u_9) →                                   
  [inst : TopologicalSpace N] → [ChartedSpace H₂ N] → WithTop ℕ∞ → Type (max u_8
 u_9)
参数：M : Type u_8；N : Type u_9；max u_8 u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partial diffeomorphism on `s` is a function `f : M → N` such that `f` restrict
s to a
diffeomorphism `s → t` between open subsets of `M` and `N`, respectively.
This is an auxiliary definition and should not be used outside of this file.
-/
structure PartialDiffeomorph extends PartialEquiv M N where
  open_source : IsOpen source
  open_target : IsOpen target
  contMDiffOn_toFun : CMDiff[source] n toFun
  contMDiffOn_invFun : CMDiff[target] n invFun

/-- Coercion of a `PartialDiffeomorph` to function.
Note that a `PartialDiffeomorph` is not `DFunLike` (like `OpenPartialHomeomorph`),
as `toFun` doesn't determine `invFun` outside of `target`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of a `PartialDiffeomorph` to function.
Note that a `PartialDiffeomorph` is not `DFunLike` (like `OpenPartialHomeomorph`
),
as `toFun` doesn't determine `invFun` outside of `target`.
-/
instance : CoeFun (PartialDiffeomorph I J M N n) fun _ => M → N :=
  ⟨fun Φ => Φ.toFun⟩

variable {I J K M N P n}

/-- A diffeomorphism is a partial diffeomorphism. -/
/-
**Diffeomorph.toPartialDiffeomorph** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Diffeomorph.toPartialDiffeomorph (h : Diffeomorph I J M N n) : PartialDiff
eomorph I J M N n where toPartialEquiv
参数：h : Diffeomorph I J M N n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Diffeomorph.contMDiff_toFun`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {E' : Type u…

--- 原说明 ---
A diffeomorphism is a partial diffeomorphism.
-/
def Diffeomorph.toPartialDiffeomorph (h : Diffeomorph I J M N n) :
    PartialDiffeomorph I J M N n where
  toPartialEquiv := h.toHomeomorph.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun x _ := h.contMDiff_toFun x
  contMDiffOn_invFun _ _ := h.symm.contMDiffWithinAt

-- Add the very basic API we need.
namespace PartialDiffeomorph
variable (Φ : PartialDiffeomorph I J M N n)

/-- A partial diffeomorphism is also a local homeomorphism. -/
@[expose, simps toPartialHomeomorph_toPartialEquiv]
/-
**PartialDiffeomorph.toOpenPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `PartialD
iffeomorph`。
形式化陈述：toOpenPartialHomeomorph : OpenPartialHomeomorph M N where toPartialEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PartialDiffeomorph.open_source`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用定理 `PartialDiffeomorph.open_target`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…

--- 原说明 ---
A partial diffeomorphism is also a local homeomorphism.
-/
def toOpenPartialHomeomorph : OpenPartialHomeomorph M N where
  toPartialEquiv := Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  continuousOn_toFun := Φ.contMDiffOn_toFun.continuousOn
  continuousOn_invFun := Φ.contMDiffOn_invFun.continuousOn

/-- The inverse of a local diffeomorphism. -/
@[expose, simps toPartialEquiv]
/-
**PartialDiffeomorph.symm** 是 Mathlib 中的一个定义，位于命名空间 `PartialDiffeomorph`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {F : Type u_3} →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace 𝕜 F] →                 {H₁ : Type u_5} →           
        [inst_5 : TopologicalSpace H₁] →                     {H₂ : Type u_6} →  
                     [inst_6 : TopologicalSpace H₂] →                         {I
 : ModelWithCorners 𝕜 E H₁} →                           {J : ModelWithCorners 𝕜 
F H₂} →                             {M : Type u_8} →                            
   [inst_7 : TopologicalSpace M] →                                 [inst_8 : Cha
rtedSpace H₁ M] →                                   {N : Type u_9} →            
                         [inst_9 : TopologicalSpace N] →                        
               [inst_10 : ChartedSpace H₂ N] →                                  
       {n : WithTop ℕ∞} → PartialDiffeomorph I J M N n → PartialDiffeomorph J I 
N M n
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PartialDiffeomorph.open_target`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用定理 `PartialDiffeomorph.open_source`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用定理 `PartialDiffeomorph.contMDiffOn_invFun`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {F : Type u_…
· 使用定理 `PartialDiffeomorph.contMDiffOn_toFun`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…

--- 原说明 ---
The inverse of a local diffeomorphism.
-/
protected def symm : PartialDiffeomorph J I N M n where
  toPartialEquiv := Φ.toPartialEquiv.symm
  open_source := Φ.open_target
  open_target := Φ.open_source
  contMDiffOn_toFun := Φ.contMDiffOn_invFun
  contMDiffOn_invFun := Φ.contMDiffOn_toFun
/-
**PartialDiffeomorph.contMDiffOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialDiffeomorph`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {H₁ : Type u_5}   [inst_5 : Topo
logicalSpace H₁] {H₂ : Type u_6} [inst_6 : TopologicalSpace H₂] {I : ModelWithCo
rners 𝕜 E H₁}   {J : ModelWithCorners 𝕜 F H₂} {M : Type u_8} [inst_7 : Topologic
alSpace M] [inst_8 : ChartedSpace H₁ M] {N : Type u_9}   [inst_9 : TopologicalSp
ace N] [inst_10 : ChartedSpace H₂ N] {n : WithTop ℕ∞} (Φ : PartialDiffeomorph I 
J M N n),   ContMDiffOn I J n (↑Φ.toPartialEquiv) Φ.source
参数：Φ : PartialDiffeomorph I J M N n；↑Φ.toPartialEquiv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialDiffeomorph.contMDiffOn_toFun`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
-/
protected theorem contMDiffOn : CMDiff[Φ.source] n Φ := Φ.contMDiffOn_toFun
/-
**PartialDiffeomorph.mdifferentiableOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialDiffeom
orph`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {H₁ : Type u_5}   [inst_5 : Topo
logicalSpace H₁] {H₂ : Type u_6} [inst_6 : TopologicalSpace H₂] {I : ModelWithCo
rners 𝕜 E H₁}   {J : ModelWithCorners 𝕜 F H₂} {M : Type u_8} [inst_7 : Topologic
alSpace M] [inst_8 : ChartedSpace H₁ M] {N : Type u_9}   [inst_9 : TopologicalSp
ace N] [inst_10 : ChartedSpace H₂ N] {n : WithTop ℕ∞} (Φ : PartialDiffeomorph I 
J M N n),   n ≠ 0 → MDiff[Φ.source] ↑Φ.toPartialEquiv
参数：Φ : PartialDiffeomorph I J M N n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.mdifferentiableOn`：ContMDiffOn.mdifferentiableOn (hf : CMDif
f[s] n f) (hn : n != 0) : MDiff[s] f
· 使用定理 `PartialDiffeomorph.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
-/
protected theorem mdifferentiableOn (hn : n ≠ 0) : MDiff[Φ.source] Φ :=
  (Φ.contMDiffOn).mdifferentiableOn hn
/-
**PartialDiffeomorph.mdifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `PartialDiffeom
orph`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {H₁ : Type u_5}   [inst_5 : Topo
logicalSpace H₁] {H₂ : Type u_6} [inst_6 : TopologicalSpace H₂] {I : ModelWithCo
rners 𝕜 E H₁}   {J : ModelWithCorners 𝕜 F H₂} {M : Type u_8} [inst_7 : Topologic
alSpace M] [inst_8 : ChartedSpace H₁ M] {N : Type u_9}   [inst_9 : TopologicalSp
ace N] [inst_10 : ChartedSpace H₂ N] {n : WithTop ℕ∞} (Φ : PartialDiffeomorph I 
J M N n),   n ≠ 0 → ∀ {x : M}, x ∈ Φ.source → MDiffAt ↑Φ.toPartialEquiv x
参数：Φ : PartialDiffeomorph I J M N n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.mdifferentiableAt`：MDifferentiableWithinAt.mdiff
erentiableAt (h : MDiffAt[s] f x) (hs : s in 𝓝 x) : MDiffAt f x
· 使用定理 `PartialDiffeomorph.mdifferentiableOn`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `PartialDiffeomorph.open_source`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
-/
protected theorem mdifferentiableAt (hn : n ≠ 0) {x : M} (hx : x ∈ Φ.source) :
    MDiffAt Φ x :=
  (Φ.mdifferentiableOn hn x hx).mdifferentiableAt (Φ.open_source.mem_nhds hx)

/-- Composition of partial diffeomorphisms. -/
@[expose, simps toPartialEquiv]
/-
**PartialDiffeomorph.trans** 是 Mathlib 中的一个定义，位于命名空间 `PartialDiffeomorph`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {F : Type u_3} →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace 𝕜 F] →                 {F' : Type u_4} →           
        [inst_5 : NormedAddCommGroup F'] →                     [inst_6 : NormedS
pace 𝕜 F'] →                       {H₁ : Type u_5} →                         [in
st_7 : TopologicalSpace H₁] →                           {H₂ : Type u_6} →       
                      [inst_8 : TopologicalSpace H₂] →                          
     {H₃ : Type u_7} →                                 [inst_9 : TopologicalSpac
e H₃] →                                   {I : ModelWithCorners 𝕜 E H₁} →       
                              {J : ModelWithCorners 𝕜 F H₂} →                   
                    {K : ModelWithCorners 𝕜 F' H₃} →                            
             {M : Type u_8} →                                           [inst_10
 : TopologicalSpace M] →                                             [inst_11 : 
ChartedSpace H₁ M] →                                               {N : Type u_9
} →                                                 [inst_12 : TopologicalSpace 
N] →                                                   [inst_13 : ChartedSpace H
₂ N] →                                                     {P : Type u_10} →    
                                                   [inst_14 : TopologicalSpace P
] →                                                         [inst_15 : ChartedSp
ace H₃ P] →                                                           {n : WithT
op ℕ∞} →                                                             PartialDiff
eomorph I J M N n →                                                             
  PartialDiffeomorph J K N P n →                                                
                 PartialDiffeomorph I K M P n
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…

--- 原说明 ---
Composition of partial diffeomorphisms.
-/
protected def trans (Ψ : PartialDiffeomorph J K N P n) : PartialDiffeomorph I K M P n where
  __ := Φ.toOpenPartialHomeomorph.trans Ψ.toOpenPartialHomeomorph
  contMDiffOn_toFun :=
    Ψ.contMDiffOn_toFun.comp (Φ.contMDiffOn_toFun.mono inter_subset_left) inter_subset_right
  contMDiffOn_invFun :=
    Φ.contMDiffOn_invFun.comp (Ψ.contMDiffOn_invFun.mono inter_subset_left) inter_subset_right

/- We could add lots of additional API (following `Diffeomorph` and `OpenPartialHomeomorph`),
such as
* further continuity and differentiability lemmas
* refl and trans instances; lemmas between them.

As this declaration is meant for internal use only, we keep it simple. -/
end PartialDiffeomorph
end PartialDiffeomorph

variable {M N}

/-- `f : M → N` is called a **`C^n` local diffeomorphism at `x`** iff there exist
open sets `U ∋ x` and `V ∋ f x` and a diffeomorphism `Φ : U → V` such that `f = Φ` on `U`. -/
/-
**IsLocalDiffeomorphAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorphAt (f : M -> N) (x : M) : Prop
参数：f : M -> N；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : M → N` is called a **`C^n` local diffeomorphism at `x`** iff there exist
open sets `U ∋ x` and `V ∋ f x` and a diffeomorphism `Φ : U → V` such that `f = 
Φ` on `U`.
-/
def IsLocalDiffeomorphAt (f : M → N) (x : M) : Prop :=
  ∃ Φ : PartialDiffeomorph I J M N n, x ∈ Φ.source ∧ EqOn f Φ Φ.source
/-
**PartialDiffeomorph.isLocalDiffeomorphAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PartialDiffeomorph.isLocalDiffeomorphAt (φ : PartialDiffeomorph I J M N n)
 {x : M} (hx : x in φ.source) : IsLocalDiffeomorphAt I J n φ x
参数：φ : PartialDiffeomorph I J M N n；hx : x in φ.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eqOn_refl`：eqOn_refl (f : α -> β) (s : Set α) : EqOn f f s
-/
lemma PartialDiffeomorph.isLocalDiffeomorphAt (φ : PartialDiffeomorph I J M N n)
    {x : M} (hx : x ∈ φ.source) : IsLocalDiffeomorphAt I J n φ x :=
  ⟨φ, hx, Set.eqOn_refl _ _⟩

namespace IsLocalDiffeomorphAt

variable {f : M → N} {x : M}

variable {I I' J n}

/-- An arbitrary choice of local inverse of `f` near `x`. -/
/-
**IsLocalDiffeomorphAt.localInverse** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalDiffeomorp
hAt`。
形式化陈述：localInverse (hf : IsLocalDiffeomorphAt I J n f x) : PartialDiffeomorph J 
I N M n
参数：hf : IsLocalDiffeomorphAt I J n f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary choice of local inverse of `f` near `x`.
-/
def localInverse (hf : IsLocalDiffeomorphAt I J n f x) :
    PartialDiffeomorph J I N M n := (Classical.choose hf).symm
/-
**IsLocalDiffeomorphAt.localInverse_open_source** 是 Mathlib 中的一个引理，位于命名空间 `IsLoc
alDiffeomorphAt`。
形式化陈述：localInverse_open_source (hf : IsLocalDiffeomorphAt I J n f x) : IsOpen hf
.localInverse.source
参数：hf : IsLocalDiffeomorphAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialDiffeomorph.open_source`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
-/
lemma localInverse_open_source (hf : IsLocalDiffeomorphAt I J n f x) :
    IsOpen hf.localInverse.source :=
  PartialDiffeomorph.open_source _
/-
**IsLocalDiffeomorphAt.localInverse_mem_source** 是 Mathlib 中的一个引理，位于命名空间 `IsLoca
lDiffeomorphAt`。
形式化陈述：localInverse_mem_source (hf : IsLocalDiffeomorphAt I J n f x) : f x in hf.
localInverse.source
参数：hf : IsLocalDiffeomorphAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
-/
lemma localInverse_mem_source (hf : IsLocalDiffeomorphAt I J n f x) :
    f x ∈ hf.localInverse.source := by
  rw [(hf.choose_spec.2 hf.choose_spec.1)]
  exact (Classical.choose hf).map_source hf.choose_spec.1
/-
**IsLocalDiffeomorphAt.localInverse_mem_target** 是 Mathlib 中的一个引理，位于命名空间 `IsLoca
lDiffeomorphAt`。
形式化陈述：localInverse_mem_target (hf : IsLocalDiffeomorphAt I J n f x) : x in hf.lo
calInverse.target
参数：hf : IsLocalDiffeomorphAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma localInverse_mem_target (hf : IsLocalDiffeomorphAt I J n f x) :
    x ∈ hf.localInverse.target :=
  hf.choose_spec.1
/-
**IsLocalDiffeomorphAt.contmdiffOn_localInverse** 是 Mathlib 中的一个引理，位于命名空间 `IsLoc
alDiffeomorphAt`。
形式化陈述：contmdiffOn_localInverse (hf : IsLocalDiffeomorphAt I J n f x) : CMDiff[hf
.localInverse.source] n hf.localInverse
参数：hf : IsLocalDiffeomorphAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialDiffeomorph.contMDiffOn_toFun`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
-/
lemma contmdiffOn_localInverse (hf : IsLocalDiffeomorphAt I J n f x) :
    CMDiff[hf.localInverse.source] n hf.localInverse :=
  hf.localInverse.contMDiffOn_toFun
/-
**IsLocalDiffeomorphAt.localInverse_right_inv** 是 Mathlib 中的一个引理，位于命名空间 `IsLocal
DiffeomorphAt`。
形式化陈述：localInverse_right_inv (hf : IsLocalDiffeomorphAt I J n f x) {y : N} (hy :
 y in hf.localInverse.source) : f (hf.localInverse y) = y
参数：hf : IsLocalDiffeomorphAt I J n f x；hy : y in hf.localInverse.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.symm_target`：symm_target : e.symm.target = e.source
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
-/
lemma localInverse_right_inv (hf : IsLocalDiffeomorphAt I J n f x) {y : N}
    (hy : y ∈ hf.localInverse.source) : f (hf.localInverse y) = y := by
  have : hf.localInverse y ∈ hf.choose.source := by
    rw [← hf.choose.symm_target]
    exact hf.choose.symm.map_source hy
  rw [hf.choose_spec.2 this]
  exact hf.choose.right_inv hy
/-
**IsLocalDiffeomorphAt.localInverse_eqOn_right** 是 Mathlib 中的一个引理，位于命名空间 `IsLoca
lDiffeomorphAt`。
形式化陈述：localInverse_eqOn_right (hf : IsLocalDiffeomorphAt I J n f x) : EqOn (f ∘ 
hf.localInverse) id hf.localInverse.source
参数：hf : IsLocalDiffeomorphAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalDiffeomorphAt.localInverse_right_inv`：localInverse_right_inv (hf 
: IsLocalDiffeomorphAt I J n f x) {y : N} (hy : y in hf.localInverse.source) : f
 (hf.localInverse y) = y
-/
lemma localInverse_eqOn_right (hf : IsLocalDiffeomorphAt I J n f x) :
    EqOn (f ∘ hf.localInverse) id hf.localInverse.source :=
  fun _y hy ↦ hf.localInverse_right_inv hy
/-
**IsLocalDiffeomorphAt.localInverse_eventuallyEq_right** 是 Mathlib 中的一个引理，位于命名空间
 `IsLocalDiffeomorphAt`。
形式化陈述：localInverse_eventuallyEq_right (hf : IsLocalDiffeomorphAt I J n f x) : f 
∘ hf.localInverse =ᶠ[nhds (f x)] id
参数：hf : IsLocalDiffeomorphAt I J n f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `PartialDiffeomorph.open_source`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用引理 `IsLocalDiffeomorphAt.localInverse_mem_source`：localInverse_mem_source (h
f : IsLocalDiffeomorphAt I J n f x) : f x in hf.localInverse.source
· 使用引理 `IsLocalDiffeomorphAt.localInverse_eqOn_right`：localInverse_eqOn_right (h
f : IsLocalDiffeomorphAt I J n f x) : EqOn (f ∘ hf.localInverse) id hf.localInve
rse.source
-/
lemma localInverse_eventuallyEq_right (hf : IsLocalDiffeomorphAt I J n f x) :
    f ∘ hf.localInverse =ᶠ[nhds (f x)] id :=
  Filter.eventuallyEq_of_mem
    (hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source)
    hf.localInverse_eqOn_right
/-
**IsLocalDiffeomorphAt.localInverse_left_inv** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalD
iffeomorphAt`。
形式化陈述：localInverse_left_inv (hf : IsLocalDiffeomorphAt I J n f x) {x' : M} (hx' 
: x' in hf.localInverse.target) : hf.localInverse (f x') = x'
参数：hf : IsLocalDiffeomorphAt I J n f x；hx' : x' in hf.localInverse.target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `PartialEquiv.symm_target`：symm_target : e.symm.target = e.source
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
-/
lemma localInverse_left_inv (hf : IsLocalDiffeomorphAt I J n f x) {x' : M}
    (hx' : x' ∈ hf.localInverse.target) : hf.localInverse (f x') = x' := by
  rw [hf.choose_spec.2 (hf.choose.symm_target ▸ hx')]
  exact hf.choose.left_inv hx'
/-
**IsLocalDiffeomorphAt.localInverse_eqOn_left** 是 Mathlib 中的一个引理，位于命名空间 `IsLocal
DiffeomorphAt`。
形式化陈述：localInverse_eqOn_left (hf : IsLocalDiffeomorphAt I J n f x) : EqOn (hf.lo
calInverse ∘ f) id hf.localInverse.target
参数：hf : IsLocalDiffeomorphAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalDiffeomorphAt.localInverse_left_inv`：localInverse_left_inv (hf : 
IsLocalDiffeomorphAt I J n f x) {x' : M} (hx' : x' in hf.localInverse.target) : 
hf.localInverse (f x') = x'
-/
lemma localInverse_eqOn_left (hf : IsLocalDiffeomorphAt I J n f x) :
    EqOn (hf.localInverse ∘ f) id hf.localInverse.target :=
  fun _ hx ↦ hf.localInverse_left_inv hx
/-
**IsLocalDiffeomorphAt.localInverse_eventuallyEq_left** 是 Mathlib 中的一个引理，位于命名空间 
`IsLocalDiffeomorphAt`。
形式化陈述：localInverse_eventuallyEq_left (hf : IsLocalDiffeomorphAt I J n f x) : hf.
localInverse ∘ f =ᶠ[nhds x] id
参数：hf : IsLocalDiffeomorphAt I J n f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `PartialDiffeomorph.open_target`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用引理 `IsLocalDiffeomorphAt.localInverse_mem_target`：localInverse_mem_target (h
f : IsLocalDiffeomorphAt I J n f x) : x in hf.localInverse.target
· 使用引理 `IsLocalDiffeomorphAt.localInverse_eqOn_left`：localInverse_eqOn_left (hf 
: IsLocalDiffeomorphAt I J n f x) : EqOn (hf.localInverse ∘ f) id hf.localInvers
e.target
-/
lemma localInverse_eventuallyEq_left (hf : IsLocalDiffeomorphAt I J n f x) :
    hf.localInverse ∘ f =ᶠ[nhds x] id :=
  Filter.eventuallyEq_of_mem
    (hf.localInverse.open_target.mem_nhds hf.localInverse_mem_target) hf.localInverse_eqOn_left
/-
**IsLocalDiffeomorphAt.localInverse_isLocalDiffeomorphAt** 是 Mathlib 中的一个引理，位于命名
空间 `IsLocalDiffeomorphAt`。
形式化陈述：localInverse_isLocalDiffeomorphAt (hf : IsLocalDiffeomorphAt I J n f x) : 
IsLocalDiffeomorphAt J I n (hf.localInverse) (f x)
参数：hf : IsLocalDiffeomorphAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PartialDiffeomorph.isLocalDiffeomorphAt`：PartialDiffeomorph.isLocalDiffe
omorphAt (φ : PartialDiffeomorph I J M N n) {x : M} (hx : x in φ.source) : IsLoc
alDiffeomorphAt I J n φ x
· 使用引理 `IsLocalDiffeomorphAt.localInverse_mem_source`：localInverse_mem_source (h
f : IsLocalDiffeomorphAt I J n f x) : f x in hf.localInverse.source
-/
lemma localInverse_isLocalDiffeomorphAt (hf : IsLocalDiffeomorphAt I J n f x) :
    IsLocalDiffeomorphAt J I n (hf.localInverse) (f x) :=
  hf.localInverse.isLocalDiffeomorphAt _ _ _ hf.localInverse_mem_source
/-
**IsLocalDiffeomorphAt.localInverse_contMDiffOn** 是 Mathlib 中的一个引理，位于命名空间 `IsLoc
alDiffeomorphAt`。
形式化陈述：localInverse_contMDiffOn (hf : IsLocalDiffeomorphAt I J n f x) : CMDiff[hf
.localInverse.source] n hf.localInverse
参数：hf : IsLocalDiffeomorphAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialDiffeomorph.contMDiffOn_toFun`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
-/
lemma localInverse_contMDiffOn (hf : IsLocalDiffeomorphAt I J n f x) :
    CMDiff[hf.localInverse.source] n hf.localInverse :=
  hf.localInverse.contMDiffOn_toFun
/-
**IsLocalDiffeomorphAt.localInverse_contMDiffAt** 是 Mathlib 中的一个引理，位于命名空间 `IsLoc
alDiffeomorphAt`。
形式化陈述：localInverse_contMDiffAt (hf : IsLocalDiffeomorphAt I J n f x) : CMDiffAt 
n hf.localInverse (f x)
参数：hf : IsLocalDiffeomorphAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用引理 `IsLocalDiffeomorphAt.localInverse_contMDiffOn`：localInverse_contMDiffOn 
(hf : IsLocalDiffeomorphAt I J n f x) : CMDiff[hf.localInverse.source] n hf.loca
lInverse
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `PartialDiffeomorph.open_source`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用引理 `IsLocalDiffeomorphAt.localInverse_mem_source`：localInverse_mem_source (h
f : IsLocalDiffeomorphAt I J n f x) : f x in hf.localInverse.source
-/
lemma localInverse_contMDiffAt (hf : IsLocalDiffeomorphAt I J n f x) :
    CMDiffAt n hf.localInverse (f x) :=
  hf.localInverse_contMDiffOn.contMDiffAt
    (hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source)
/-
**IsLocalDiffeomorphAt.localInverse_mdifferentiableAt** 是 Mathlib 中的一个引理，位于命名空间 
`IsLocalDiffeomorphAt`。
形式化陈述：localInverse_mdifferentiableAt (hf : IsLocalDiffeomorphAt I J n f x) (hn :
 n != 0) : MDiffAt hf.localInverse (f x)
参数：hf : IsLocalDiffeomorphAt I J n f x；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用引理 `IsLocalDiffeomorphAt.localInverse_contMDiffAt`：localInverse_contMDiffAt 
(hf : IsLocalDiffeomorphAt I J n f x) : CMDiffAt n hf.localInverse (f x)
-/
lemma localInverse_mdifferentiableAt (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    MDiffAt hf.localInverse (f x) :=
  hf.localInverse_contMDiffAt.mdifferentiableAt hn
/-
**IsLocalDiffeomorphAt.comp** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalDiffeomorphAt`。
形式化陈述：comp (hf : IsLocalDiffeomorphAt I J n f x) {g : N -> P} (hg : IsLocalDiffe
omorphAt J K n g (f x)) : IsLocalDiffeomorphAt I K n (g ∘ f) x
参数：hf : IsLocalDiffeomorphAt I J n f x；hg : IsLocalDiffeomorphAt J K n g (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialDiffeomorph.trans_toPartialEquiv`：∀ {𝕜 : Type u_1} [inst : Nontri
viallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : 
NormedSpace 𝕜 E] {F : Type u_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartial
Equiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_
1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.EqOn.eq_of_mem`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ :
 α → β} {a : α}, Set.EqOn f₁ f₂ s → a ∈ s → f₁ a = f₂ a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp (hf : IsLocalDiffeomorphAt I J n f x) {g : N → P}
    (hg : IsLocalDiffeomorphAt J K n g (f x)) :
    IsLocalDiffeomorphAt I K n (g ∘ f) x := by
  obtain ⟨Φ, hx, heq⟩ := hf
  obtain ⟨Ψ, hy, heq'⟩ := hg
  refine ⟨Φ.trans Ψ, by simp [hx, ← heq.eq_of_mem hx, hy], ?_⟩
  intro y ⟨hyl, hyr⟩
  have hfy : f y ∈ Ψ.source := by rwa [heq.eq_of_mem hyl]
  simp [← heq.eq_of_mem hyl, ← heq'.eq_of_mem hfy]

end IsLocalDiffeomorphAt

/-- `f : M → N` is called a **`C^n` local diffeomorphism on `s`** iff it is a local diffeomorphism
at each `x : s`. -/
/-
**IsLocalDiffeomorphOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {F : Type u_3} →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace 𝕜 F] →                 {H₁ : Type u_5} →           
        [inst_5 : TopologicalSpace H₁] →                     {H₂ : Type u_6} →  
                     [inst_6 : TopologicalSpace H₂] →                         Mo
delWithCorners 𝕜 E H₁ →                           ModelWithCorners 𝕜 F H₂ →     
                        {M : Type u_8} →                               [inst : T
opologicalSpace M] →                                 [ChartedSpace H₁ M] →      
                             {N : Type u_9} →                                   
  [inst : TopologicalSpace N] →                                       [ChartedSp
ace H₂ N] → WithTop ℕ∞ → (M → N) → Set M → Prop
参数：M → N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : M → N` is called a **`C^n` local diffeomorphism on `s`** iff it is a local 
diffeomorphism
at each `x : s`.
-/
@[expose] def IsLocalDiffeomorphOn (f : M → N) (s : Set M) : Prop :=
  ∀ x : s, IsLocalDiffeomorphAt I J n f x

/-- `f : M → N` is a **`C^n` local diffeomorphism** iff it is a local diffeomorphism
at each `x ∈ M`. -/
/-
**IsLocalDiffeomorph** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {F : Type u_3} →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace 𝕜 F] →                 {H₁ : Type u_5} →           
        [inst_5 : TopologicalSpace H₁] →                     {H₂ : Type u_6} →  
                     [inst_6 : TopologicalSpace H₂] →                         Mo
delWithCorners 𝕜 E H₁ →                           ModelWithCorners 𝕜 F H₂ →     
                        {M : Type u_8} →                               [inst : T
opologicalSpace M] →                                 [ChartedSpace H₁ M] →      
                             {N : Type u_9} →                                   
  [inst : TopologicalSpace N] → [ChartedSpace H₂ N] → WithTop ℕ∞ → (M → N) → Pro
p
参数：M → N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : M → N` is a **`C^n` local diffeomorphism** iff it is a local diffeomorphism
at each `x ∈ M`.
-/
@[expose] def IsLocalDiffeomorph (f : M → N) : Prop :=
  ∀ x : M, IsLocalDiffeomorphAt I J n f x

variable {I J n} in
/-
**isLocalDiffeomorphOn_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalDiffeomorphOn_iff {f : M -> N} (s : Set M) : IsLocalDiffeomorphOn I
 J n f s ↔ forall x : s, IsLocalDiffeomorphAt I J n f x
参数：s : Set M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLocalDiffeomorphOn_iff {f : M → N} (s : Set M) :
    IsLocalDiffeomorphOn I J n f s ↔ ∀ x : s, IsLocalDiffeomorphAt I J n f x := by rfl

variable {I J n} in
/-
**isLocalDiffeomorph_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalDiffeomorph_iff {f : M -> N} : IsLocalDiffeomorph I J n f ↔ forall 
x : M, IsLocalDiffeomorphAt I J n f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLocalDiffeomorph_iff {f : M → N} :
    IsLocalDiffeomorph I J n f ↔ ∀ x : M, IsLocalDiffeomorphAt I J n f x := by rfl

variable {I J n} in
/-
**isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ {f : M -> N} : IsLocalDif
feomorph I J n f ↔ IsLocalDiffeomorphOn I J n f Set.univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ {f : M → N} :
    IsLocalDiffeomorph I J n f ↔ IsLocalDiffeomorphOn I J n f Set.univ :=
  ⟨fun hf x ↦ hf x, fun hf x ↦ hf ⟨x, trivial⟩⟩

variable {I J n} in
/-
**IsLocalDiffeomorph.isLocalDiffeomorphOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorph.isLocalDiffeomorphOn {f : M -> N} (hf : IsLocalDiffeomo
rph I J n f) (s : Set M) : IsLocalDiffeomorphOn I J n f s
参数：hf : IsLocalDiffeomorph I J n f；s : Set M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsLocalDiffeomorph.isLocalDiffeomorphOn
    {f : M → N} (hf : IsLocalDiffeomorph I J n f) (s : Set M) : IsLocalDiffeomorphOn I J n f s :=
  fun x ↦ hf x

/-! ### Basic properties of local diffeomorphisms -/
section Basic
variable {f : M → N} {s : Set M} {x : M}
variable {I J n}

/-- A `C^n` local diffeomorphism at `x` is `C^n` differentiable at `x`. -/
/-
**IsLocalDiffeomorphAt.contMDiffAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorphAt.contMDiffAt (hf : IsLocalDiffeomorphAt I J n f x) : C
MDiffAt n f x
参数：hf : IsLocalDiffeomorphAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `PartialDiffeomorph.contMDiffOn_toFun`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `PartialDiffeomorph.open_source`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A `C^n` local diffeomorphism at `x` is `C^n` differentiable at `x`.
-/
lemma IsLocalDiffeomorphAt.contMDiffAt (hf : IsLocalDiffeomorphAt I J n f x) :
    CMDiffAt n f x := by
  choose Φ hx heq using hf
  -- In fact, even `CMDiff[Φ.source] n f`.
  exact ((Φ.contMDiffOn_toFun).congr heq).contMDiffAt (Φ.open_source.mem_nhds hx)

/-- A local diffeomorphism at `x` is differentiable at `x`. -/
/-
**IsLocalDiffeomorphAt.mdifferentiableAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorphAt.mdifferentiableAt (hf : IsLocalDiffeomorphAt I J n f 
x) (hn : n != 0) : MDiffAt f x
参数：hf : IsLocalDiffeomorphAt I J n f x；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用引理 `IsLocalDiffeomorphAt.contMDiffAt`：IsLocalDiffeomorphAt.contMDiffAt (hf :
 IsLocalDiffeomorphAt I J n f x) : CMDiffAt n f x

--- 原说明 ---
A local diffeomorphism at `x` is differentiable at `x`.
-/
lemma IsLocalDiffeomorphAt.mdifferentiableAt (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    MDiffAt f x :=
  hf.contMDiffAt.mdifferentiableAt hn

/-- A `C^n` local diffeomorphism on `s` is `C^n` on `s`. -/
/-
**IsLocalDiffeomorphOn.contMDiffOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorphOn.contMDiffOn (hf : IsLocalDiffeomorphOn I J n f s) : C
MDiff[s] n f
参数：hf : IsLocalDiffeomorphOn I J n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用引理 `IsLocalDiffeomorphAt.contMDiffAt`：IsLocalDiffeomorphAt.contMDiffAt (hf :
 IsLocalDiffeomorphAt I J n f x) : CMDiffAt n f x

--- 原说明 ---
A `C^n` local diffeomorphism on `s` is `C^n` on `s`.
-/
lemma IsLocalDiffeomorphOn.contMDiffOn (hf : IsLocalDiffeomorphOn I J n f s) :
    CMDiff[s] n f :=
  fun x hx ↦ (hf ⟨x, hx⟩).contMDiffAt.contMDiffWithinAt

/-- A local diffeomorphism on `s` is differentiable on `s`. -/
/-
**IsLocalDiffeomorphOn.mdifferentiableOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorphOn.mdifferentiableOn (hf : IsLocalDiffeomorphOn I J n f 
s) (hn : n != 0) : MDiff[s] f
参数：hf : IsLocalDiffeomorphOn I J n f s；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.mdifferentiableOn`：ContMDiffOn.mdifferentiableOn (hf : CMDif
f[s] n f) (hn : n != 0) : MDiff[s] f
· 使用引理 `IsLocalDiffeomorphOn.contMDiffOn`：IsLocalDiffeomorphOn.contMDiffOn (hf :
 IsLocalDiffeomorphOn I J n f s) : CMDiff[s] n f

--- 原说明 ---
A local diffeomorphism on `s` is differentiable on `s`.
-/
lemma IsLocalDiffeomorphOn.mdifferentiableOn (hf : IsLocalDiffeomorphOn I J n f s) (hn : n ≠ 0) :
    MDiff[s] f :=
  hf.contMDiffOn.mdifferentiableOn hn

/-- A `C^n` local diffeomorphism is `C^n`. -/
/-
**IsLocalDiffeomorph.contMDiff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorph.contMDiff (hf : IsLocalDiffeomorph I J n f) : CMDiff n 
f
参数：hf : IsLocalDiffeomorph I J n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalDiffeomorphAt.contMDiffAt`：IsLocalDiffeomorphAt.contMDiffAt (hf :
 IsLocalDiffeomorphAt I J n f x) : CMDiffAt n f x

--- 原说明 ---
A `C^n` local diffeomorphism is `C^n`.
-/
lemma IsLocalDiffeomorph.contMDiff (hf : IsLocalDiffeomorph I J n f) : CMDiff n f :=
  fun x ↦ (hf x).contMDiffAt

/-- A `C^n` local diffeomorphism is differentiable. -/
/-
**IsLocalDiffeomorph.mdifferentiable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorph.mdifferentiable (hf : IsLocalDiffeomorph I J n f) (hn :
 n != 0) : MDiff f
参数：hf : IsLocalDiffeomorph I J n f；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalDiffeomorphAt.mdifferentiableAt`：IsLocalDiffeomorphAt.mdifferenti
ableAt (hf : IsLocalDiffeomorphAt I J n f x) (hn : n != 0) : MDiffAt f x

--- 原说明 ---
A `C^n` local diffeomorphism is differentiable.
-/
lemma IsLocalDiffeomorph.mdifferentiable (hf : IsLocalDiffeomorph I J n f) (hn : n ≠ 0) :
    MDiff f :=
  fun x ↦ (hf x).mdifferentiableAt hn

/-- A `C^n` diffeomorphism is a local diffeomorphism. -/
/-
**Diffeomorph.isLocalDiffeomorph** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ^n⟮I, J⟯ N) : IsLocalDiffeomorph I
 J n Φ
参数：Φ : M ≃ₘ^n⟮I, J⟯ N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eqOn_refl`：eqOn_refl (f : α -> β) (s : Set α) : EqOn f f s

--- 原说明 ---
A `C^n` diffeomorphism is a local diffeomorphism.
-/
lemma Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ^n⟮I, J⟯ N) : IsLocalDiffeomorph I J n Φ :=
  fun _x ↦ ⟨Φ.toPartialDiffeomorph, by trivial, eqOn_refl Φ _⟩

-- FUTURE: if useful, also add "a `PartialDiffeomorph` is a local diffeomorphism on its source"

/-- A local diffeomorphism on `s` is a local homeomorphism on `s`. -/
/-
**IsLocalDiffeomorphOn.isLocalHomeomorphOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorphOn.isLocalHomeomorphOn {s : Set M} (hf : IsLocalDiffeomo
rphOn I J n f s) : IsLocalHomeomorphOn f s
参数：hf : IsLocalDiffeomorphOn I J n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHomeomorphOn.mk`：mk (h : forall x in s, exists e : OpenPartialHom
eomorph X Y, x in e.source ∧ Set.EqOn f e e.source) : IsLocalHomeomorphOn f s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A local diffeomorphism on `s` is a local homeomorphism on `s`.
-/
theorem IsLocalDiffeomorphOn.isLocalHomeomorphOn {s : Set M} (hf : IsLocalDiffeomorphOn I J n f s) :
    IsLocalHomeomorphOn f s := by
  apply IsLocalHomeomorphOn.mk
  intro x hx
  choose U hyp using hf ⟨x, hx⟩
  exact ⟨U.toOpenPartialHomeomorph, hyp⟩

/-- A local diffeomorphism is a local homeomorphism. -/
/-
**IsLocalDiffeomorph.isLocalHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorph.isLocalHomeomorph (hf : IsLocalDiffeomorph I J n f) : I
sLocalHomeomorph f
参数：hf : IsLocalDiffeomorph I J n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isLocalHomeomorph_iff_isLocalHomeomorphOn_univ`：isLocalHomeomorph_iff_is
LocalHomeomorphOn_univ : IsLocalHomeomorph f ↔ IsLocalHomeomorphOn f Set.univ
· 使用定理 `IsLocalDiffeomorphOn.isLocalHomeomorphOn`：IsLocalDiffeomorphOn.isLocalHo
meomorphOn {s : Set M} (hf : IsLocalDiffeomorphOn I J n f s) : IsLocalHomeomorph
On f s
· 使用定理 `isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ`：isLocalDiffeomorph_iff
_isLocalDiffeomorphOn_univ {f : M -> N} : IsLocalDiffeomorph I J n f ↔ IsLocalDi
ffeomorphOn I J n f Set.univ

--- 原说明 ---
A local diffeomorphism is a local homeomorphism.
-/
theorem IsLocalDiffeomorph.isLocalHomeomorph (hf : IsLocalDiffeomorph I J n f) :
    IsLocalHomeomorph f := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  rw [isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ] at hf
  exact hf.isLocalHomeomorphOn

/-- A local diffeomorphism is an open map. -/
/-
**IsLocalDiffeomorph.isOpenMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorph.isOpenMap (hf : IsLocalDiffeomorph I J n f) : IsOpenMap
 f
参数：hf : IsLocalDiffeomorph I J n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHomeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsLocalHomeomorph 
f → IsOpenMap f
· 使用定理 `IsLocalDiffeomorph.isLocalHomeomorph`：IsLocalDiffeomorph.isLocalHomeomor
ph (hf : IsLocalDiffeomorph I J n f) : IsLocalHomeomorph f

--- 原说明 ---
A local diffeomorphism is an open map.
-/
lemma IsLocalDiffeomorph.isOpenMap (hf : IsLocalDiffeomorph I J n f) : IsOpenMap f :=
  (hf.isLocalHomeomorph).isOpenMap

/-- A local diffeomorphism has open range. -/
/-
**IsLocalDiffeomorph.isOpen_range** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorph.isOpen_range (hf : IsLocalDiffeomorph I J n f) : IsOpen
 (range f)
参数：hf : IsLocalDiffeomorph I J n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → IsOpen (S
et.range f)
· 使用引理 `IsLocalDiffeomorph.isOpenMap`：IsLocalDiffeomorph.isOpenMap (hf : IsLocal
Diffeomorph I J n f) : IsOpenMap f

--- 原说明 ---
A local diffeomorphism has open range.
-/
lemma IsLocalDiffeomorph.isOpen_range (hf : IsLocalDiffeomorph I J n f) : IsOpen (range f) :=
  (hf.isOpenMap).isOpen_range

/-- The image of a local diffeomorphism is open. -/
/-
**IsLocalDiffeomorph.image** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalDiffeomorph`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {F : Type u_3} →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace 𝕜 F] →                 {H₁ : Type u_5} →           
        [inst_5 : TopologicalSpace H₁] →                     {H₂ : Type u_6} →  
                     [inst_6 : TopologicalSpace H₂] →                         {I
 : ModelWithCorners 𝕜 E H₁} →                           {J : ModelWithCorners 𝕜 
F H₂} →                             {M : Type u_8} →                            
   [inst_7 : TopologicalSpace M] →                                 [inst_8 : Cha
rtedSpace H₁ M] →                                   {N : Type u_9} →            
                         [inst_9 : TopologicalSpace N] →                        
               [inst_10 : ChartedSpace H₂ N] →                                  
       {n : WithTop ℕ∞} →                                           {f : M → N} 
→ IsLocalDiffeomorph I J n f → TopologicalSpace.Opens N
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalDiffeomorph.isOpen_range`：IsLocalDiffeomorph.isOpen_range (hf : I
sLocalDiffeomorph I J n f) : IsOpen (range f)

--- 原说明 ---
The image of a local diffeomorphism is open.
-/
@[expose] def IsLocalDiffeomorph.image (hf : IsLocalDiffeomorph I J n f) : Opens N :=
  ⟨range f, hf.isOpen_range⟩
/-
**IsLocalDiffeomorph.image_coe** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorph.image_coe (hf : IsLocalDiffeomorph I J n f) : hf.image.
1 = range f
参数：hf : IsLocalDiffeomorph I J n f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsLocalDiffeomorph.image_coe (hf : IsLocalDiffeomorph I J n f) : hf.image.1 = range f :=
  rfl

-- TODO: this result holds more generally for (local) structomorphisms
-- This argument implies a `LocalDiffeomorphOn f s` for `s` open is a `PartialDiffeomorph`

/-- A bijective local diffeomorphism is a diffeomorphism. -/
/-
**IsLocalDiffeomorph.diffeomorphOfBijective** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocalDiffeomorph.diffeomorphOfBijective (hf : IsLocalDiffeomorph I J n f
) (hf' : Function.Bijective f) : Diffeomorph I J M N n
参数：hf : IsLocalDiffeomorph I J n f；hf' : Function.Bijective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalDiffeomorph.contMDiff`：IsLocalDiffeomorph.contMDiff (hf : IsLocal
Diffeomorph I J n f) : CMDiff n f

--- 原说明 ---
A bijective local diffeomorphism is a diffeomorphism.
-/
def IsLocalDiffeomorph.diffeomorphOfBijective
    (hf : IsLocalDiffeomorph I J n f) (hf' : Function.Bijective f) : Diffeomorph I J M N n := by
  -- Choose a right inverse `g` of `f`.
  choose g hgInverse using (Function.bijective_iff_has_inverse).mp hf'
  -- Choose diffeomorphisms φ_x which coincide with `f` near `x`.
  choose Φ hyp using (fun x ↦ hf x)
  -- Two such diffeomorphisms (and their inverses!) coincide on their sources:
  -- they're both inverses to g. In fact, the latter suffices for our proof.
  -- have (x y) : EqOn (Φ x).symm (Φ y).symm ((Φ x).target ∩ (Φ y).target) := sorry
  have aux (x) : EqOn g (Φ x).symm (Φ x).target :=
    eqOn_of_leftInvOn_of_rightInvOn (fun x' _ ↦ hgInverse.1 x')
      (LeftInvOn.congr_left ((Φ x).toOpenPartialHomeomorph).rightInvOn
        ((Φ x).toOpenPartialHomeomorph).mapsTo_symm (hyp x).2.symm)
      (fun _y hy ↦ (Φ x).map_target hy)
  exact {
    toFun := f
    invFun := g
    left_inv := hgInverse.1
    right_inv := hgInverse.2
    contMDiff_toFun := hf.contMDiff
    contMDiff_invFun := by
      intro y
      let x := g y
      obtain ⟨hx, hfx⟩ := hyp x
      apply ((Φ x).symm.contMDiffOn.congr (aux x)).contMDiffAt (((Φ x).open_target).mem_nhds ?_)
      have : y = (Φ x) x := ((hgInverse.2 y).congr (hfx hx)).mp rfl
      exact this ▸ (Φ x).map_source hx }

end Basic

section Differential

variable {f : M → N} {s : Set M} {x : M}

variable {I I' J n}

set_option backward.isDefEq.respectTransparency false in
/-- If `f` is a `C^n` local diffeomorphism at `x`, for `n ≠ 0`, the differential `df_x`
is a linear equivalence. -/
/-
**IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 
`IsLocalDiffeomorphAt`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {F : Type u_3} →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace 𝕜 F] →                 {H₁ : Type u_5} →           
        [inst_5 : TopologicalSpace H₁] →                     {H₂ : Type u_6} →  
                     [inst_6 : TopologicalSpace H₂] →                         {I
 : ModelWithCorners 𝕜 E H₁} →                           {J : ModelWithCorners 𝕜 
F H₂} →                             {M : Type u_8} →                            
   [inst_7 : TopologicalSpace M] →                                 [inst_8 : Cha
rtedSpace H₁ M] →                                   {N : Type u_9} →            
                         [inst_9 : TopologicalSpace N] →                        
               [inst_10 : ChartedSpace H₂ N] →                                  
       {n : WithTop ℕ∞} →                                           {f : M → N} 
→                                             {x : M} →                         
                      IsLocalDiffeomorphAt I J n f x →                          
                       n ≠ 0 → TangentSpace I x ≃L[𝕜] TangentSpace J (f x)
参数：f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a `C^n` local diffeomorphism at `x`, for `n ≠ 0`, the differential `df
_x`
is a linear equivalence.
-/
@[expose] def IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    TangentSpace I x ≃L[𝕜] TangentSpace J (f x) where
  toFun := mfderiv% f x
  invFun := mfderiv% hf.localInverse (f x)
  left_inv := by
    apply ContinuousLinearMap.leftInverse_of_comp
    rw [← mfderiv_id, ← hf.localInverse_eventuallyEq_left.mfderiv_eq]
    exact (mfderiv_comp _ (hf.localInverse_mdifferentiableAt hn) (hf.mdifferentiableAt hn)).symm
  right_inv := by
    apply ContinuousLinearMap.rightInverse_of_comp
    rw [← mfderiv_id, ← hf.localInverse_eventuallyEq_right.mfderiv_eq]
    -- We need to rewrite the base point hf.localInverse (f x) = x twice,
    -- in the differentiability hypothesis and for applying the chain rule.
    have hf' : MDifferentiableAt I J f (hf.localInverse (f x)) := by
      rw [hf.localInverse_left_inv hf.localInverse_mem_target]
      exact hf.mdifferentiableAt hn
    rw [mfderiv_comp _ hf' (hf.localInverse_mdifferentiableAt hn),
      hf.localInverse_left_inv hf.localInverse_mem_target]
  continuous_toFun := (mfderiv% f x).cont
  continuous_invFun := (mfderiv% hf.localInverse (f x)).cont
  map_add' := fun x_1 y ↦ map_add _ x_1 y
  map_smul' := by intros; simp

@[simp, mfld_simps]
/-
**IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe (hf : IsLocalDiffe
omorphAt I J n f x) (hn : n != 0) : hf.mfderivToContinuousLinearEquiv hn = mfder
iv% f x
参数：hf : IsLocalDiffeomorphAt I J n f x；hn : n != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    hf.mfderivToContinuousLinearEquiv hn = mfderiv% f x := rfl

/-- Each differential of a `C^n` diffeomorphism of Banach manifolds (`n ≠ 0`)
is a linear equivalence. -/
/-
**Diffeomorph.mfderivToContinuousLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Diffeomorph.mfderivToContinuousLinearEquiv (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n !=
 0) (x : M) : TangentSpace I x ≃L[𝕜] TangentSpace J (Φ x)
参数：Φ : M ≃ₘ^n⟮I, J⟯ N；hn : n != 0；x : M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Diffeomorph.isLocalDiffeomorph`：Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ
^n⟮I, J⟯ N) : IsLocalDiffeomorph I J n Φ

--- 原说明 ---
Each differential of a `C^n` diffeomorphism of Banach manifolds (`n ≠ 0`)
is a linear equivalence.
-/
def Diffeomorph.mfderivToContinuousLinearEquiv
    (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (x : M) :
    TangentSpace I x ≃L[𝕜] TangentSpace J (Φ x) :=
  (Φ.isLocalDiffeomorph x).mfderivToContinuousLinearEquiv hn
/-
**Diffeomorph.mfderivToContinuousLinearEquiv_coe** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : 
n != 0) : Φ.mfderivToContinuousLinearEquiv hn x = mfderiv% Φ x
参数：Φ : M ≃ₘ^n⟮I, J⟯ N；hn : n != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) :
    Φ.mfderivToContinuousLinearEquiv hn x = mfderiv% Φ x := by rfl

/-- If `f` is a `C^n` local diffeomorphism of Banach manifolds (`n ≠ 0`),
each differential is a linear equivalence. -/
/-
**IsLocalDiffeomorph.mfderivToContinuousLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``
。
形式化陈述：IsLocalDiffeomorph.mfderivToContinuousLinearEquiv (hf : IsLocalDiffeomorph
 I J n f) (hn : n != 0) (x : M) : TangentSpace I x ≃L[𝕜] TangentSpace J (f x)
参数：hf : IsLocalDiffeomorph I J n f；hn : n != 0；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a `C^n` local diffeomorphism of Banach manifolds (`n ≠ 0`),
each differential is a linear equivalence.
-/
def IsLocalDiffeomorph.mfderivToContinuousLinearEquiv
    (hf : IsLocalDiffeomorph I J n f) (hn : n ≠ 0) (x : M) :
    TangentSpace I x ≃L[𝕜] TangentSpace J (f x) :=
  (hf x).mfderivToContinuousLinearEquiv hn
/-
**IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe (hf : IsLocalDiffeom
orph I J n f) (hn : n != 0) (x : M) : hf.mfderivToContinuousLinearEquiv hn x = m
fderiv% f x
参数：hf : IsLocalDiffeomorph I J n f；hn : n != 0；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe`：IsLocalDiffeomo
rphAt.mfderivToContinuousLinearEquiv_coe (hf : IsLocalDiffeomorphAt I J n f x) (
hn : n != 0) : hf.mfderivToContinuousLinearEq…
-/
lemma IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (hf : IsLocalDiffeomorph I J n f) (hn : n ≠ 0) (x : M) :
    hf.mfderivToContinuousLinearEquiv hn x = mfderiv% f x :=
  (hf x).mfderivToContinuousLinearEquiv_coe hn

end Differential

