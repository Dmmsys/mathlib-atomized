/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Algebra.UniformConvergence
public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Algebra-related equicontinuity criteria
-/

public section


open Function

open UniformConvergence

@[to_additive]
/-
**equicontinuous_of_equicontinuousAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuous_of_equicontinuousAt_one {ι G M hom : Type*} [TopologicalSpa
ce G] [UniformSpace M] [Group G] [Group M] [IsTopologicalGroup G] [IsUniformGrou
p M] [FunLike hom G M] [MonoidHomClass hom G M] (F : ι -> hom) (hf : Equicontinu
ousAt ((↑) ∘ F) (1 : G)) : Equicontinuous ((↑) ∘ F)
参数：F : ι -> hom；hf : EquicontinuousAt ((↑) ∘ F) (1 : G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `equicontinuous_iff_continuous`：equicontinuous_iff_continuous {F : ι -> X
 -> α} : Equicontinuous F ↔ Continuous (ofFun ∘ Function.swap F : X -> ι ->ᵤ α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `continuous_of_continuousAt_one`：continuous_of_continuousAt_one {M hom : 
Type*} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] [FunLike hom G M] 
[MonoidHomClass hom …
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用定理 `instIsUniformGroupUniformFun`：∀ {α : Type u_1} {G : Type u_2} [inst : Gr
oup G] [inst_1 : UniformSpace G] [IsUniformGroup G],   IsUniformGroup (UniformFu
n α G)
· 使用定理 `equicontinuousAt_iff_continuousAt`：equicontinuousAt_iff_continuousAt {F 
: ι -> X -> α} {x₀ : X} : EquicontinuousAt F x₀ ↔ ContinuousAt (ofFun ∘ Function
.swap F : X -> ι ->ᵤ α)…
-/
theorem equicontinuous_of_equicontinuousAt_one {ι G M hom : Type*} [TopologicalSpace G]
    [UniformSpace M] [Group G] [Group M] [IsTopologicalGroup G] [IsUniformGroup M]
    [FunLike hom G M] [MonoidHomClass hom G M] (F : ι → hom)
    (hf : EquicontinuousAt ((↑) ∘ F) (1 : G)) :
    Equicontinuous ((↑) ∘ F) := by
  rw [equicontinuous_iff_continuous]
  rw [equicontinuousAt_iff_continuousAt] at hf
  let φ : G →* (ι →ᵤ M) :=
    { toFun := swap ((↑) ∘ F)
      map_one' := by dsimp [UniformFun]; ext; exact map_one _
      map_mul' := fun a b => by dsimp [UniformFun]; ext; exact map_mul _ _ _ }
  exact continuous_of_continuousAt_one φ hf

@[to_additive]
/-
**uniformEquicontinuous_of_equicontinuousAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformEquicontinuous_of_equicontinuousAt_one {ι G M hom : Type*} [Uniform
Space G] [UniformSpace M] [Group G] [Group M] [IsUniformGroup G] [IsUniformGroup
 M] [FunLike hom G M] [MonoidHomClass hom G M] (F : ι -> hom) (hf : Equicontinuo
usAt ((↑) ∘ F) (1 : G)) : UniformEquicontinuous ((↑) ∘ F)
参数：F : ι -> hom；hf : EquicontinuousAt ((↑) ∘ F) (1 : G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformEquicontinuous_iff_uniformContinuous`：uniformEquicontinuous_iff_u
niformContinuous {F : ι -> β -> α} : UniformEquicontinuous F ↔ UniformContinuous
 (ofFun ∘ Function.swap F : β -> …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `uniformContinuous_of_continuousAt_one`：uniformContinuous_of_continuousAt
_one {hom : Type*} [UniformSpace β] [Group β] [IsUniformGroup β] [FunLike hom α 
β] [MonoidHomClass hom α β]…
· 使用定理 `instIsUniformGroupUniformFun`：∀ {α : Type u_1} {G : Type u_2} [inst : Gr
oup G] [inst_1 : UniformSpace G] [IsUniformGroup G],   IsUniformGroup (UniformFu
n α G)
· 使用定理 `equicontinuousAt_iff_continuousAt`：equicontinuousAt_iff_continuousAt {F 
: ι -> X -> α} {x₀ : X} : EquicontinuousAt F x₀ ↔ ContinuousAt (ofFun ∘ Function
.swap F : X -> ι ->ᵤ α)…
-/
theorem uniformEquicontinuous_of_equicontinuousAt_one {ι G M hom : Type*} [UniformSpace G]
    [UniformSpace M] [Group G] [Group M] [IsUniformGroup G] [IsUniformGroup M]
    [FunLike hom G M] [MonoidHomClass hom G M]
    (F : ι → hom) (hf : EquicontinuousAt ((↑) ∘ F) (1 : G)) :
    UniformEquicontinuous ((↑) ∘ F) := by
  rw [uniformEquicontinuous_iff_uniformContinuous]
  rw [equicontinuousAt_iff_continuousAt] at hf
  let φ : G →* (ι →ᵤ M) :=
    { toFun := swap ((↑) ∘ F)
      map_one' := by dsimp [UniformFun]; ext; exact map_one _
      map_mul' := fun a b => by dsimp [UniformFun]; ext; exact map_mul _ _ _ }
  exact uniformContinuous_of_continuousAt_one φ hf
