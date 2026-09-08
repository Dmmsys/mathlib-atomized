/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.CompactOpen

/-!
# Equivalence between `C(X, Σ i, Y i)` and `Σ i, C(X, Y i)`

If `X` is a connected topological space, then for every continuous map `f` from `X` to the disjoint
union of a collection of topological spaces `Y i` there exists a unique index `i` and a continuous
map from `g` to `Y i` such that `f` is the composition of the natural embedding
`Sigma.mk i : Y i → Σ i, Y i` with `g`.

This defines an equivalence between `C(X, Σ i, Y i)` and `Σ i, C(X, Y i)`. In fact, this equivalence
is a homeomorphism if the spaces of continuous maps are equipped with the compact-open topology.

## Implementation notes

There are two natural ways to talk about this result: one is to say that for each `f` there exist
unique `i` and `g`; another one is to define a noncomputable equivalence. We choose the second way
because it is easier to use an equivalence in applications.

## TODO

Some results in this file can be generalized to the case when `X` is a preconnected space. However,
if `X` is empty, then any index `i` will work, so there is no 1-to-1 correspondence.

## Keywords

continuous map, sigma type, disjoint union
-/

@[expose] public section

noncomputable section

open Filter Topology

variable {X ι : Type*} {Y : ι → Type*} [TopologicalSpace X] [∀ i, TopologicalSpace (Y i)]

namespace ContinuousMap

/-
**ContinuousMap.isEmbedding_sigmaMk_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMa
p`。
形式化陈述：isEmbedding_sigmaMk_comp [Nonempty X] : IsEmbedding (fun g : Σ i, C(X, Y i
) => (sigmaMk g.1).comp g.2) where toIsInducing
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inducing_sigma`：inducing_sigma {f : Sigma σ -> X} : IsInducing f ↔ (fora
ll i, IsInducing (f ∘ Sigma.mk i)) ∧ (forall i, exists U, IsOpen U ∧ forall x, f
 x i…
· 使用定理 `ContinuousMap.isInducing_postcomp`：isInducing_postcomp (g : C(Y, Z)) (hg
 : IsInducing g) : IsInducing (g.comp : C(X, Y) -> C(X, Z)) where eq_induced
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用引理 `Topology.IsEmbedding.sigmaMk`：Topology.IsEmbedding.sigmaMk {i : ι} : IsE
mbedding (@Sigma.mk ι σ i)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ContinuousEvalConst.continuous_eval_const`：∀ {F : Type u_1} {α : outPara
m (Type u_2)} {X : outParam (Type u_3)} {inst : FunLike F α X}   {inst_1 : Topol
ogicalSpace F} {inst_2 : Topolo…
· 使用定理 `ContinuousMap.instContinuousEvalConst`：∀ {X : Type u_2} {Y : Type u_3} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   ContinuousEvalConst 
C(X, Y) X Y
· 使用定理 `isOpen_sigma_fst_preimage`：isOpen_sigma_fst_preimage (s : Set ι) : IsOpe
n (Sigma.fst ⁻¹' s : Set (Σ a, σ a))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Function.eq_of_sigmaMk_comp`：∀ {α : Type u_1} {β : α → Type u_4} {γ : Ty
pe u_7} [Nonempty γ] {a b : α} {f : γ → β a} {g : γ → β b},   Sigma.mk a ∘ f = S
igma.mk b ∘ g → a…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem isEmbedding_sigmaMk_comp [Nonempty X] :
    IsEmbedding (fun g : Σ i, C(X, Y i) ↦ (sigmaMk g.1).comp g.2) where
  toIsInducing := inducing_sigma.2
    ⟨fun i ↦ (sigmaMk i).isInducing_postcomp IsEmbedding.sigmaMk.isInducing, fun i ↦
      let ⟨x⟩ := ‹Nonempty X›
      ⟨_, (isOpen_sigma_fst_preimage {i}).preimage (continuous_eval_const x), fun _ ↦ Iff.rfl⟩⟩
  injective := by
    rintro ⟨i, g⟩ ⟨i', g'⟩ h
    obtain ⟨rfl, hg⟩ : i = i' ∧ ⇑g ≍ ⇑g' :=
      Function.eq_of_sigmaMk_comp <| congr_arg DFunLike.coe h
    simpa using hg

section ConnectedSpace

variable [ConnectedSpace X]

/-- Every continuous map from a connected topological space to the disjoint union of a family of
topological spaces is a composition of the embedding `ContinuousMap.sigmaMk i : C(Y i, Σ i, Y i)`
for some `i` and a continuous map `g : C(X, Y i)`. See also `Continuous.exists_lift_sigma` for a
version with unbundled functions and `ContinuousMap.sigmaCodHomeomorph` for a homeomorphism defined
using this fact. -/
/-
**ContinuousMap.exists_lift_sigma** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：exists_lift_sigma (f : C(X, Σ i, Y i)) : exists i g, f = (sigmaMk i).comp 
g
参数：f : C(X, Σ i, Y i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.exists_lift_sigma`：Continuous.exists_lift_sigma [ConnectedSpa
ce α] [forall i, TopologicalSpace (X i)] {f : α -> Σ i, X i} (hf : Continuous f)
 : exists (i : ι) …
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g

--- 原说明 ---
Every continuous map from a connected topological space to the disjoint union of
 a family of
topological spaces is a composition of the embedding `ContinuousMap.sigmaMk i : 
C(Y i, Σ i, Y i)`
for some `i` and a continuous map `g : C(X, Y i)`. See also `Continuous.exists_l
ift_sigma` for a
version with unbundled functions and `ContinuousMap.sigmaCodHomeomorph` for a ho
meomorphism defined
using this fact.
-/
theorem exists_lift_sigma (f : C(X, Σ i, Y i)) : ∃ i g, f = (sigmaMk i).comp g :=
  let ⟨i, g, hg, hfg⟩ := (map_continuous f).exists_lift_sigma
  ⟨i, ⟨g, hg⟩, DFunLike.ext' hfg⟩

variable (X Y)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Homeomorphism between the type `C(X, Σ i, Y i)` of continuous maps from a connected topological
space to the disjoint union of a family of topological spaces and the disjoint union of the types of
continuous maps `C(X, Y i)`.

The inverse map sends `⟨i, g⟩` to `ContinuousMap.comp (ContinuousMap.sigmaMk i) g`. -/
@[simps! symm_apply]
/-
**ContinuousMap.sigmaCodHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：sigmaCodHomeomorph : C(X, Σ i, Y i) ≃ₜ Σ i, C(X, Y i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homeomorphism between the type `C(X, Σ i, Y i)` of continuous maps from a connec
ted topological
space to the disjoint union of a family of topological spaces and the disjoint u
nion of the types of
continuous maps `C(X, Y i)`.

The inverse map sends `⟨i, g⟩` to `ContinuousMap.comp (ContinuousMap.sigmaMk i) 
g`.
-/
def sigmaCodHomeomorph : C(X, Σ i, Y i) ≃ₜ Σ i, C(X, Y i) :=
  .symm <| Equiv.toHomeomorphOfIsInducing
    (.ofBijective _ ⟨isEmbedding_sigmaMk_comp.injective, fun f ↦
      let ⟨i, g, hg⟩ := f.exists_lift_sigma; ⟨⟨i, g⟩, hg.symm⟩⟩)
    isEmbedding_sigmaMk_comp.isInducing

end ConnectedSpace

end ContinuousMap

