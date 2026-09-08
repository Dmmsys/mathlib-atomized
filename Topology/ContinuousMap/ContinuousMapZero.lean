/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuous maps sending zero to zero

This is the type of continuous maps from `X` to `R` such that `(0 : X) ↦ (0 : R)` for which we
provide the scoped notation `C(X, R)₀`.  We provide this as a dedicated type solely for the
non-unital continuous functional calculus, as using various terms of type `Ideal C(X, R)` were
overly burdensome on type class synthesis.

Of course, one could generalize to maps between pointed topological spaces, but that goes beyond
the purpose of this type.
-/

@[expose] public section

assert_not_exists StarOrderedRing

open Function Set Topology

/-- The type of continuous maps which map zero to zero.

Note that one should never use the structure projection `ContinuousMapZero.toContinuousMap` and
instead favor the coercion `(↑) : C(X, R)₀ → C(X, R)` available from the instance of
`ContinuousMapClass`. All the instances on `C(X, R)₀` from `C(X, R)` passes through this coercion,
not the structure projection. Of course, the two are definitionally equal, but not reducibly so. -/
/-
**ContinuousMapZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_1) → (R : Type u_2) → [Zero X] → [Zero R] → [TopologicalSpace 
X] → [TopologicalSpace R] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of continuous maps which map zero to zero.

Note that one should never use the structure projection `ContinuousMapZero.toCon
tinuousMap` and
instead favor the coercion `(↑) : C(X, R)₀ → C(X, R)` available from the instanc
e of
`ContinuousMapClass`. All the instances on `C(X, R)₀` from `C(X, R)` passes thro
ugh this coercion,
not the structure projection. Of course, the two are definitionally equal, but n
ot reducibly so.
-/
structure ContinuousMapZero (X R : Type*) [Zero X] [Zero R] [TopologicalSpace X]
    [TopologicalSpace R] extends C(X, R) where
  map_zero' : toContinuousMap 0 = 0

namespace ContinuousMapZero

@[inherit_doc]
scoped notation "C(" X ", " R ")₀" => ContinuousMapZero X R

section Basic

variable {X Y R : Type*} [Zero X] [Zero Y] [Zero R]
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace R]

/-
**ContinuousMapZero.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
形式化陈述：instFunLike : FunLike C(X, R)₀ X R where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike C(X, R)₀ X R where
  coe f := f.toFun
  coe_injective _ _ h := congr(⟨⟨$(h), _⟩, _⟩)
/-
**ContinuousMapZero.instContinuousMapClass** 是 Mathlib 中的一个实例，位于命名空间 `Continuous
MapZero`。
形式化陈述：instContinuousMapClass : ContinuousMapClass C(X, R)₀ X R where map_continu
ous f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
-/
instance instContinuousMapClass : ContinuousMapClass C(X, R)₀ X R where
  map_continuous f := f.continuous
/-
**ContinuousMapZero.instZeroHomClass** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZer
o`。
形式化陈述：instZeroHomClass : ZeroHomClass C(X, R)₀ X R where map_zero f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMapZero.map_zero'`：∀ {X : Type u_1} {R : Type u_2} [inst : Zer
o X] [inst_1 : Zero R] [inst_2 : TopologicalSpace X]   [inst_3 : TopologicalSpac
e R] (self : Cont…
-/
instance instZeroHomClass : ZeroHomClass C(X, R)₀ X R where
  map_zero f := f.map_zero'

/-- not marked as an instance because it would be a bad one in general, but it can
be useful when working with `ContinuousMapZero` and the non-unital continuous
functional calculus. -/
@[instance_reducible]
/-
**ContinuousMapZero._root_.Set.zeroOfFactMem** 是 Mathlib 中的一个定义，位于命名空间 `Continuo
usMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
not marked as an instance because it would be a bad one in general, but it can
be useful when working with `ContinuousMapZero` and the non-unital continuous
functional calculus.
-/
def _root_.Set.zeroOfFactMem {X : Type*} [Zero X] (s : Set X) [Fact (0 ∈ s)] :
    Zero s where
  zero := ⟨0, Fact.out⟩

scoped[ContinuousMapZero] attribute [instance] Set.zeroOfFactMem

@[ext]
/-
**ContinuousMapZero.ext** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMapZero`。
形式化陈述：ext {f g : C(X, R)₀} (h : forall x, f x = g x) : f = g
参数：X, R；h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
lemma ext {f g : C(X, R)₀} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

@[simp]
/-
**ContinuousMapZero.coe_mk** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMapZero`。
形式化陈述：coe_mk {f : C(X, R)} {h0 : f 0 = 0} : ⇑(mk f h0) = f
参数：X, R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk {f : C(X, R)} {h0 : f 0 = 0} : ⇑(mk f h0) = f := rfl
/-
**ContinuousMapZero.toContinuousMap_injective** 是 Mathlib 中的一个引理，位于命名空间 `Continu
ousMapZero`。
形式化陈述：toContinuousMap_injective : Injective ((↑) : C(X, R)₀ -> C(X, R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `ContinuousMapZero.map_zero'`：∀ {X : Type u_1} {R : Type u_2} [inst : Zer
o X] [inst_1 : Zero R] [inst_2 : TopologicalSpace X]   [inst_3 : TopologicalSpac
e R] (self : Cont…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma toContinuousMap_injective : Injective ((↑) : C(X, R)₀ → C(X, R)) :=
  fun _ _ h ↦ congr(.mk $(h) _)
/-
**ContinuousMapZero.range_toContinuousMap** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousM
apZero`。
形式化陈述：range_toContinuousMap : range ((↑) : C(X, R)₀ -> C(X, R)) = {f : C(X, R) |
 f 0 = 0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
-/
lemma range_toContinuousMap : range ((↑) : C(X, R)₀ → C(X, R)) = {f : C(X, R) | f 0 = 0} :=
  Set.ext fun f ↦ ⟨fun ⟨f', hf'⟩ ↦ hf' ▸ map_zero f', fun hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩

/-- Composition of continuous maps which map zero to zero. -/
/-
**ContinuousMapZero.comp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMapZero`。
形式化陈述：comp (g : C(Y, R)₀) (f : C(X, Y)₀) : C(X, R)₀ where toContinuousMap
参数：g : C(Y, R)₀；f : C(X, Y)₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of continuous maps which map zero to zero.
-/
def comp (g : C(Y, R)₀) (f : C(X, Y)₀) : C(X, R)₀ where
  toContinuousMap := (g : C(Y, R)).comp (f : C(X, Y))
  map_zero' := show g (f 0) = 0 from map_zero f ▸ map_zero g

@[simp]
/-
**ContinuousMapZero.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMapZero`。
形式化陈述：comp_apply (g : C(Y, R)₀) (f : C(X, Y)₀) (x : X) : g.comp f x = g (f x)
参数：g : C(Y, R)₀；f : C(X, Y)₀；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_apply (g : C(Y, R)₀) (f : C(X, Y)₀) (x : X) : g.comp f x = g (f x) := rfl
/-
**ContinuousMapZero.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZer
o`。
形式化陈述：instPartialOrder [PartialOrder R] : PartialOrder C(X, R)₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrder [PartialOrder R] : PartialOrder C(X, R)₀ := fast_instance%
  .lift _ DFunLike.coe_injective
/-
**ContinuousMapZero.le_def** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMapZero`。
形式化陈述：le_def [PartialOrder R] (f g : C(X, R)₀) : f <= g ↔ forall x, f x <= g x
参数：f g : C(X, R)₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_def [PartialOrder R] (f g : C(X, R)₀) : f ≤ g ↔ ∀ x, f x ≤ g x := Iff.rfl
/-
**ContinuousMapZero.instTopologicalSpace** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMa
pZero`。
形式化陈述：{X : Type u_1} →   {R : Type u_3} →     [inst : Zero X] →       [inst_1 : 
Zero R] →         [inst_2 : TopologicalSpace X] → [inst_3 : TopologicalSpace R] 
→ TopologicalSpace (ContinuousMapZero X R)
参数：ContinuousMapZero X R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance instTopologicalSpace : TopologicalSpace C(X, R)₀ := fast_instance%
  TopologicalSpace.induced ((↑) : C(X, R)₀ → C(X, R)) inferInstance
/-
**ContinuousMapZero.isEmbedding_toContinuousMap** 是 Mathlib 中的一个引理，位于命名空间 `Conti
nuousMapZero`。
形式化陈述：isEmbedding_toContinuousMap : IsEmbedding ((↑) : C(X, R)₀ -> C(X, R)) wher
e eq_induced
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMapZero.ext`：ext {f g : C(X, R)₀} (h : forall x, f x = g x) : 
f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma isEmbedding_toContinuousMap : IsEmbedding ((↑) : C(X, R)₀ → C(X, R)) where
  eq_induced := rfl
  injective _ _ h := ext fun x ↦ congr($(h) x)
/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T0Space R] : T0Space C(X, R)₀ := isEmbedding_toContinuousMap.t0Space
/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [R0Space R] : R0Space C(X, R)₀ := isEmbedding_toContinuousMap.r0Space
/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T1Space R] : T1Space C(X, R)₀ := isEmbedding_toContinuousMap.t1Space
/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [R1Space R] : R1Space C(X, R)₀ := isEmbedding_toContinuousMap.r1Space
/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space R] : T2Space C(X, R)₀ := isEmbedding_toContinuousMap.t2Space
/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RegularSpace R] : RegularSpace C(X, R)₀ := isEmbedding_toContinuousMap.regularSpace
/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T3Space R] : T3Space C(X, R)₀ := isEmbedding_toContinuousMap.t3Space
/-
**ContinuousMapZero.instContinuousEvalConst** 是 Mathlib 中的一个实例，位于命名空间 `Continuou
sMapZero`。
形式化陈述：instContinuousEvalConst : ContinuousEvalConst C(X, R)₀ X R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousEvalConst.of_continuous_forget`：ContinuousEvalConst.of_continu
ous_forget {F' : Type*} [FunLike F' α X] [TopologicalSpace F'] {f : F' -> F} (hc
 : Continuous f) (hf : forall …
· 使用定理 `ContinuousMap.instContinuousEvalConst`：∀ {X : Type u_2} {Y : Type u_3} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   ContinuousEvalConst 
C(X, Y) X Y
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用引理 `ContinuousMapZero.isEmbedding_toContinuousMap`：isEmbedding_toContinuousM
ap : IsEmbedding ((↑) : C(X, R)₀ -> C(X, R)) where eq_induced
-/
instance instContinuousEvalConst : ContinuousEvalConst C(X, R)₀ X R :=
  .of_continuous_forget isEmbedding_toContinuousMap.continuous
/-
**ContinuousMapZero.instContinuousEval** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZ
ero`。
形式化陈述：instContinuousEval [LocallyCompactPair X R] : ContinuousEval C(X, R)₀ X R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousEval.of_continuous_forget`：ContinuousEval.of_continuous_forget
 {F' : Type*} [FunLike F' X Y] [TopologicalSpace F'] {f : F' -> F} (hc : Continu
ous f) (hf : forall g, ⇑(…
· 使用定理 `ContinuousMap.instContinuousEvalOfLocallyCompactPair`：∀ {X : Type u_2} {
Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [Locally
CompactPair X Y],   ContinuousEval C(X, Y)…
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用引理 `ContinuousMapZero.isEmbedding_toContinuousMap`：isEmbedding_toContinuousM
ap : IsEmbedding ((↑) : C(X, R)₀ -> C(X, R)) where eq_induced
-/
instance instContinuousEval [LocallyCompactPair X R] : ContinuousEval C(X, R)₀ X R :=
  .of_continuous_forget isEmbedding_toContinuousMap.continuous
/-
**ContinuousMapZero.isClosedEmbedding_toContinuousMap** 是 Mathlib 中的一个引理，位于命名空间 
`ContinuousMapZero`。
形式化陈述：isClosedEmbedding_toContinuousMap [T1Space R] : IsClosedEmbedding ((↑) : C
(X, R)₀ -> C(X, R)) where toIsEmbedding
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMapZero.isEmbedding_toContinuousMap`：isEmbedding_toContinuousM
ap : IsEmbedding ((↑) : C(X, R)₀ -> C(X, R)) where eq_induced
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousMapZero.range_toContinuousMap`：range_toContinuousMap : range (
(↑) : C(X, R)₀ -> C(X, R)) = {f : C(X, R) | f 0 = 0}
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `ContinuousEvalConst.continuous_eval_const`：∀ {F : Type u_1} {α : outPara
m (Type u_2)} {X : outParam (Type u_3)} {inst : FunLike F α X}   {inst_1 : Topol
ogicalSpace F} {inst_2 : Topolo…
· 使用定理 `ContinuousMap.instContinuousEvalConst`：∀ {X : Type u_2} {Y : Type u_3} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   ContinuousEvalConst 
C(X, Y) X Y
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
-/
lemma isClosedEmbedding_toContinuousMap [T1Space R] :
    IsClosedEmbedding ((↑) : C(X, R)₀ → C(X, R)) where
  toIsEmbedding := isEmbedding_toContinuousMap
  isClosed_range := by
    rw [range_toContinuousMap]
    exact isClosed_singleton.preimage <| continuous_eval_const 0

@[fun_prop]
/-
**ContinuousMapZero.continuous_precomp** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMapZ
ero`。
形式化陈述：continuous_precomp (f : C(X, Y)₀) : Continuous fun g : C(Y, R)₀ => g.comp 
f
参数：f : C(X, Y)₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `ContinuousMap.continuous_precomp`：continuous_precomp (f : C(X, Y)) : Con
tinuous (fun g => g.comp f : C(Y, Z) -> C(X, Z))
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
-/
lemma continuous_precomp (f : C(X, Y)₀) : Continuous fun g : C(Y, R)₀ ↦ g.comp f := by
  rw [continuous_induced_rng]
  change Continuous fun g : C(Y, R)₀ ↦ (g : C(Y, R)).comp (f : C(X, Y))
  fun_prop

@[deprecated (since := "2026-02-20")] alias continuous_comp_left := continuous_precomp
/-
**ContinuousMapZero.postcomp_injective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMapZ
ero`。
形式化陈述：postcomp_injective (g : C(Y, R)₀) (hg : Injective g) : Injective (g.comp :
 C(X, Y)₀ -> C(X, R)₀)
参数：g : C(Y, R)₀；hg : Injective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMapZero.ext`：ext {f g : C(X, R)₀} (h : forall x, f x = g x) : 
f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem postcomp_injective (g : C(Y, R)₀) (hg : Injective g) :
    Injective (g.comp : C(X, Y)₀ → C(X, R)₀) :=
  fun _ _ h ↦ ext fun x ↦ hg congr($h x)

@[fun_prop]
/-
**ContinuousMapZero.continuous_postcomp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
Zero`。
形式化陈述：continuous_postcomp (g : C(Y, R)₀) : Continuous (g.comp : C(X, Y)₀ -> C(X,
 R)₀)
参数：g : C(Y, R)₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsEmbedding.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z 
: Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topo
logicalSpace Y] [inst_2 :…
· 使用引理 `ContinuousMapZero.isEmbedding_toContinuousMap`：isEmbedding_toContinuousM
ap : IsEmbedding ((↑) : C(X, R)₀ -> C(X, R)) where eq_induced
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousMap.continuous_postcomp`：continuous_postcomp (g : C(Y, Z)) : C
ontinuous (ContinuousMap.comp g : C(X, Y) -> C(X, Z))
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
-/
theorem continuous_postcomp (g : C(Y, R)₀) : Continuous (g.comp : C(X, Y)₀ → C(X, R)₀) := by
  rw [ContinuousMapZero.isEmbedding_toContinuousMap.continuous_iff]
  exact g.toContinuousMap.continuous_postcomp |>.comp <|
    ContinuousMapZero.isEmbedding_toContinuousMap.continuous

/-- The identity function as an element of `C(s, R)₀` when `0 ∈ (s : Set R)`. -/
@[simps!]
/-
**ContinuousMapZero.id** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMapZero`。
形式化陈述：{R : Type u_3} →   [inst : Zero R] → [inst_1 : TopologicalSpace R] → (s : 
Set R) → [inst_2 : Fact (0 ∈ s)] → ContinuousMapZero (↑s) R
参数：s : Set R；0 ∈ s；↑s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity function as an element of `C(s, R)₀` when `0 ∈ (s : Set R)`.
-/
protected def id (s : Set R) [Fact (0 ∈ s)] : C(s, R)₀ :=
  ⟨.restrict s (.id R), rfl⟩

@[simp]
/-
**ContinuousMapZero.toContinuousMap_id** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMapZ
ero`。
形式化陈述：toContinuousMap_id {s : Set R} [Fact (0 in s)] : (ContinuousMapZero.id s :
 C(s, R)) = .restrict s (.id R)
参数：0 in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousMap_id {s : Set R} [Fact (0 ∈ s)] :
    (ContinuousMapZero.id s : C(s, R)) = .restrict s (.id R) :=
  rfl

end Basic

section mkD

variable {X R : Type*} [Zero R]
variable [TopologicalSpace X] [TopologicalSpace R]

open scoped Classical in
/--
Interpret `f : α → β` as an element of `C(α, β)₀`, falling back to the default value
`default : C(α, β)₀` if `f` is not continuous or does not map `0` to `0`.
This is mainly intended to be used for `C(α, β)₀`-valued integration. For example, if a family of
functions `f : ι → α → β` satisfies that `f i` is continuous and maps `0` to `0` for almost every
`i`, you can write the `C(α, β)₀`-valued integral "`∫ i, f i`" as
`∫ i, ContinuousMapZero.mkD (f i) 0`.
-/
/-
**ContinuousMapZero.mkD** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMapZero`。
形式化陈述：mkD [Zero X] (f : X -> R) (default : C(X, R)₀) : C(X, R)₀
参数：f : X -> R；default : C(X, R)₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret `f : α → β` as an element of `C(α, β)₀`, falling back to the default v
alue
`default : C(α, β)₀` if `f` is not continuous or does not map `0` to `0`.
This is mainly intended to be used for `C(α, β)₀`-valued integration. For exampl
e, if a family of
functions `f : ι → α → β` satisfies that `f i` is continuous and maps `0` to `0`
 for almost every
`i`, you can write the `C(α, β)₀`-valued integral "`∫ i, f i`" as
`∫ i, ContinuousMapZero.mkD (f i) 0`.
-/
noncomputable def mkD [Zero X] (f : X → R) (default : C(X, R)₀) : C(X, R)₀ :=
  if h : Continuous f ∧ f 0 = 0 then ⟨⟨_, h.1⟩, h.2⟩ else default
/-
**ContinuousMapZero.mkD_of_continuous** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMapZe
ro`。
形式化陈述：mkD_of_continuous [Zero X] {f : X -> R} {g : C(X, R)₀} (hf : Continuous f)
 (hf₀ : f 0 = 0) : mkD f g = ⟨⟨f, hf⟩, hf₀⟩
参数：X, R；hf : Continuous f；hf₀ : f 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
lemma mkD_of_continuous [Zero X] {f : X → R} {g : C(X, R)₀} (hf : Continuous f) (hf₀ : f 0 = 0) :
    mkD f g = ⟨⟨f, hf⟩, hf₀⟩ := by
  simp only [mkD, And.intro hf hf₀, true_and, ↓reduceDIte]
/-
**ContinuousMapZero.mkD_of_not_continuous** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousM
apZero`。
形式化陈述：mkD_of_not_continuous [Zero X] {f : X -> R} {g : C(X, R)₀} (hf : ¬ Continu
ous f) : mkD f g = g
参数：X, R；hf : ¬ Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_and_of_not_left`：∀ {a : Prop} (b : Prop), ¬a → ¬(a ∧ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mkD_of_not_continuous [Zero X] {f : X → R} {g : C(X, R)₀} (hf : ¬ Continuous f) :
    mkD f g = g := by
  simp only [mkD, not_and_of_not_left _ hf, ↓reduceDIte]
/-
**ContinuousMapZero.mkD_of_not_zero** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMapZero
`。
形式化陈述：mkD_of_not_zero [Zero X] {f : X -> R} {g : C(X, R)₀} (hf : f 0 != 0) : mkD
 f g = g
参数：X, R；hf : f 0 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_and_of_not_right`：∀ (a : Prop) {b : Prop}, ¬b → ¬(a ∧ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mkD_of_not_zero [Zero X] {f : X → R} {g : C(X, R)₀} (hf : f 0 ≠ 0) :
    mkD f g = g := by
  simp only [mkD, not_and_of_not_right _ hf, ↓reduceDIte]
/-
**ContinuousMapZero.mkD_apply_of_continuous** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sMapZero`。
形式化陈述：mkD_apply_of_continuous [Zero X] {f : X -> R} {g : C(X, R)₀} {x : X} (hf :
 Continuous f) (hf₀ : f 0 = 0) : mkD f g x = f x
参数：X, R；hf : Continuous f；hf₀ : f 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousMapZero.mkD_of_continuous`：mkD_of_continuous [Zero X] {f : X -
> R} {g : C(X, R)₀} (hf : Continuous f) (hf₀ : f 0 = 0) : mkD f g = ⟨⟨f, hf⟩, hf
₀⟩
· 使用引理 `ContinuousMapZero.coe_mk`：coe_mk {f : C(X, R)} {h0 : f 0 = 0} : ⇑(mk f h
0) = f
· 使用定理 `ContinuousMap.coe_mk`：coe_mk (f : X -> Y) (h : Continuous f) : ⇑(⟨f, h⟩ 
: C(X, Y)) = f
-/
lemma mkD_apply_of_continuous [Zero X] {f : X → R} {g : C(X, R)₀} {x : X}
    (hf : Continuous f) (hf₀ : f 0 = 0) :
    mkD f g x = f x := by
  rw [mkD_of_continuous hf hf₀, coe_mk, ContinuousMap.coe_mk]
/-
**ContinuousMapZero.mkD_of_continuousOn** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap
Zero`。
形式化陈述：mkD_of_continuousOn {s : Set X} [Zero s] {f : X -> R} {g : C(s, R)₀} (hf :
 ContinuousOn f s) (hf₀ : f (0 : s) = 0) : mkD (s.domRestrict f) g = ⟨⟨s.domRest
rict f, hf.domRestrict⟩, hf₀⟩
参数：s, R；hf : ContinuousOn f s；hf₀ : f (0 : s) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMapZero.mkD_of_continuous`：mkD_of_continuous [Zero X] {f : X -
> R} {g : C(X, R)₀} (hf : Continuous f) (hf₀ : f 0 = 0) : mkD f g = ⟨⟨f, hf⟩, hf
₀⟩
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
-/
lemma mkD_of_continuousOn {s : Set X} [Zero s] {f : X → R} {g : C(s, R)₀}
    (hf : ContinuousOn f s) (hf₀ : f (0 : s) = 0) :
    mkD (s.domRestrict f) g = ⟨⟨s.domRestrict f, hf.domRestrict⟩, hf₀⟩ :=
  mkD_of_continuous hf.domRestrict hf₀
/-
**ContinuousMapZero.mkD_of_not_continuousOn** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sMapZero`。
形式化陈述：mkD_of_not_continuousOn {s : Set X} [Zero s] {f : X -> R} {g : C(s, R)₀} (
hf : ¬ ContinuousOn f s) : mkD (s.domRestrict f) g = g
参数：s, R；hf : ¬ ContinuousOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMapZero.mkD_of_not_continuous`：mkD_of_not_continuous [Zero X] 
{f : X -> R} {g : C(X, R)₀} (hf : ¬ Continuous f) : mkD f g = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
-/
lemma mkD_of_not_continuousOn {s : Set X} [Zero s] {f : X → R} {g : C(s, R)₀}
    (hf : ¬ ContinuousOn f s) :
    mkD (s.domRestrict f) g = g := by
  rw [continuousOn_iff_continuous_domRestrict] at hf
  exact mkD_of_not_continuous hf

set_option backward.isDefEq.respectTransparency false in
/-
**ContinuousMapZero.mkD_apply_of_continuousOn** 是 Mathlib 中的一个引理，位于命名空间 `Continu
ousMapZero`。
形式化陈述：mkD_apply_of_continuousOn {s : Set X} [Zero s] {f : X -> R} {g : C(s, R)₀}
 {x : s} (hf : ContinuousOn f s) (hf₀ : f (0 : s) = 0) : mkD (s.domRestrict f) g
 x = f x
参数：s, R；hf : ContinuousOn f s；hf₀ : f (0 : s) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousMapZero.mkD_of_continuousOn`：mkD_of_continuousOn {s : Set X} [
Zero s] {f : X -> R} {g : C(s, R)₀} (hf : ContinuousOn f s) (hf₀ : f (0 : s) = 0
) : mkD (s.domRestrict f) g…
· 使用引理 `ContinuousMapZero.coe_mk`：coe_mk {f : C(X, R)} {h0 : f 0 = 0} : ⇑(mk f h
0) = f
· 使用定理 `ContinuousMap.coe_mk`：coe_mk (f : X -> Y) (h : Continuous f) : ⇑(⟨f, h⟩ 
: C(X, Y)) = f
· 使用定理 `Set.domRestrict_apply`：domRestrict_apply (f : (a : α) -> π a) (s : Set α
) (x : s) : s.domRestrict f x = f x
-/
lemma mkD_apply_of_continuousOn {s : Set X} [Zero s] {f : X → R} {g : C(s, R)₀} {x : s}
    (hf : ContinuousOn f s) (hf₀ : f (0 : s) = 0) :
    mkD (s.domRestrict f) g x = f x := by
  rw [mkD_of_continuousOn hf hf₀, coe_mk, ContinuousMap.coe_mk, domRestrict_apply]

open ContinuousMap in
/-- Link between `ContinuousMapZero.mkD` and `ContinuousMap.mkD`. -/
/-
**ContinuousMapZero.mkD_eq_mkD_of_map_zero** 是 Mathlib 中的一个引理，位于命名空间 `Continuous
MapZero`。
形式化陈述：mkD_eq_mkD_of_map_zero [Zero X] (f : X -> R) (g : C(X, R)₀) (f_zero : f 0 
= 0) : mkD f g = ContinuousMap.mkD f g
参数：f : X -> R；g : C(X, R)₀；f_zero : f 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `toContinuousMap.congr_simp`：∀ {F : Type u_1} {X : Type u_2} {Y : Type u_
3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : FunLike
 F X Y] [inst_3 …
· 使用引理 `ContinuousMapZero.mkD_of_continuous`：mkD_of_continuous [Zero X] {f : X -
> R} {g : C(X, R)₀} (hf : Continuous f) (hf₀ : f 0 = 0) : mkD f g = ⟨⟨f, hf⟩, hf
₀⟩
· 使用引理 `ContinuousMap.mkD_of_continuous`：mkD_of_continuous {f : α -> β} {g : C(α
, β)} (hf : Continuous f) : mkD f g = ⟨f, hf⟩
· 使用引理 `ContinuousMapZero.mkD_of_not_continuous`：mkD_of_not_continuous [Zero X] 
{f : X -> R} {g : C(X, R)₀} (hf : ¬ Continuous f) : mkD f g = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `ContinuousMap.mkD_of_not_continuous`：mkD_of_not_continuous {f : α -> β} 
{g : C(α, β)} (hf : ¬ Continuous f) : mkD f g = g

--- 原说明 ---
Link between `ContinuousMapZero.mkD` and `ContinuousMap.mkD`.
-/
lemma mkD_eq_mkD_of_map_zero [Zero X] (f : X → R) (g : C(X, R)₀) (f_zero : f 0 = 0) :
    mkD f g = ContinuousMap.mkD f g := by
  ext
  by_cases f_cont : Continuous f <;>
    simp [*, ContinuousMap.mkD_of_continuous, mkD_of_continuous, mkD_of_not_continuous,
      ContinuousMap.mkD_of_not_continuous]
/-
**ContinuousMapZero.mkD_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMapZero`。
形式化陈述：mkD_eq_self [Zero X] {f g : C(X, R)₀} : mkD f g = f
参数：X, R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMapZero.mkD_of_continuous`：mkD_of_continuous [Zero X] {f : X -
> R} {g : C(X, R)₀} (hf : Continuous f) (hf₀ : f 0 = 0) : mkD f g = ⟨⟨f, hf⟩, hf
₀⟩
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
-/
lemma mkD_eq_self [Zero X] {f g : C(X, R)₀} : mkD f g = f :=
  mkD_of_continuous f.continuous (map_zero f)

end mkD

section Algebra

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [TopologicalSpace R]

/-
**ContinuousMapZero.instZero** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
形式化陈述：instZero [Zero R] : Zero C(X, R)₀ where zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero [Zero R] : Zero C(X, R)₀ where
  zero := ⟨0, rfl⟩
/-
**ContinuousMapZero.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMapZero`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Zero X] [inst_1 : TopologicalSpace
 X] [inst_2 : TopologicalSpace R]   [inst_3 : Zero R], ⇑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_zero [Zero R] : ⇑(0 : C(X, R)₀) = 0 := rfl
/-
**ContinuousMapZero.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
形式化陈述：instAdd [AddZeroClass R] [ContinuousAdd R] : Add C(X, R)₀ where add f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd [AddZeroClass R] [ContinuousAdd R] : Add C(X, R)₀ where
  add f g := ⟨f + g, by simp⟩
/-
**ContinuousMapZero.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMapZero`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Zero X] [inst_1 : TopologicalSpace
 X] [inst_2 : TopologicalSpace R]   [inst_3 : AddZeroClass R] [inst_4 : Continuo
usAdd R] (f g : ContinuousMapZero X R), ⇑(f + g) = ⇑f + ⇑g
参数：f g : ContinuousMapZero X R；f + g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_add [AddZeroClass R] [ContinuousAdd R] (f g : C(X, R)₀) : ⇑(f + g) = f + g := rfl
/-
**ContinuousMapZero.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
形式化陈述：instNeg [NegZeroClass R] [ContinuousNeg R] : Neg C(X, R)₀ where neg f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg [NegZeroClass R] [ContinuousNeg R] : Neg C(X, R)₀ where
  neg f := ⟨- f, by simp⟩
/-
**ContinuousMapZero.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMapZero`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Zero X] [inst_1 : TopologicalSpace
 X] [inst_2 : TopologicalSpace R]   [inst_3 : NegZeroClass R] [inst_4 : Continuo
usNeg R] (f : ContinuousMapZero X R), ⇑(-f) = -⇑f
参数：f : ContinuousMapZero X R；-f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_neg [NegZeroClass R] [ContinuousNeg R] (f : C(X, R)₀) : ⇑(-f) = -f := rfl
/-
**ContinuousMapZero.instSub** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
形式化陈述：instSub [SubNegZeroMonoid R] [ContinuousSub R] : Sub C(X, R)₀ where sub f 
g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub [SubNegZeroMonoid R] [ContinuousSub R] : Sub C(X, R)₀ where
  sub f g := ⟨f - g, by simp⟩
/-
**ContinuousMapZero.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMapZero`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Zero X] [inst_1 : TopologicalSpace
 X] [inst_2 : TopologicalSpace R]   [inst_3 : SubNegZeroMonoid R] [inst_4 : Cont
inuousSub R] (f g : ContinuousMapZero X R), ⇑(f - g) = ⇑f - ⇑g
参数：f g : ContinuousMapZero X R；f - g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_sub [SubNegZeroMonoid R] [ContinuousSub R] (f g : C(X, R)₀) :
    ⇑(f - g) = f - g := rfl
/-
**ContinuousMapZero.instMul** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
形式化陈述：instMul [MulZeroClass R] [ContinuousMul R] : Mul C(X, R)₀ where mul f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul [MulZeroClass R] [ContinuousMul R] : Mul C(X, R)₀ where
  mul f g := ⟨f * g, by simp⟩
/-
**ContinuousMapZero.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMapZero`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Zero X] [inst_1 : TopologicalSpace
 X] [inst_2 : TopologicalSpace R]   [inst_3 : MulZeroClass R] [inst_4 : Continuo
usMul R] (f g : ContinuousMapZero X R), ⇑(f * g) = ⇑f * ⇑g
参数：f g : ContinuousMapZero X R；f * g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mul [MulZeroClass R] [ContinuousMul R] (f g : C(X, R)₀) : ⇑(f * g) = f * g := rfl
/-
**ContinuousMapZero.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
形式化陈述：instSMul {M : Type*} [Zero R] [SMulZeroClass M R] [ContinuousConstSMul M R
] : SMul M C(X, R)₀ where smul m f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul {M : Type*} [Zero R] [SMulZeroClass M R] [ContinuousConstSMul M R] :
    SMul M C(X, R)₀ where
  smul m f := ⟨m • f, by simp⟩
/-
**ContinuousMapZero.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMapZero`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Zero X] [inst_1 : TopologicalSpace
 X] [inst_2 : TopologicalSpace R]   {M : Type u_3} [inst_3 : Zero R] [inst_4 : S
MulZeroClass M R] [inst_5 : ContinuousConstSMul M R] (m : M)   (f : ContinuousMa
pZero X R), ⇑(m • f) = m • ⇑f
参数：m : M；f : ContinuousMapZero X R；m • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_smul {M : Type*} [Zero R] [SMulZeroClass M R] [ContinuousConstSMul M R]
    (m : M) (f : C(X, R)₀) : ⇑(m • f) = m • f := rfl

section AddCommMonoid

variable [AddCommMonoid R] [ContinuousAdd R]

/-
**ContinuousMapZero.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZe
ro`。
形式化陈述：instAddCommMonoid : AddCommMonoid C(X, R)₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid : AddCommMonoid C(X, R)₀ :=
  fast_instance% toContinuousMap_injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
/-
**ContinuousMapZero.instModule** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
形式化陈述：instModule {M : Type*} [Semiring M] [Module M R] [ContinuousConstSMul M R]
 : Module M C(X, R)₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule {M : Type*} [Semiring M] [Module M R] [ContinuousConstSMul M R] :
    Module M C(X, R)₀ :=
  fast_instance% toContinuousMap_injective.module M
    { toFun := _, map_add' := fun _ _ ↦ rfl, map_zero' := rfl } (fun _ _ ↦ rfl)
/-
**ContinuousMapZero.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZe
ro`。
形式化陈述：instSMulCommClass {M N : Type*} [SMulZeroClass M R] [ContinuousConstSMul M
 R] [SMulZeroClass N R] [ContinuousConstSMul N R] [SMulCommClass M N R] : SMulCo
mmClass M N C(X, R)₀ where smul_comm _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMapZero.ext`：ext {f g : C(X, R)₀} (h : forall x, f x = g x) : 
f = g
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass {M N : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
    [SMulZeroClass N R] [ContinuousConstSMul N R] [SMulCommClass M N R] :
    SMulCommClass M N C(X, R)₀ where
  smul_comm _ _ _ := ext fun _ ↦ smul_comm ..
/-
**ContinuousMapZero.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZe
ro`。
形式化陈述：instIsScalarTower {M N : Type*} [SMulZeroClass M R] [ContinuousConstSMul M
 R] [SMulZeroClass N R] [ContinuousConstSMul N R] [SMul M N] [IsScalarTower M N 
R] : IsScalarTower M N C(X, R)₀ where smul_assoc _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMapZero.ext`：ext {f g : C(X, R)₀} (h : forall x, f x = g x) : 
f = g
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance instIsScalarTower {M N : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
    [SMulZeroClass N R] [ContinuousConstSMul N R] [SMul M N] [IsScalarTower M N R] :
    IsScalarTower M N C(X, R)₀ where
  smul_assoc _ _ _ := ext fun _ ↦ smul_assoc ..

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup R] [IsTopologicalAddGroup R]

/-
**ContinuousMapZero.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZer
o`。
形式化陈述：instAddCommGroup : AddCommGroup C(X, R)₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup : AddCommGroup C(X, R)₀ :=
  fast_instance% toContinuousMap_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end AddCommGroup

section Semiring

variable [CommSemiring R] [IsTopologicalSemiring R]

/-
**ContinuousMapZero.instNonUnitalCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Continu
ousMapZero`。
形式化陈述：instNonUnitalCommSemiring : NonUnitalCommSemiring C(X, R)₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalCommSemiring : NonUnitalCommSemiring C(X, R)₀ :=
  fast_instance% toContinuousMap_injective.nonUnitalCommSemiring
    _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
/-
**ContinuousMapZero.instSMulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZ
ero`。
形式化陈述：instSMulCommClass' {M : Type*} [SMulZeroClass M R] [SMulCommClass M R R] [
ContinuousConstSMul M R] : SMulCommClass M C(X, R)₀ C(X, R)₀ where smul_comm m f
 g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用引理 `ContinuousMapZero.ext`：ext {f g : C(X, R)₀} (h : forall x, f x = g x) : 
f = g
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass' {M : Type*} [SMulZeroClass M R] [SMulCommClass M R R]
    [ContinuousConstSMul M R] : SMulCommClass M C(X, R)₀ C(X, R)₀ where
  smul_comm m f g := ext fun x ↦ smul_comm m (f x) (g x)
/-
**ContinuousMapZero.instIsScalarTower'** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZ
ero`。
形式化陈述：instIsScalarTower' {M : Type*} [SMulZeroClass M R] [IsScalarTower M R R] [
ContinuousConstSMul M R] : IsScalarTower M C(X, R)₀ C(X, R)₀ where smul_assoc m 
f g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用引理 `ContinuousMapZero.ext`：ext {f g : C(X, R)₀} (h : forall x, f x = g x) : 
f = g
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance instIsScalarTower' {M : Type*} [SMulZeroClass M R] [IsScalarTower M R R]
    [ContinuousConstSMul M R] : IsScalarTower M C(X, R)₀ C(X, R)₀ where
  smul_assoc m f g := ext fun x ↦ smul_assoc m (f x) (g x)
/-
**ContinuousMapZero.instStarRing** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
形式化陈述：instStarRing [StarRing R] [ContinuousStar R] : StarRing C(X, R)₀ where sta
r f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarRing [StarRing R] [ContinuousStar R] : StarRing C(X, R)₀ where
  star f := ⟨star f, by simp⟩
  star_involutive _ := ext fun _ ↦ star_star _
  star_mul _ _ := ext fun _ ↦ star_mul ..
  star_add _ _ := ext fun _ ↦ star_add ..
/-
**ContinuousMapZero.instStarModule** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`
。
形式化陈述：instStarModule [StarRing R] {M : Type*} [SMulZeroClass M R] [ContinuousCon
stSMul M R] [Star M] [StarModule M R] [ContinuousStar R] : StarModule M C(X, R)₀
 where star_smul r f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMapZero.ext`：ext {f g : C(X, R)₀} (h : forall x, f x = g x) : 
f = g
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
-/
instance instStarModule [StarRing R] {M : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
    [Star M] [StarModule M R] [ContinuousStar R] : StarModule M C(X, R)₀ where
  star_smul r f := ext fun x ↦ star_smul r (f x)
/-
**ContinuousMapZero.coe_star** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMapZero`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Zero X] [inst_1 : TopologicalSpace
 X] [inst_2 : TopologicalSpace R]   [inst_3 : CommSemiring R] [inst_4 : IsTopolo
gicalSemiring R] [inst_5 : StarRing R] [inst_6 : ContinuousStar R]   (f : Contin
uousMapZero X R), ⇑(star f) = star ⇑f
参数：f : ContinuousMapZero X R；star f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_star [StarRing R] [ContinuousStar R] (f : C(X, R)₀) : ⇑(star f) = star ⇑f := rfl
/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [StarRing R] [ContinuousStar R] [TrivialStar R] : TrivialStar C(X, R)₀ where
  star_trivial _ := DFunLike.ext _ _ fun _ ↦ star_trivial _
/-
**ContinuousMapZero.instCanLift** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
形式化陈述：instCanLift : CanLift C(X, R) C(X, R)₀ (↑) (fun f => f 0 = 0) where prf f 
hf
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCanLift : CanLift C(X, R) C(X, R)₀ (↑) (fun f ↦ f 0 = 0) where
  prf f hf := ⟨⟨f, hf⟩, rfl⟩

/-- The coercion `C(X, R)₀ → C(X, R)` bundled as a non-unital star algebra homomorphism. -/
@[simps]
/-
**ContinuousMapZero.toContinuousMapHom** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMapZ
ero`。
形式化陈述：toContinuousMapHom [StarRing R] [ContinuousStar R] : C(X, R)₀ ->⋆ₙₐ[R] C(X
, R) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion `C(X, R)₀ → C(X, R)` bundled as a non-unital star algebra homomorph
ism.
-/
def toContinuousMapHom [StarRing R] [ContinuousStar R] : C(X, R)₀ →⋆ₙₐ[R] C(X, R) where
  toFun f := f
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
/-
**ContinuousMapZero.coe_toContinuousMapHom** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
MapZero`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Zero X] [inst_1 : TopologicalSpace
 X] [inst_2 : TopologicalSpace R]   [inst_3 : CommSemiring R] [inst_4 : IsTopolo
gicalSemiring R] [inst_5 : StarRing R] [inst_6 : ContinuousStar R],   ⇑Continuou
sMapZero.toContinuousMapHom = toContinuousMap
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
@[simp] lemma coe_toContinuousMapHom [StarRing R] [ContinuousStar R] :
    ⇑(toContinuousMapHom (X := X) (R := R)) = (↑) :=
  rfl

/-- The coercion `C(X, R)₀ → C(X, R)` bundled as a continuous linear map. -/
@[simps]
/-
**ContinuousMapZero.toContinuousMapCLM** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMapZ
ero`。
形式化陈述：toContinuousMapCLM (M : Type*) [Semiring M] [Module M R] [ContinuousConstS
Mul M R] : C(X, R)₀ ->L[M] C(X, R) where toFun f
参数：M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion `C(X, R)₀ → C(X, R)` bundled as a continuous linear map.
-/
def toContinuousMapCLM (M : Type*) [Semiring M] [Module M R] [ContinuousConstSMul M R] :
    C(X, R)₀ →L[M] C(X, R) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The evaluation at a point, as a continuous linear map from `C(X, R)₀` to `R`. -/
/-
**ContinuousMapZero.evalCLM** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMapZero`。
形式化陈述：evalCLM (𝕜 : Type*) [Semiring 𝕜] [Module 𝕜 R] [ContinuousConstSMul 𝕜 R] (x
 : X) : C(X, R)₀ ->L[𝕜] R
参数：𝕜 : Type*；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation at a point, as a continuous linear map from `C(X, R)₀` to `R`.
-/
def evalCLM (𝕜 : Type*) [Semiring 𝕜] [Module 𝕜 R] [ContinuousConstSMul 𝕜 R] (x : X) :
    C(X, R)₀ →L[𝕜] R :=
  (ContinuousMap.evalCLM 𝕜 x).comp (toContinuousMapCLM 𝕜)

@[simp]
/-
**ContinuousMapZero.evalCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMapZero`。
形式化陈述：evalCLM_apply {𝕜 : Type*} [Semiring 𝕜] [Module 𝕜 R] [ContinuousConstSMul 𝕜
 R] (x : X) (f : C(X, R)₀) : evalCLM 𝕜 x f = f x
参数：x : X；f : C(X, R)₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
-/
lemma evalCLM_apply {𝕜 : Type*} [Semiring 𝕜] [Module 𝕜 R] [ContinuousConstSMul 𝕜 R]
    (x : X) (f : C(X, R)₀) : evalCLM 𝕜 x f = f x := rfl

/-- Coercion to a function as an `AddMonoidHom`. Similar to `ContinuousMap.coeFnAddMonoidHom`. -/
/-
**ContinuousMapZero.coeFnAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMapZe
ro`。
形式化陈述：coeFnAddMonoidHom : C(X, R)₀ ->+ X -> R where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion to a function as an `AddMonoidHom`. Similar to `ContinuousMap.coeFnAddM
onoidHom`.
-/
def coeFnAddMonoidHom : C(X, R)₀ →+ X → R where
  toFun f := f
  map_zero' := coe_zero
  map_add' f g := by simp

@[simp]
/-
**ContinuousMapZero.coeFnAddMonoidHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sMapZero`。
形式化陈述：coeFnAddMonoidHom_apply (f : C(X, R)₀) : coeFnAddMonoidHom f = f
参数：f : C(X, R)₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
-/
lemma coeFnAddMonoidHom_apply (f : C(X, R)₀) : coeFnAddMonoidHom f = f := rfl
/-
**ContinuousMapZero.coe_sum** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMapZero`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Zero X] [inst_1 : TopologicalSpace
 X] [inst_2 : TopologicalSpace R]   [inst_3 : CommSemiring R] [inst_4 : IsTopolo
gicalSemiring R] {ι : Type u_3} (s : Finset ι)   (f : ι → ContinuousMapZero X R)
, ⇑(s.sum f) = ∑ i ∈ s, ⇑(f i)
参数：s : Finset ι；f : ι → ContinuousMapZero X R；s.sum f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
@[simp] lemma coe_sum {ι : Type*} (s : Finset ι)
    (f : ι → C(X, R)₀) : ⇑(s.sum f) = s.sum (fun i => ⇑(f i)) :=
  map_sum coeFnAddMonoidHom f s

end Semiring

section Ring

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-
**ContinuousMapZero.instNonUnitalCommRing** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousM
apZero`。
形式化陈述：instNonUnitalCommRing : NonUnitalCommRing C(X, R)₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalCommRing : NonUnitalCommRing C(X, R)₀ :=
  fast_instance% toContinuousMap_injective.nonUnitalCommRing _ rfl
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousNeg C(X, R)₀ where
  continuous_neg := by
    rw [continuous_induced_rng]
    exact continuous_neg.comp continuous_induced_dom

end Ring

end Algebra

section UniformSpace

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [Zero R] [UniformSpace R]

/-
**ContinuousMapZero.instUniformSpace** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMapZer
o`。
形式化陈述：{X : Type u_1} →   {R : Type u_2} →     [inst : Zero X] →       [inst_1 : 
TopologicalSpace X] →         [inst_2 : Zero R] → [inst_3 : UniformSpace R] → Un
iformSpace (ContinuousMapZero X R)
参数：ContinuousMapZero X R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance instUniformSpace : UniformSpace C(X, R)₀ :=
  fast_instance% .comap toContinuousMap inferInstance
/-
**ContinuousMapZero.isUniformEmbedding_toContinuousMap** 是 Mathlib 中的一个引理，位于命名空间
 `ContinuousMapZero`。
形式化陈述：isUniformEmbedding_toContinuousMap : IsUniformEmbedding ((↑) : C(X, R)₀ ->
 C(X, R)) where comap_uniformity
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMapZero.ext`：ext {f g : C(X, R)₀} (h : forall x, f x = g x) : 
f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma isUniformEmbedding_toContinuousMap :
    IsUniformEmbedding ((↑) : C(X, R)₀ → C(X, R)) where
  comap_uniformity := rfl
  injective _ _ h := ext fun x ↦ congr($(h) x)
/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T1Space R] [CompleteSpace C(X, R)] : CompleteSpace C(X, R)₀ :=
  completeSpace_iff_isComplete_range isUniformEmbedding_toContinuousMap.isUniformInducing
    |>.mpr isClosedEmbedding_toContinuousMap.isClosed_range.isComplete
/-
**ContinuousMapZero.isUniformEmbedding_comp** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sMapZero`。
形式化陈述：isUniformEmbedding_comp {Y : Type*} [UniformSpace Y] [Zero Y] (g : C(Y, R)
₀) (hg : IsUniformEmbedding g) : IsUniformEmbedding (g.comp · : C(X, Y)₀ -> C(X,
 R)₀)
参数：g : C(Y, R)₀；hg : IsUniformEmbedding g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUniformEmbedding.of_comp_iff`：IsUniformEmbedding.of_comp_iff {g : β ->
 γ} (hg : IsUniformEmbedding g) {f : α -> β} : IsUniformEmbedding (g ∘ f) ↔ IsUn
iformEmbedding f
· 使用引理 `ContinuousMapZero.isUniformEmbedding_toContinuousMap`：isUniformEmbedding
_toContinuousMap : IsUniformEmbedding ((↑) : C(X, R)₀ -> C(X, R)) where comap_un
iformity
· 使用定理 `IsUniformEmbedding.comp`：IsUniformEmbedding.comp {g : β -> γ} (hg : IsUn
iformEmbedding g) {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformEmbedding 
(g ∘ f) where…
· 使用定理 `ContinuousMap.isUniformEmbedding_comp`：isUniformEmbedding_comp (g : C(β,
 δ)) (hg : IsUniformEmbedding g) : IsUniformEmbedding (ContinuousMap.comp g : C(
α, β) -> C(α, δ))
-/
lemma isUniformEmbedding_comp {Y : Type*} [UniformSpace Y] [Zero Y] (g : C(Y, R)₀)
    (hg : IsUniformEmbedding g) : IsUniformEmbedding (g.comp · : C(X, Y)₀ → C(X, R)₀) :=
  isUniformEmbedding_toContinuousMap.of_comp_iff.mp <|
    ContinuousMap.isUniformEmbedding_comp g.toContinuousMap hg |>.comp
      isUniformEmbedding_toContinuousMap

/-- The uniform equivalence `C(X, R)₀ ≃ᵤ C(Y, R)₀` induced by a homeomorphism of the domains
sending `0 : X` to `0 : Y`. -/
/-
**ContinuousMapZero._root_.UniformEquiv.arrowCongrLeft** 是 Mathlib 中的一个定义，位于命名空间
 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uniform equivalence `C(X, R)₀ ≃ᵤ C(Y, R)₀` induced by a homeomorphism of the
 domains
sending `0 : X` to `0 : Y`.
-/
def _root_.UniformEquiv.arrowCongrLeft₀ {Y : Type*} [TopologicalSpace Y] [Zero Y] (f : X ≃ₜ Y)
    (hf : f 0 = 0) : C(X, R)₀ ≃ᵤ C(Y, R)₀ where
  toFun g := g.comp ⟨f.symm, (f.eq_symm_apply.eq ▸ hf).symm⟩
  invFun g := g.comp ⟨f, hf⟩
  left_inv g := ext fun _ ↦ congrArg g <| f.left_inv _
  right_inv g := ext fun _ ↦ congrArg g <| f.right_inv _
  uniformContinuous_toFun := isUniformEmbedding_toContinuousMap.uniformContinuous_iff.mpr <|
    ContinuousMap.uniformContinuous_comp_left (f.symm : C(Y, X)) |>.comp
    isUniformEmbedding_toContinuousMap.uniformContinuous
  uniformContinuous_invFun := isUniformEmbedding_toContinuousMap.uniformContinuous_iff.mpr <|
    ContinuousMap.uniformContinuous_comp_left (f : C(X, Y)) |>.comp
    isUniformEmbedding_toContinuousMap.uniformContinuous

end UniformSpace

section CompHoms

variable {X Y M R S : Type*} [Zero X] [Zero Y] [CommSemiring M]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace R] [TopologicalSpace S]
  [CommSemiring R] [StarRing R] [IsTopologicalSemiring R] [ContinuousStar R]
  [CommSemiring S] [StarRing S] [IsTopologicalSemiring S] [ContinuousStar S]
  [Module M R] [Module M S] [ContinuousConstSMul M R] [ContinuousConstSMul M S]

variable (R) in
/-- The functor `C(·, R)₀` from topological spaces with zero (and `ContinuousMapZero` maps) to
non-unital star algebras. -/
@[simps]
/-
**ContinuousMapZero.nonUnitalStarAlgHom_precomp** 是 Mathlib 中的一个定义，位于命名空间 `Conti
nuousMapZero`。
形式化陈述：nonUnitalStarAlgHom_precomp (f : C(X, Y)₀) : C(Y, R)₀ ->⋆ₙₐ[R] C(X, R)₀ wh
ere toFun g
参数：f : C(X, Y)₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `C(·, R)₀` from topological spaces with zero (and `ContinuousMapZero
` maps) to
non-unital star algebras.
-/
def nonUnitalStarAlgHom_precomp (f : C(X, Y)₀) : C(Y, R)₀ →⋆ₙₐ[R] C(X, R)₀ where
  toFun g := g.comp f
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
variable (X) in
/-- The functor `C(X, ·)₀` from non-unital topological star algebras (with non-unital continuous
star homomorphisms) to non-unital star algebras. -/
@[simps apply]
/-
**ContinuousMapZero.nonUnitalStarAlgHom_postcomp** 是 Mathlib 中的一个定义，位于命名空间 `Cont
inuousMapZero`。
形式化陈述：nonUnitalStarAlgHom_postcomp (φ : R ->⋆ₙₐ[M] S) (hφ : Continuous φ) : C(X,
 R)₀ ->⋆ₙₐ[M] C(X, S)₀ where toFun
参数：φ : R ->⋆ₙₐ[M] S；hφ : Continuous φ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `C(X, ·)₀` from non-unital topological star algebras (with non-unita
l continuous
star homomorphisms) to non-unital star algebras.
-/
def nonUnitalStarAlgHom_postcomp (φ : R →⋆ₙₐ[M] S) (hφ : Continuous φ) :
    C(X, R)₀ →⋆ₙₐ[M] C(X, S)₀ where
  toFun := .comp ⟨⟨φ, hφ⟩, by simp⟩
  map_zero' := ext <| by simp
  map_add' _ _ := ext <| by simp
  map_mul' _ _ := ext <| by simp
  map_star' _ := ext <| by simp [map_star]
  map_smul' r f := ext <| by simp

end CompHoms

section Norm

variable {α : Type*} {𝕜 : Type*} {R : Type*} [TopologicalSpace α] [CompactSpace α] [Zero α]

/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [MetricSpace R] [Zero R] : MetricSpace C(α, R)₀ :=
  ContinuousMapZero.isUniformEmbedding_toContinuousMap.comapMetricSpace _
/-
**ContinuousMapZero.isometry_toContinuousMap** 是 Mathlib 中的一个引理，位于命名空间 `Continuo
usMapZero`。
形式化陈述：isometry_toContinuousMap [MetricSpace R] [Zero R] : Isometry (toContinuous
Map : C(α, R)₀ -> C(α, R))
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isometry_toContinuousMap [MetricSpace R] [Zero R] :
    Isometry (toContinuousMap : C(α, R)₀ → C(α, R)) :=
  fun _ _ ↦ rfl
/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [NormedAddCommGroup R] : Norm C(α, R)₀ where
  norm f := ‖(f : C(α, R))‖
/-
**ContinuousMapZero.norm_def** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMapZero`。
形式化陈述：norm_def [NormedAddCommGroup R] (f : C(α, R)₀) : ‖f‖ = ‖(f : C(α, R))‖
参数：f : C(α, R)₀。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_def [NormedAddCommGroup R] (f : C(α, R)₀) : ‖f‖ = ‖(f : C(α, R))‖ :=
  rfl
/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [NormedAddCommGroup R] : NormedAddCommGroup C(α, R)₀ where
  dist_eq f g := NormedAddGroup.dist_eq (f : C(α, R)) g
/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [NormedCommRing R] : NonUnitalNormedCommRing C(α, R)₀ where
  dist_eq f g := NormedAddGroup.dist_eq (f : C(α, R)) g
  norm_mul_le f g := norm_mul_le (f : C(α, R)) g
  mul_comm f g := mul_comm f g
/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [NormedField 𝕜] [NormedCommRing R] [NormedAlgebra 𝕜 R] :
    NormedSpace 𝕜 C(α, R)₀ where
  norm_smul_le r f := norm_smul_le r (f : C(α, R))
/-
**ContinuousMapZero.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMapZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NormedCommRing R] [StarRing R] [CStarRing R] : CStarRing C(α, R)₀ where
  norm_mul_self_le f := CStarRing.norm_mul_self_le (f : C(α, R))

end Norm

end ContinuousMapZero

