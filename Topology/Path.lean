/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.UnitInterval

/-!
# Paths in topological spaces

This file introduces continuous paths and provides API for them.

## Main definitions

In this file the unit interval `[0, 1]` in `ℝ` is denoted by `I`, and `X` is a topological space.

* `Path x y` is the type of paths from `x` to `y`, i.e., continuous maps from `I` to `X`
  mapping `0` to `x` and `1` to `y`.
* `Path.refl x : Path x x` is the constant path at `x`.
* `Path.symm γ : Path y x` is the reverse of a path `γ : Path x y`.
* `Path.trans γ γ' : Path x z` is the concatenation of two paths `γ : Path x y`, `γ' : Path y z`.
* `Path.map γ hf : Path (f x) (f y)` is the image of `γ : Path x y` under a continuous map `f`.
* `Path.reparam γ f hf hf₀ hf₁ : Path x y` is the reparametrisation of `γ : Path x y` by
  a continuous map `f : I → I` fixing `0` and `1`.
* `Path.truncate γ t₀ t₁ : Path (γ t₀) (γ t₁)` is the path that follows `γ` from `t₀` to `t₁` and
  stays constant otherwise.
* `Path.extend γ : C(ℝ, X)` is the extension `γ` to `ℝ` that is constant before `0` and after `1`.

`Path x y` is equipped with the topology induced by the compact-open topology on `C(I,X)`, and
several of the above constructions are shown to be continuous.

## Implementation notes

By default, all paths have `I` as their source and `X` as their target, but there is an
operation `Set.IccExtend` that will extend any continuous map `γ : I → X` into a continuous map
`IccExtend zero_le_one γ : ℝ → X` that is constant before `0` and after `1`.

This is used to define `Path.extend` that turns `γ : Path x y` into a continuous map
`γ.extend : ℝ → X` whose restriction to `I` is the original `γ`, and is equal to `x`
on `(-∞, 0]` and to `y` on `[1, +∞)`.
-/

@[expose] public section

noncomputable section

open Topology Filter unitInterval Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*}

/-! ### Paths -/

/-- Continuous path connecting two points `x` and `y` in a topological space -/
/-
**Path** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{X : Type u_1} → [TopologicalSpace X] → X → X → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous path connecting two points `x` and `y` in a topological space
-/
structure Path (x y : X) extends C(I, X) where
  /-- The start point of a `Path`. -/
  source' : toFun 0 = x
  /-- The end point of a `Path`. -/
  target' : toFun 1 = y
/-
**Path.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Path.instFunLike : FunLike (Path x y) I X where coe γ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Path.instFunLike : FunLike (Path x y) I X where
  coe γ := ⇑γ.toContinuousMap
  coe_injective γ₁ γ₂ h := by
    simp only [DFunLike.coe_fn_eq] at h
    cases γ₁; cases γ₂; congr
/-
**Path.continuousMapClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Path.continuousMapClass : ContinuousMapClass (Path x y) I X where map_cont
inuous γ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
-/
instance Path.continuousMapClass : ContinuousMapClass (Path x y) I X where
  map_continuous γ := show Continuous γ.toContinuousMap by fun_prop

@[ext, grind ext]
/-
**Path.ext** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ : Path x y},
 ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Path.ext : ∀ {γ₁ γ₂ : Path x y}, (γ₁ : I → X) = γ₂ → γ₁ = γ₂ := by
  rintro ⟨⟨x, h11⟩, h12, h13⟩ ⟨⟨x, h21⟩, h22, h23⟩ rfl
  rfl

namespace Path

/-- A path constructed from a continuous map `f` has the same underlying function. -/
@[simp]
/-
**Path.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：coe_mk' (f : C(I, X)) (h₁ h₂) : ⇑(mk f h₁ h₂ : Path x y) = f
参数：f : C(I, X)；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path constructed from a continuous map `f` has the same underlying function.
-/
theorem coe_mk' (f : C(I, X)) (h₁ h₂) : ⇑(mk f h₁ h₂ : Path x y) = f := rfl
/-
**Path.coe_mk_mk** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：coe_mk_mk (f : I -> X) (h₁) (h₂ : f 0 = x) (h₃ : f 1 = y) : ⇑(mk ⟨f, h₁⟩ h
₂ h₃ : Path x y) = f
参数：f : I -> X；h₁；h₂ : f 0 = x；h₃ : f 1 = y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk_mk (f : I → X) (h₁) (h₂ : f 0 = x) (h₃ : f 1 = y) :
    ⇑(mk ⟨f, h₁⟩ h₂ h₃ : Path x y) = f :=
  rfl

variable (γ : Path x y)

@[continuity]
/-
**Path.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ : Path x y), Con
tinuous ⇑γ
参数：γ : Path x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
-/
protected theorem continuous : Continuous γ :=
  γ.continuous_toFun

@[simp, grind =]
/-
**Path.source** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ : Path x y), γ 0
 = x
参数：γ : Path x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.source'`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (se
lf : Path x y), self.toFun 0 = x
-/
protected theorem source : γ 0 = x :=
  γ.source'

@[simp, grind =]
/-
**Path.target** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ : Path x y), γ 1
 = y
参数：γ : Path x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.target'`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (se
lf : Path x y), self.toFun 1 = y
-/
protected theorem target : γ 1 = y :=
  γ.target'

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
/-
**Path.simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `Path.simps`。
形式化陈述：{X : Type u_1} → [inst : TopologicalSpace X] → {x y : X} → Path x y → ↑uni
tInterval → X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
because it is a composition of multiple projections.
-/
def simps.apply : I → X :=
  γ

initialize_simps_projections Path (toFun → simps.apply, -toContinuousMap)

@[simp]
/-
**Path.coe_toContinuousMap** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：coe_toContinuousMap : ⇑γ.toContinuousMap = γ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousMap : ⇑γ.toContinuousMap = γ :=
  rfl

@[simp]
/-
**Path.range_coe** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：range_coe : range ((↑) : Path x y -> C(I, X)) = {f | f 0 = x ∧ f 1 = y}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y
-/
theorem range_coe : range ((↑) : Path x y → C(I, X)) = {f | f 0 = x ∧ f 1 = y} :=
  Subset.antisymm (range_subset_iff.mpr fun γ ↦ ⟨γ.source, γ.target⟩) fun f ⟨hf₀, hf₁⟩ ↦
    ⟨⟨f, hf₀, hf₁⟩, rfl⟩

/-- Any function `φ : Π (a : α), Path (x a) (y a)` can be seen as a function `α × I → X`. -/
/-
**Path.instHasUncurryPath** 是 Mathlib 中的一个实例，位于命名空间 `Path`。
形式化陈述：instHasUncurryPath {α : Type*} {x y : α -> X} : HasUncurry (forall a : α, 
Path (x a) (y a)) (α × I) X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any function `φ : Π (a : α), Path (x a) (y a)` can be seen as a function `α × I 
→ X`.
-/
instance instHasUncurryPath {α : Type*} {x y : α → X} :
    HasUncurry (∀ a : α, Path (x a) (y a)) (α × I) X :=
  ⟨fun φ p => φ p.1 p.2⟩

@[simp high, grind! .]
/-
**Path.source_mem_range** 是 Mathlib 中的一个引理，位于命名空间 `Path`。
形式化陈述：source_mem_range (γ : Path x y) : x in range ⇑γ
参数：γ : Path x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
-/
lemma source_mem_range (γ : Path x y) : x ∈ range ⇑γ :=
  ⟨0, Path.source γ⟩

@[simp high, grind! .]
/-
**Path.target_mem_range** 是 Mathlib 中的一个引理，位于命名空间 `Path`。
形式化陈述：target_mem_range (γ : Path x y) : y in range ⇑γ
参数：γ : Path x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y
-/
lemma target_mem_range (γ : Path x y) : y ∈ range ⇑γ :=
  ⟨1, Path.target γ⟩

/-- The path 0 ⟶ 1 in `I` -/
@[simps!]
/-
**Path.id** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：Path 0 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The path 0 ⟶ 1 in `I`
-/
protected def id : Path (0 : I) 1 where
  toContinuousMap := .id _
  source' := rfl
  target' := rfl

/-- The constant path from a point to itself -/
@[refl, simps! (attr := grind =)]
/-
**Path.refl** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：refl (x : X) : Path x x where toContinuousMap
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant path from a point to itself
-/
def refl (x : X) : Path x x where
  toContinuousMap := .const I x
  source' := rfl
  target' := rfl

@[simp]
/-
**Path.refl_range** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：refl_range {a : X} : range (Path.refl a) = {a}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_const`：range_const : forall [Nonempty ι] {c : α}, (range fun _
 : ι => c) = {c}
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `unitInterval.instNontrivialElemReal`：Nontrivial ↑unitInterval
-/
theorem refl_range {a : X} : range (Path.refl a) = {a} := range_const

/-- The reverse of a path from `x` to `y`, as a path from `y` to `x` -/
@[symm, simps (attr := grind =)]
/-
**Path.symm** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：symm (γ : Path x y) : Path y x where toFun
参数：γ : Path x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reverse of a path from `x` to `y`, as a path from `y` to `x`
-/
def symm (γ : Path x y) : Path y x where
  toFun := γ ∘ σ
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp]
/-
**Path.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：symm_symm (γ : Path x y) : γ.symm.symm = γ
参数：γ : Path x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (γ : Path x y) : γ.symm.symm = γ := by grind
/-
**Path.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：symm_bijective : Function.Bijective (Path.symm : Path x y -> Path y x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `Path.symm_symm`：symm_symm (γ : Path x y) : γ.symm.symm = γ
-/
theorem symm_bijective : Function.Bijective (Path.symm : Path x y → Path y x) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/-
**Path.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：refl_symm {a : X} : (Path.refl a).symm = Path.refl a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm {a : X} : (Path.refl a).symm = Path.refl a := rfl

@[simp]
/-
**Path.symm_range** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：symm_range {a b : X} (γ : Path a b) : range γ.symm = range γ
参数：γ : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_comp`：∀ {α : Type u_1} {ι : Sort u_3} {ι' : So
rt u_4} {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α), Set.range (g ∘ f
) = Set.range g
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用定理 `unitInterval.symm_involutive`：symm_involutive : Function.Involutive (sym
m : I -> I)
-/
theorem symm_range {a b : X} (γ : Path a b) : range γ.symm = range γ :=
  symm_involutive.surjective.range_comp γ

/-! #### Space of paths -/


open ContinuousMap

/-- The following instance defines the topology on the path space to be induced from the
compact-open topology on the space `C(I,X)` of continuous maps from `I` to `X`.
-/
/-
**Path.instTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `Path`。
形式化陈述：instTopologicalSpace : TopologicalSpace (Path x y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The following instance defines the topology on the path space to be induced from
 the
compact-open topology on the space `C(I,X)` of continuous maps from `I` to `X`.
-/
instance instTopologicalSpace : TopologicalSpace (Path x y) :=
  TopologicalSpace.induced ((↑) : _ → C(I, X)) ContinuousMap.compactOpen
/-
**Path.** 是 Mathlib 中的一个实例，位于命名空间 `Path`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousEval (Path x y) I X := .of_continuous_forget continuous_induced_dom
/-
**Path.continuous_uncurry_iff** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：continuous_uncurry_iff {Y} [TopologicalSpace Y] {g : Y -> Path x y} : Cont
inuous ↿g ↔ Continuous g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `ContinuousMap.continuous_uncurry_of_continuous`：continuous_uncurry_of_co
ntinuous [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) : Continuous (Function.uncu
rry fun x y => f x y)
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `proper_of_compact`：∀ {α : Type u} [inst : PseudoMetricSpace α] [CompactS
pace α], ProperSpace α
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ContinuousMap.continuous_of_continuous_uncurry`：continuous_of_continuous
_uncurry (f : X -> C(Y, Z)) (h : Continuous (Function.uncurry fun x y => f x y))
 : Continuous f
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
-/
theorem continuous_uncurry_iff {Y} [TopologicalSpace Y] {g : Y → Path x y} :
    Continuous ↿g ↔ Continuous g :=
  Iff.symm <| continuous_induced_rng.trans
    ⟨fun h => continuous_uncurry_of_continuous ⟨_, h⟩,
    continuous_of_continuous_uncurry (fun (y : Y) ↦ ContinuousMap.mk (g y))⟩

/-- A continuous map extending a path to `ℝ`, constant before `0` and after `1`. -/
/-
**Path.extend** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：extend : C(Real, X) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous map extending a path to `ℝ`, constant before `0` and after `1`.
-/
def extend : C(ℝ, X) where
  toFun := IccExtend zero_le_one γ

/-- See Note [continuity lemma statement]. -/
@[continuity, fun_prop]
/-
**Path._root_.Continuous.pathExtend** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [continuity lemma statement].
-/
theorem _root_.Continuous.pathExtend {γ : Y → Path x y} {f : Y → ℝ} (hγ : Continuous ↿γ)
    (hf : Continuous f) : Continuous fun t => (γ t).extend (f t) :=
  Continuous.IccExtend hγ hf

/-- A useful special case of `Continuous.path_extend`. -/
/-
**Path.continuous_extend** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：continuous_extend : Continuous γ.extend
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.Icc_extend'`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOr
der α] {a b : α} {h : a ≤ b} [inst_1 : TopologicalSpace α]   [OrderTopology α] [
inst_3 : Top…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Path.continuous`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} 
(γ : Path x y), Continuous ⇑γ

--- 原说明 ---
A useful special case of `Continuous.path_extend`.
-/
theorem continuous_extend : Continuous γ.extend :=
  γ.continuous.Icc_extend'
/-
**Path._root_.Filter.Tendsto.pathExtend** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.Tendsto.pathExtend
    {l r : Y → X} {y : Y} {l₁ : Filter ℝ} {l₂ : Filter X} {γ : ∀ y, Path (l y) (r y)}
    (hγ : Tendsto ↿γ (𝓝 y ×ˢ l₁.map (projIcc 0 1 zero_le_one)) l₂) :
    Tendsto (↿fun x => ⇑(γ x).extend) (𝓝 y ×ˢ l₁) l₂ :=
  Filter.Tendsto.IccExtend _ hγ
/-
**Path._root_.ContinuousAt.pathExtend** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousAt.pathExtend {g : Y → ℝ} {l r : Y → X} (γ : ∀ y, Path (l y) (r y))
    {y : Y} (hγ : ContinuousAt ↿γ (y, projIcc 0 1 zero_le_one (g y))) (hg : ContinuousAt g y) :
    ContinuousAt (fun i => (γ i).extend (g i)) y :=
  hγ.IccExtend (fun x => γ x) hg

@[simp, grind =]
/-
**Path.extend_apply** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：extend_apply {a b : X} (γ : Path a b) {t : Real} (ht : t in (Icc 0 1 : Set
 Real)) : γ.extend t = γ ⟨t, ht⟩
参数：γ : Path a b；ht : t in (Icc 0 1 : Set Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IccExtend_of_mem`：IccExtend_of_mem (f : Icc a b -> β) (hx : x in Icc
 a b) : IccExtend h f x = f ⟨x, hx⟩
-/
theorem extend_apply {a b : X} (γ : Path a b) {t : ℝ}
    (ht : t ∈ (Icc 0 1 : Set ℝ)) : γ.extend t = γ ⟨t, ht⟩ :=
  IccExtend_of_mem _ γ ht
/-
**Path.extend_zero** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：extend_zero : γ.extend 0 = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Path.extend_apply`：extend_apply {a b : X} (γ : Path a b) {t : Real} (ht 
: t in (Icc 0 1 : Set Real)) : γ.extend t = γ ⟨t, ht⟩
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extend_zero : γ.extend 0 = x := by simp
/-
**Path.extend_one** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：extend_one : γ.extend 1 = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Path.extend_apply`：extend_apply {a b : X} (γ : Path a b) {t : Real} (ht 
: t in (Icc 0 1 : Set Real)) : γ.extend t = γ ⟨t, ht⟩
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extend_one : γ.extend 1 = y := by simp
/-
**Path.extend_extends'** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：extend_extends' {a b : X} (γ : Path a b) (t : (Icc 0 1 : Set Real)) : γ.ex
tend t = γ t
参数：γ : Path a b；t : (Icc 0 1 : Set Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IccExtend_val`：IccExtend_val (f : Icc a b -> β) (x : Icc a b) : IccE
xtend h f x = f x
-/
theorem extend_extends' {a b : X} (γ : Path a b) (t : (Icc 0 1 : Set ℝ)) : γ.extend t = γ t :=
  IccExtend_val _ γ t

@[simp]
/-
**Path.extend_range** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：extend_range {a b : X} (γ : Path a b) : range γ.extend = range γ
参数：γ : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IccExtend_range`：IccExtend_range (f : Icc a b -> β) : range (IccExte
nd h f) = range f
-/
theorem extend_range {a b : X} (γ : Path a b) :
    range γ.extend = range γ :=
  IccExtend_range _ γ
/-
**Path.image_extend_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：image_extend_of_subset (γ : Path x y) {s : Set Real} (h : I subseteq s) : 
γ.extend '' s = range γ
参数：γ : Path x y；h : I subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Path.extend_range`：extend_range {a b : X} (γ : Path a b) : range γ.exten
d = range γ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Path.extend_extends'`：extend_extends' {a b : X} (γ : Path a b) (t : (Icc
 0 1 : Set Real)) : γ.extend t = γ t
-/
theorem image_extend_of_subset (γ : Path x y) {s : Set ℝ} (h : I ⊆ s) :
    γ.extend '' s = range γ :=
  (γ.extend_range ▸ image_subset_range _ _).antisymm <| range_subset_iff.mpr <| fun t ↦
    ⟨t, h t.2, extend_extends' _ _⟩
/-
**Path.extend_of_le_zero** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：extend_of_le_zero {a b : X} (γ : Path a b) {t : Real} (ht : t <= 0) : γ.ex
tend t = a
参数：γ : Path a b；ht : t <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Set.IccExtend_of_le_left`：IccExtend_of_le_left (f : Icc a b -> β) (hx : 
x <= a) : IccExtend h f x = f ⟨a, left_mem_Icc.2 h⟩
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
-/
theorem extend_of_le_zero {a b : X} (γ : Path a b) {t : ℝ}
    (ht : t ≤ 0) : γ.extend t = a :=
  (IccExtend_of_le_left _ _ ht).trans γ.source
/-
**Path.extend_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：extend_of_one_le {a b : X} (γ : Path a b) {t : Real} (ht : 1 <= t) : γ.ext
end t = b
参数：γ : Path a b；ht : 1 <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `Set.IccExtend_of_right_le`：IccExtend_of_right_le (f : Icc a b -> β) (hx 
: b <= x) : IccExtend h f x = f ⟨b, right_mem_Icc.2 h⟩
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y
-/
theorem extend_of_one_le {a b : X} (γ : Path a b) {t : ℝ}
    (ht : 1 ≤ t) : γ.extend t = b :=
  (IccExtend_of_right_le _ _ ht).trans γ.target

@[simp]
/-
**Path.refl_extend** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：refl_extend {a : X} : (Path.refl a).extend = .const Real a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_extend {a : X} : (Path.refl a).extend = .const ℝ a :=
  rfl
/-
**Path.extend_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：extend_symm_apply (γ : Path x y) (t : Real) : γ.symm.extend t = γ.extend (
1 - t)
参数：γ : Path x y；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `unitInterval.symm_projIcc`：symm_projIcc (x : Real) : symm (projIcc 0 1 z
ero_le_one x) = projIcc 0 1 zero_le_one (1 - x)
-/
theorem extend_symm_apply (γ : Path x y) (t : ℝ) : γ.symm.extend t = γ.extend (1 - t) :=
  congrArg γ <| symm_projIcc _

@[simp]
/-
**Path.extend_symm** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：extend_symm (γ : Path x y) : γ.symm.extend = (γ.extend <| 1 - ·)
参数：γ : Path x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Path.extend_symm_apply`：extend_symm_apply (γ : Path x y) (t : Real) : γ.
symm.extend t = γ.extend (1 - t)
-/
theorem extend_symm (γ : Path x y) : γ.symm.extend = (γ.extend <| 1 - ·) :=
  funext γ.extend_symm_apply

/-- The path obtained from a map defined on `ℝ` by restriction to the unit interval. -/
/-
**Path.ofLine** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：ofLine {f : Real -> X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = 
y) : Path x y where toFun
参数：hf : ContinuousOn f I；h₀ : f 0 = x；h₁ : f 1 = y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The path obtained from a map defined on `ℝ` by restriction to the unit interval.
-/
def ofLine {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) : Path x y where
  toFun := f ∘ ((↑) : unitInterval → ℝ)
  continuous_toFun := hf.comp_continuous continuous_subtype_val Subtype.prop
  source' := h₀
  target' := h₁
/-
**Path.ofLine_mem** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：ofLine_mem {f : Real -> X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 
1 = y) : forall t, ofLine hf h₀ h₁ t in f '' I
参数：hf : ContinuousOn f I；h₀ : f 0 = x；h₁ : f 1 = y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLine_mem {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) :
    ∀ t, ofLine hf h₀ h₁ t ∈ f '' I := fun ⟨t, t_in⟩ => ⟨t, t_in, rfl⟩

@[simp]
/-
**Path.ofLine_extend** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：ofLine_extend (γ : Path x y) : ofLine (by fun_prop) (extend_zero γ) (exten
d_one γ) = γ
参数：γ : Path x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `Path.extend_zero`：extend_zero : γ.extend 0 = x
· 使用定理 `Path.extend_one`：extend_one : γ.extend 1 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.extend_apply`：extend_apply {a b : X} (γ : Path a b) {t : Real} (ht 
: t in (Icc 0 1 : Set Real)) : γ.extend t = γ ⟨t, ht⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofLine_extend (γ : Path x y) : ofLine (by fun_prop) (extend_zero γ) (extend_one γ) = γ := by
  ext t
  simp [ofLine]

attribute [local simp] Iic_def

/-- Concatenation of two paths from `x` to `y` and from `y` to `z`, putting the first
path on `[0, 1/2]` and the second one on `[1/2, 1]`. -/
@[trans]
/-
**Path.trans** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：trans (γ : Path x y) (γ' : Path y z) : Path x z where toFun
参数：γ : Path x y；γ' : Path y z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Concatenation of two paths from `x` to `y` and from `y` to `z`, putting the firs
t
path on `[0, 1/2]` and the second one on `[1/2, 1]`.
-/
def trans (γ : Path x y) (γ' : Path y z) : Path x z where
  toFun := (fun t : ℝ => if t ≤ 1 / 2 then γ.extend (2 * t) else γ'.extend (2 * t - 1)) ∘ (↑)
  continuous_toFun := by
    refine
      (Continuous.if_le ?_ ?_ continuous_id continuous_const (by simp)).comp
        continuous_subtype_val <;>
    fun_prop
  source' := by simp
  target' := by norm_num

@[grind =]
/-
**Path.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：trans_apply (γ : Path x y) (γ' : Path y z) (t : I) : (γ.trans γ') t = if h
 : (t : Real) <= 1 / 2 then γ ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩
⟩ else γ' ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩
参数：γ : Path x y；γ' : Path y z；t : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `unitInterval.mul_pos_mem_iff`：mul_pos_mem_iff {a t : Real} (ha : 0 < a) 
: a * t in I ↔ t in Set.Icc (0 : Real) (1 / a)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `unitInterval.two_mul_sub_one_mem_iff`：two_mul_sub_one_mem_iff {t : Real}
 : 2 * t - 1 in I ↔ t in Set.Icc (1 / 2 : Real) 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Path.extend_apply`：extend_apply {a b : X} (γ : Path a b) {t : Real} (ht 
: t in (Icc 0 1 : Set Real)) : γ.extend t = γ ⟨t, ht⟩
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem trans_apply (γ : Path x y) (γ' : Path y z) (t : I) :
    (γ.trans γ') t =
      if h : (t : ℝ) ≤ 1 / 2 then γ ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else γ' ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩ :=
  show ite _ _ _ = _ by split_ifs <;> rw [extend_apply]

@[simp]
/-
**Path.trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：trans_symm (γ : Path x y) (γ' : Path y z) : (γ.trans γ').symm = γ'.symm.tr
ans γ.symm
参数：γ : Path x y；γ' : Path y z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `unitInterval.mul_pos_mem_iff`：mul_pos_mem_iff {a t : Real} (ha : 0 < a) 
: a * t in I ↔ t in Set.Icc (0 : Real) (1 / a)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `unitInterval.two_mul_sub_one_mem_iff`：two_mul_sub_one_mem_iff {t : Real}
 : 2 * t - 1 in I ↔ t in Set.Icc (1 / 2 : Real) 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Path.symm_apply`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} 
(γ : Path x y) (a : ↑unitInterval),   γ.symm a = (⇑γ ∘ unitInterval.symm) a
· 使用定理 `Path.trans_apply`：trans_apply (γ : Path x y) (γ' : Path y z) (t : I) : (
γ.trans γ') t = if h : (t : Real) <= 1 / 2 then γ ⟨2 * t, (mul_pos_mem_iff zero_
lt_two…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
（共 103 条，此处仅展示前 30 条）
-/
theorem trans_symm (γ : Path x y) (γ' : Path y z) : (γ.trans γ').symm = γ'.symm.trans γ.symm := by
  ext t
  simp only [trans_apply, symm_apply, Function.comp_apply]
  split_ifs with h h₁ h₂ <;> rw [coe_symm_eq] at h
  · have ht : (t : ℝ) = 1 / 2 := by linarith
    norm_num [ht]
  · refine congr_arg _ (Subtype.ext ?_)
    norm_num [sub_sub_eq_add_sub, mul_sub]
  · refine congr_arg _ (Subtype.ext ?_)
    simp only [coe_symm_eq]
    ring
  · exfalso
    linarith
/-
**Path.extend_trans_of_le_half** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：extend_trans_of_le_half (γ₁ : Path x y) (γ₂ : Path y z) {t : Real} (ht : t
 <= 1 / 2) : (γ₁.trans γ₂).extend t = γ₁.extend (2 * t)
参数：γ₁ : Path x y；γ₂ : Path y z；ht : t <= 1 / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.extend_of_le_zero`：extend_of_le_zero {a b : X} (γ : Path a b) {t : 
Real} (ht : t <= 0) : γ.extend t = a
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 83 条，此处仅展示前 30 条）
-/
theorem extend_trans_of_le_half (γ₁ : Path x y) (γ₂ : Path y z) {t : ℝ} (ht : t ≤ 1 / 2) :
    (γ₁.trans γ₂).extend t = γ₁.extend (2 * t) := by
  obtain _ | ht₀ := le_total t 0
  · repeat rw [extend_of_le_zero _ (by linarith)]
  · rwa [extend_apply _ ⟨ht₀, by linarith⟩, trans_apply, dif_pos, extend_apply]
/-
**Path.extend_trans_of_half_le** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：extend_trans_of_half_le (γ₁ : Path x y) (γ₂ : Path y z) {t : Real} (ht : 1
 / 2 <= t) : (γ₁.trans γ₂).extend t = γ₂.extend (2 * t - 1)
参数：γ₁ : Path x y；γ₂ : Path y z；ht : 1 / 2 <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `Path.extend_symm_apply`：extend_symm_apply (γ : Path x y) (t : Real) : γ.
symm.extend t = γ.extend (1 - t)
· 使用定理 `Path.trans_symm`：trans_symm (γ : Path x y) (γ' : Path y z) : (γ.trans γ'
).symm = γ'.symm.trans γ.symm
· 使用定理 `Path.extend_trans_of_le_half`：extend_trans_of_le_half (γ₁ : Path x y) (γ
₂ : Path y z) {t : Real} (ht : t <= 1 / 2) : (γ₁.trans γ₂).extend t = γ₁.extend 
(2 * t)
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 70 条，此处仅展示前 30 条）
-/
theorem extend_trans_of_half_le (γ₁ : Path x y) (γ₂ : Path y z) {t : ℝ} (ht : 1 / 2 ≤ t) :
    (γ₁.trans γ₂).extend t = γ₂.extend (2 * t - 1) := by
  conv_lhs => rw [← sub_sub_cancel 1 t]
  rw [← extend_symm_apply, trans_symm, extend_trans_of_le_half _ _ (by linarith), extend_symm_apply]
  congr 1
  linarith

@[simp]
/-
**Path.refl_trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：refl_trans_refl {a : X} : (Path.refl a).trans (Path.refl a) = Path.refl a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `ContinuousMap.mk.congr_simp`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (toFun toFun_1 : X → Y)   (e_toFu
n : toFun = toFun…
· 使用定理 `Path.mk.congr_simp`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : 
X} (toContinuousMap toContinuousMap_1 : C(↑unitInterval, X))   (e_toContinuousMa
p : toCo…
· 使用定理 `Path.refl_apply`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (x
_1 : ↑unitInterval), (Path.refl x) x_1 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem refl_trans_refl {a : X} :
    (Path.refl a).trans (Path.refl a) = Path.refl a := by
  ext
  simp [Path.trans]
/-
**Path.trans_range** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：trans_range {a b c : X} (γ₁ : Path a b) (γ₂ : Path b c) : range (γ₁.trans 
γ₂) = range γ₁ union range γ₂
参数：γ₁ : Path a b；γ₂ : Path b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Path.extend_range`：extend_range {a b : X} (γ : Path a b) : range γ.exten
d = range γ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.Iic_union_Ici`：Iic_union_Ici : Iic a union Ici a = univ
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `Set.EqOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : 
α → β}, Set.EqOn f₁ f₂ s → f₁ '' s = f₂ '' s
· 使用定理 `Path.extend_trans_of_le_half`：extend_trans_of_le_half (γ₁ : Path x y) (γ
₂ : Path y z) {t : Real} (ht : t <= 1 / 2) : (γ₁.trans γ₂).extend t = γ₁.extend 
(2 * t)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic
 b ↔ x ≤ b
· 使用定理 `Path.extend_trans_of_half_le`：extend_trans_of_half_le (γ₁ : Path x y) (γ
₂ : Path y z) {t : Real} (ht : 1 / 2 <= t) : (γ₁.trans γ₂).extend t = γ₂.extend 
(2 * t - 1)
· 使用定理 `Set.mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ici
 b ↔ b ≤ x
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Set.image_mul_left_Iic`：image_mul_left_Iic (h : 0 < a) (b : G₀) : (a * ·
) '' Iic b = Iic (a * b)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
（共 44 条，此处仅展示前 30 条）
-/
theorem trans_range {a b c : X} (γ₁ : Path a b) (γ₂ : Path b c) :
    range (γ₁.trans γ₂) = range γ₁ ∪ range γ₂ := by
  rw [← extend_range, ← image_univ, ← Iic_union_Ici (a := 1 / 2), image_union,
    EqOn.image_eq fun t ht ↦ extend_trans_of_le_half _ _ (mem_Iic.1 ht),
    EqOn.image_eq fun t ht ↦ extend_trans_of_half_le _ _ (mem_Ici.1 ht),
    ← image_image γ₁.extend, ← image_image (γ₂.extend <| · - 1), ← image_image γ₂.extend]
  norm_num [image_mul_left_Ici, image_mul_left_Iic,
    image_extend_of_subset, Icc_subset_Iic_self, Icc_subset_Ici_self]

/-- Image of a path from `x` to `y` by a map which is continuous on the path. -/
/-
**Path.map'** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：map' (γ : Path x y) {f : X -> Y} (h : ContinuousOn f (range γ)) : Path (f 
x) (f y) where toFun
参数：γ : Path x y；h : ContinuousOn f (range γ)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Image of a path from `x` to `y` by a map which is continuous on the path.
-/
def map' (γ : Path x y) {f : X → Y} (h : ContinuousOn f (range γ)) : Path (f x) (f y) where
  toFun := f ∘ γ
  continuous_toFun := h.comp_continuous γ.continuous (fun x ↦ mem_range_self x)
  source' := by simp
  target' := by simp

/-- Image of a path from `x` to `y` by a continuous map -/
/-
**Path.map** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：map (γ : Path x y) {f : X -> Y} (h : Continuous f) : Path (f x) (f y)
参数：γ : Path x y；h : Continuous f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Image of a path from `x` to `y` by a continuous map
-/
def map (γ : Path x y) {f : X → Y} (h : Continuous f) :
    Path (f x) (f y) := γ.map' h.continuousOn

@[simp, grind =]
/-
**Path.map_coe** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：map_coe (γ : Path x y) {f : X -> Y} (h : Continuous f) : (γ.map h : I -> Y
) = f ∘ γ
参数：γ : Path x y；h : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem map_coe (γ : Path x y) {f : X → Y} (h : Continuous f) :
    (γ.map h : I → Y) = f ∘ γ := by
  ext t
  rfl

@[simp]
/-
**Path.map_symm** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：map_symm (γ : Path x y) {f : X -> Y} (h : Continuous f) : (γ.map h).symm =
 γ.symm.map h
参数：γ : Path x y；h : Continuous f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_symm (γ : Path x y) {f : X → Y} (h : Continuous f) :
    (γ.map h).symm = γ.symm.map h :=
  rfl

@[simp]
/-
**Path.map_trans** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：map_trans (γ : Path x y) (γ' : Path y z) {f : X -> Y} (h : Continuous f) :
 (γ.trans γ').map h = (γ.map h).trans (γ'.map h)
参数：γ : Path x y；γ' : Path y z；h : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `unitInterval.mul_pos_mem_iff`：mul_pos_mem_iff {a t : Real} (ha : 0 < a) 
: a * t in I ↔ t in Set.Icc (0 : Real) (1 / a)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `unitInterval.two_mul_sub_one_mem_iff`：two_mul_sub_one_mem_iff {t : Real}
 : 2 * t - 1 in I ↔ t in Set.Icc (1 / 2 : Real) 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.trans_apply`：trans_apply (γ : Path x y) (γ' : Path y z) (t : I) : (
γ.trans γ') t = if h : (t : Real) <= 1 / 2 then γ ⟨2 * t, (mul_pos_mem_iff zero_
lt_two…
· 使用定理 `Path.map_coe`：map_coe (γ : Path x y) {f : X -> Y} (h : Continuous f) : (
γ.map h : I -> Y) = f ∘ γ
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem map_trans (γ : Path x y) (γ' : Path y z) {f : X → Y}
    (h : Continuous f) : (γ.trans γ').map h = (γ.map h).trans (γ'.map h) := by
  ext t
  rw [trans_apply, map_coe, Function.comp_apply, trans_apply, map_coe, map_coe]
  grind

@[simp]
/-
**Path.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：map_id (γ : Path x y) : γ.map continuous_id = γ
参数：γ : Path x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem map_id (γ : Path x y) : γ.map continuous_id = γ := by
  ext
  rfl

@[simp]
/-
**Path.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：map_map (γ : Path x y) {Z : Type*} [TopologicalSpace Z] {f : X -> Y} (hf :
 Continuous f) {g : Y -> Z} (hg : Continuous g) : (γ.map hf).map hg = γ.map (hg.
comp hf)
参数：γ : Path x y；hf : Continuous f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem map_map (γ : Path x y) {Z : Type*} [TopologicalSpace Z]
    {f : X → Y} (hf : Continuous f) {g : Y → Z} (hg : Continuous g) :
    (γ.map hf).map hg = γ.map (hg.comp hf) := by
  ext
  rfl

/-- Casting a path from `x` to `y` to a path from `x'` to `y'` when `x' = x` and `y' = y` -/
/-
**Path.cast** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：Path.cast {u v u' v' : U} (hu : u = u') (hv : v = v') (p : Path u v) : Pat
h u' v'
参数：hu : u = u'；hv : v = v'；p : Path u v。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Path.continuous`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} 
(γ : Path x y), Continuous ⇑γ

--- 原说明 ---
Casting a path from `x` to `y` to a path from `x'` to `y'` when `x' = x` and `y'
 = y`
-/
def cast (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : Path x' y' where
  toFun := γ
  continuous_toFun := γ.continuous
  source' := by simp [hx]
  target' := by simp [hy]
/-
**Path.cast_rfl_rfl** 是 Mathlib 中的一个定理，位于命名空间 `Quiver`。
形式化陈述：Path.cast_rfl_rfl {u v : U} (p : Path u v) : p.cast rfl rfl = p
参数：p : Path u v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem cast_rfl_rfl (γ : Path x y) : γ.cast rfl rfl = γ := rfl

@[simp]
/-
**Path.cast_symm** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：cast_symm {a₁ a₂ b₁ b₂ : X} (γ : Path a₂ b₂) (ha : a₁ = a₂) (hb : b₁ = b₂)
 : (γ.symm).cast hb ha = (γ.cast ha hb).symm
参数：γ : Path a₂ b₂；ha : a₁ = a₂；hb : b₁ = b₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_symm {a₁ a₂ b₁ b₂ : X} (γ : Path a₂ b₂) (ha : a₁ = a₂) (hb : b₁ = b₂) :
    (γ.symm).cast hb ha = (γ.cast ha hb).symm :=
  rfl

@[simp]
/-
**Path.cast_trans** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：cast_trans {a₁ a₂ b₁ b₂ c₁ c₂ : X} (γ : Path a₂ b₂) (γ' : Path b₂ c₂) (ha 
: a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) : (γ.trans γ').cast ha hc = (γ.cast ha 
hb).trans (γ'.cast hb hc)
参数：γ : Path a₂ b₂；γ' : Path b₂ c₂；ha : a₁ = a₂；hb : b₁ = b₂；hc : c₁ = c₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_trans {a₁ a₂ b₁ b₂ c₁ c₂ : X} (γ : Path a₂ b₂)
    (γ' : Path b₂ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) :
    (γ.trans γ').cast ha hc = (γ.cast ha hb).trans (γ'.cast hb hc) :=
  rfl

@[simp]
/-
**Path.extend_cast** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：extend_cast {x' y'} (γ : Path x y) (hx : x' = x) (hy : y' = y) : (γ.cast h
x hy).extend = γ.extend
参数：γ : Path x y；hx : x' = x；hy : y' = y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extend_cast {x' y'} (γ : Path x y) (hx : x' = x) (hy : y' = y) :
    (γ.cast hx hy).extend = γ.extend := rfl

@[simp]
/-
**Path.cast_coe** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：cast_coe (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : (γ.cast hx h
y : I -> X) = γ
参数：γ : Path x y；hx : x' = x；hy : y' = y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_coe (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : (γ.cast hx hy : I → X) = γ :=
  rfl
/-
**Path.bijective_cast** 是 Mathlib 中的一个引理，位于命名空间 `Path`。
形式化陈述：bijective_cast {x' y' : X} (hx : x' = x) (hy : y' = y) : Bijective (Path.c
ast · hx hy)
参数：hx : x' = x；hy : y' = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
lemma bijective_cast {x' y' : X} (hx : x' = x) (hy : y' = y) : Bijective (Path.cast · hx hy) := by
  subst_vars; exact bijective_id

@[congr]
/-
**Path.exists_congr** 是 Mathlib 中的一个引理，位于命名空间 `Path`。
形式化陈述：exists_congr {x₁ x₂ y₁ y₂ : X} {p : Path x₁ y₁ -> Prop} (hx : x₁ = x₂) (hy
 : y₁ = y₂) : (exists γ, p γ) ↔ (exists (γ : Path x₂ y₂), p (γ.cast hx hy))
参数：hx : x₁ = x₂；hy : y₁ = y₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用引理 `Path.bijective_cast`：bijective_cast {x' y' : X} (hx : x' = x) (hy : y' =
 y) : Bijective (Path.cast · hx hy)
-/
lemma exists_congr {x₁ x₂ y₁ y₂ : X} {p : Path x₁ y₁ → Prop}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (∃ γ, p γ) ↔ (∃ (γ : Path x₂ y₂), p (γ.cast hx hy)) :=
  bijective_cast hx hy |>.surjective.exists

@[continuity, fun_prop]
/-
**Path.symm_continuous_family** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：symm_continuous_family {ι : Type*} [TopologicalSpace ι] {a b : ι -> X} (γ 
: forall t : ι, Path (a t) (b t)) (h : Continuous ↿γ) : Continuous ↿fun t => (γ 
t).symm
参数：γ : forall t : ι, Path (a t) (b t)；h : Continuous ↿γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `unitInterval.continuous_symm`：continuous_symm : Continuous σ
-/
theorem symm_continuous_family {ι : Type*} [TopologicalSpace ι]
    {a b : ι → X} (γ : ∀ t : ι, Path (a t) (b t)) (h : Continuous ↿γ) :
    Continuous ↿fun t => (γ t).symm :=
  h.comp (continuous_id.prodMap continuous_symm)

@[continuity]
/-
**Path.continuous_symm** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：continuous_symm : Continuous (symm : Path x y -> Path y x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Path.continuous_uncurry_iff`：continuous_uncurry_iff {Y} [TopologicalSpac
e Y] {g : Y -> Path x y} : Continuous ↿g ↔ Continuous g
· 使用定理 `Path.symm_continuous_family`：symm_continuous_family {ι : Type*} [Topolog
icalSpace ι] {a b : ι -> X} (γ : forall t : ι, Path (a t) (b t)) (h : Continuous
 ↿γ) : Continuous…
· 使用定理 `Continuous.eval`：∀ {F : Type u_1} {X : Type u_2} {Y : Type u_3} {Z : Typ
e u_4} [inst : FunLike F X Y] [inst_1 : TopologicalSpace F]   [inst_2 : Topologi
calSp…
· 使用定理 `Path.instContinuousEvalElemRealUnitInterval`：∀ {X : Type u_1} [inst : To
pologicalSpace X] {x y : X}, ContinuousEval (Path x y) (↑unitInterval) X
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
theorem continuous_symm : Continuous (symm : Path x y → Path y x) :=
  continuous_uncurry_iff.mp <| symm_continuous_family _ (by fun_prop)

@[continuity]
/-
**Path.continuous_uncurry_extend_of_continuous_family** 是 Mathlib 中的一个定理，位于命名空间 
`Path`。
形式化陈述：continuous_uncurry_extend_of_continuous_family {ι : Type*} [TopologicalSpa
ce ι] {a b : ι -> X} (γ : forall t : ι, Path (a t) (b t)) (h : Continuous ↿γ) : 
Continuous ↿fun t => ⇑(γ t).extend
参数：γ : forall t : ι, Path (a t) (b t)；h : Continuous ↿γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_projIcc`：continuous_projIcc : Continuous (projIcc a b h)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem continuous_uncurry_extend_of_continuous_family {ι : Type*} [TopologicalSpace ι]
    {a b : ι → X} (γ : ∀ t : ι, Path (a t) (b t)) (h : Continuous ↿γ) :
    Continuous ↿fun t => ⇑(γ t).extend := by
  apply h.comp (continuous_id.prodMap continuous_projIcc)
  exact zero_le_one

@[continuity]
/-
**Path.trans_continuous_family** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：trans_continuous_family {ι : Type*} [TopologicalSpace ι] {a b c : ι -> X} 
(γ₁ : forall t : ι, Path (a t) (b t)) (h₁ : Continuous ↿γ₁) (γ₂ : forall t : ι, 
Path (b t) (c t)) (h₂ : Continuous ↿γ₂) : Continuous ↿fun t => (γ₁ t).trans (γ₂ 
t)
参数：γ₁ : forall t : ι, Path (a t) (b t)；h₁ : Continuous ↿γ₁；γ₂ : forall t : ι, Pa
th (b t) (c t)；h₂ : Continuous ↿γ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.continuous_uncurry_extend_of_continuous_family`：continuous_uncurry_
extend_of_continuous_family {ι : Type*} [TopologicalSpace ι] {a b : ι -> X} (γ :
 forall t : ι, Path (a t) (b t)) (h : Con…
· 使用定理 `Continuous.if_le`：Continuous.if_le [TopologicalSpace γ] [forall x, Decid
able (f x <= g x)] {f' g' : β -> γ} (hf' : Continuous f') (hg' : Continuous g') 
(hf : …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Path.extend_apply`：extend_apply {a b : X} (γ : Path a b) {t : Real} (ht 
: t in (Icc 0 1 : Set Real)) : γ.extend t = γ ⟨t, ht⟩
（共 35 条，此处仅展示前 30 条）
-/
theorem trans_continuous_family {ι : Type*} [TopologicalSpace ι]
    {a b c : ι → X} (γ₁ : ∀ t : ι, Path (a t) (b t)) (h₁ : Continuous ↿γ₁)
    (γ₂ : ∀ t : ι, Path (b t) (c t)) (h₂ : Continuous ↿γ₂) :
    Continuous ↿fun t => (γ₁ t).trans (γ₂ t) := by
  have h₁' := Path.continuous_uncurry_extend_of_continuous_family γ₁ h₁
  have h₂' := Path.continuous_uncurry_extend_of_continuous_family γ₂ h₂
  simp only [HasUncurry.uncurry, Path.trans]
  refine Continuous.if_le ?_ ?_ (continuous_subtype_val.comp continuous_snd) continuous_const ?_
  · change
      Continuous ((fun p : ι × ℝ => (γ₁ p.1).extend p.2) ∘ Prod.map id (fun x => 2 * x : I → ℝ))
    exact h₁'.comp (by fun_prop)
  · change
      Continuous ((fun p : ι × ℝ => (γ₂ p.1).extend p.2) ∘ Prod.map id (fun x => 2 * x - 1 : I → ℝ))
    exact h₂'.comp (by fun_prop)
  · rintro st hst
    simp [hst]

@[continuity, fun_prop]
/-
**Path._root_.Continuous.path_trans** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.path_trans {f : Y → Path x y} {g : Y → Path y z} :
    Continuous f → Continuous g → Continuous fun t => (f t).trans (g t) := by
  intro hf hg
  apply continuous_uncurry_iff.mp
  exact trans_continuous_family _ (continuous_uncurry_iff.mpr hf) _ (continuous_uncurry_iff.mpr hg)

@[continuity, fun_prop]
/-
**Path.continuous_trans** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：continuous_trans {x y z : X} : Continuous fun ρ : Path x y × Path y z => ρ
.1.trans ρ.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.path_trans`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] {x y z : X} {f : Y → Path x y}   {g : Y
 → Path y z…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
theorem continuous_trans {x y z : X} : Continuous fun ρ : Path x y × Path y z => ρ.1.trans ρ.2 := by
  fun_prop


/-! #### Product of paths -/
section Prod

variable {a₁ a₂ a₃ : X} {b₁ b₂ b₃ : Y}

/-- Given a path in `X` and a path in `Y`, we can take their pointwise product to get a path in
`X × Y`. -/
/-
**Path.prod** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：{X : Type u_1} →   {Y : Type u_2} →     [inst : TopologicalSpace X] →     
  [inst_1 : TopologicalSpace Y] → {a₁ a₂ : X} → {b₁ b₂ : Y} → Path a₁ a₂ → Path 
b₁ b₂ → Path (a₁, b₁) (a₂, b₂)
参数：a₁, b₁；a₂, b₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a path in `X` and a path in `Y`, we can take their pointwise product to ge
t a path in
`X × Y`.
-/
protected def prod (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) : Path (a₁, b₁) (a₂, b₂) where
  toContinuousMap := ContinuousMap.prodMk γ₁.toContinuousMap γ₂.toContinuousMap
  source' := by simp
  target' := by simp

@[simp, grind =]
/-
**Path.prod_coe** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：prod_coe (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) : ⇑(γ₁.prod γ₂) = fun t => (γ
₁ t, γ₂ t)
参数：γ₁ : Path a₁ a₂；γ₂ : Path b₁ b₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_coe (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) :
    ⇑(γ₁.prod γ₂) = fun t => (γ₁ t, γ₂ t) :=
  rfl

/-- Path composition commutes with products -/
/-
**Path.trans_prod_eq_prod_trans** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：trans_prod_eq_prod_trans (γ₁ : Path a₁ a₂) (δ₁ : Path a₂ a₃) (γ₂ : Path b₁
 b₂) (δ₂ : Path b₂ b₃) : (γ₁.prod γ₂).trans (δ₁.prod δ₂) = (γ₁.trans δ₁).prod (γ
₂.trans δ₂)
参数：γ₁ : Path a₁ a₂；δ₁ : Path a₂ a₃；γ₂ : Path b₁ b₂；δ₂ : Path b₂ b₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Path composition commutes with products
-/
theorem trans_prod_eq_prod_trans (γ₁ : Path a₁ a₂) (δ₁ : Path a₂ a₃) (γ₂ : Path b₁ b₂)
    (δ₂ : Path b₂ b₃) : (γ₁.prod γ₂).trans (δ₁.prod δ₂) = (γ₁.trans δ₁).prod (γ₂.trans δ₂) := by
  grind

end Prod

section Pi

variable {χ : ι → Type*} [∀ i, TopologicalSpace (χ i)] {as bs cs : ∀ i, χ i}

/-- Given a family of paths, one in each Xᵢ, we take their pointwise product to get a path in
Π i, Xᵢ. -/
/-
**Path.pi** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：{ι : Type u_3} →   {χ : ι → Type u_4} →     [inst : (i : ι) → TopologicalS
pace (χ i)] → {as bs : (i : ι) → χ i} → ((i : ι) → Path (as i) (bs i)) → Path as
 bs
参数：i : ι；χ i；i : ι；(i : ι) → Path (as i) (bs i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of paths, one in each Xᵢ, we take their pointwise product to get 
a path in
Π i, Xᵢ.
-/
protected def pi (γ : ∀ i, Path (as i) (bs i)) : Path as bs where
  toContinuousMap := ContinuousMap.pi fun i => (γ i).toContinuousMap
  source' := by simp
  target' := by simp

@[simp, grind =]
/-
**Path.pi_coe** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：pi_coe (γ : forall i, Path (as i) (bs i)) : ⇑(Path.pi γ) = fun t i => γ i 
t
参数：γ : forall i, Path (as i) (bs i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_coe (γ : ∀ i, Path (as i) (bs i)) : ⇑(Path.pi γ) = fun t i => γ i t :=
  rfl

/-- Path composition commutes with products -/
/-
**Path.trans_pi_eq_pi_trans** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：trans_pi_eq_pi_trans (γ₀ : forall i, Path (as i) (bs i)) (γ₁ : forall i, P
ath (bs i) (cs i)) : (Path.pi γ₀).trans (Path.pi γ₁) = Path.pi fun i => (γ₀ i).t
rans (γ₁ i)
参数：γ₀ : forall i, Path (as i) (bs i)；γ₁ : forall i, Path (bs i) (cs i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e

--- 原说明 ---
Path composition commutes with products
-/
theorem trans_pi_eq_pi_trans (γ₀ : ∀ i, Path (as i) (bs i)) (γ₁ : ∀ i, Path (bs i) (cs i)) :
    (Path.pi γ₀).trans (Path.pi γ₁) = Path.pi fun i => (γ₀ i).trans (γ₁ i) := by
  ext t i
  unfold Path.trans
  simp only [Path.coe_mk_mk, Function.comp_apply, pi_coe]
  split_ifs
  · rfl
  · rfl

end Pi

/-! #### Pointwise operations on paths in a topological (additive) group -/


/-- Pointwise multiplication of paths in a topological group. -/
@[to_additive (attr := simps!) /-- Pointwise addition of paths in a topological additive group. -/]
/-
**Path.mul** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：{X : Type u_1} →   [inst : TopologicalSpace X] →     [inst_1 : Mul X] → [C
ontinuousMul X] → {a₁ b₁ a₂ b₂ : X} → Path a₁ b₁ → Path a₂ b₂ → Path (a₁ * a₂) (
b₁ * b₂)
参数：a₁ * a₂；b₁ * b₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2

--- 原说明 ---
Pointwise multiplication of paths in a topological group.
-/
protected def mul [Mul X] [ContinuousMul X] {a₁ b₁ a₂ b₂ : X} (γ₁ : Path a₁ b₁) (γ₂ : Path a₂ b₂) :
    Path (a₁ * a₂) (b₁ * b₂) :=
  (γ₁.prod γ₂).map continuous_mul

/-- Pointwise inversion of paths in a topological group. -/
@[to_additive (attr := simps!) /-- Pointwise negation of paths in a topological group. -/]
/-
**Path.inv** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：inv {a b : X} [Inv X] [ContinuousInv X] (γ : Path a b) : Path a⁻¹ b⁻¹
参数：γ : Path a b。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹

--- 原说明 ---
Pointwise inversion of paths in a topological group.
-/
def inv {a b : X} [Inv X] [ContinuousInv X] (γ : Path a b) :
    Path a⁻¹ b⁻¹ :=
  γ.map continuous_inv

/-! #### Truncating a path -/


/-- `γ.truncate t₀ t₁` is the path which follows the path `γ` on the time interval `[t₀, t₁]`
and stays still otherwise. -/
/-
**Path.truncate** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：truncate {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) (t₀ t₁ 
: Real) : Path (γ.extend <| min t₀ t₁) (γ.extend t₁) where toFun s
参数：γ : Path a b；t₀ t₁ : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`γ.truncate t₀ t₁` is the path which follows the path `γ` on the time interval `
[t₀, t₁]`
and stays still otherwise.
-/
def truncate {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) (t₀ t₁ : ℝ) :
    Path (γ.extend <| min t₀ t₁) (γ.extend t₁) where
  toFun s := γ.extend (min (max s t₀) t₁)
  continuous_toFun := γ.continuous_extend.comp (by fun_prop)
  source' := by
    simp only [min_def, max_def']
    split_ifs with h₁ h₂ h₃ h₄
    · simp [γ.extend_of_le_zero h₁]
    · congr
      linarith
    · have h₄ : t₁ ≤ 0 := le_of_lt (by simpa using h₂)
      simp [γ.extend_of_le_zero h₄, γ.extend_of_le_zero h₁]
    all_goals rfl
  target' := by
    simp only [min_def, max_def']
    split_ifs with h₁ h₂ h₃
    · simp [γ.extend_of_one_le h₂]
    · rfl
    · have h₄ : 1 ≤ t₀ := le_of_lt (by simpa using h₁)
      simp [γ.extend_of_one_le h₄, γ.extend_of_one_le (h₄.trans h₃)]
    · rfl

/-- `γ.truncateOfLE t₀ t₁ h`, where `h : t₀ ≤ t₁` is `γ.truncate t₀ t₁`
casted as a path from `γ.extend t₀` to `γ.extend t₁`. -/
/-
**Path.truncateOfLE** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：truncateOfLE {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) {t₀
 t₁ : Real} (h : t₀ <= t₁) : Path (γ.extend t₀) (γ.extend t₁)
参数：γ : Path a b；h : t₀ <= t₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`γ.truncateOfLE t₀ t₁ h`, where `h : t₀ ≤ t₁` is `γ.truncate t₀ t₁`
casted as a path from `γ.extend t₀` to `γ.extend t₁`.
-/
def truncateOfLE {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) {t₀ t₁ : ℝ}
    (h : t₀ ≤ t₁) : Path (γ.extend t₀) (γ.extend t₁) :=
  (γ.truncate t₀ t₁).cast (by rw [min_eq_left h]) rfl
/-
**Path.truncate_range** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：truncate_range {a b : X} (γ : Path a b) {t₀ t₁ : Real} : range (γ.truncate
 t₀ t₁) subseteq range γ
参数：γ : Path a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Path.extend_range`：extend_range {a b : X} (γ : Path a b) : range γ.exten
d = range γ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem truncate_range {a b : X} (γ : Path a b) {t₀ t₁ : ℝ} :
    range (γ.truncate t₀ t₁) ⊆ range γ := by
  rw [← γ.extend_range]
  simp only [range_subset_iff, SetCoe.forall]
  intro x _hx
  simp only [DFunLike.coe, Path.truncate, mem_range_self]

/-- For a path `γ`, `γ.truncate` gives a "continuous family of paths", by which we mean
the uncurried function which maps `(t₀, t₁, s)` to `γ.truncate t₀ t₁ s` is continuous. -/
@[continuity]
/-
**Path.truncate_continuous_family** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：truncate_continuous_family {a b : X} (γ : Path a b) : Continuous (fun x =>
 γ.truncate x.1 x.2.1 x.2.2 : Real × Real × I -> X)
参数：γ : Path a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Path.continuous_extend`：continuous_extend : Continuous γ.extend
· 使用定理 `Continuous.min`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : LinearOrder α] [OrderClosedTopology α] {f g : β → α}   [inst_3 : Topol
ogic…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.max`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : LinearOrder α] [OrderClosedTopology α] {f g : β → α}   [inst_3 : Topol
ogic…
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)

--- 原说明 ---
For a path `γ`, `γ.truncate` gives a "continuous family of paths", by which we m
ean
the uncurried function which maps `(t₀, t₁, s)` to `γ.truncate t₀ t₁ s` is conti
nuous.
-/
theorem truncate_continuous_family {a b : X} (γ : Path a b) :
    Continuous (fun x => γ.truncate x.1 x.2.1 x.2.2 : ℝ × ℝ × I → X) :=
  γ.continuous_extend.comp
    (((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).max continuous_fst).min
      (continuous_fst.comp continuous_snd))

@[continuity]
/-
**Path.truncate_const_continuous_family** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：truncate_const_continuous_family {a b : X} (γ : Path a b) (t : Real) : Con
tinuous ↿(γ.truncate t)
参数：γ : Path a b；t : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Path.truncate_continuous_family`：truncate_continuous_family {a b : X} (γ
 : Path a b) : Continuous (fun x => γ.truncate x.1 x.2.1 x.2.2 : Real × Real × I
 -> X)
-/
theorem truncate_const_continuous_family {a b : X} (γ : Path a b)
    (t : ℝ) : Continuous ↿(γ.truncate t) := by
  have key : Continuous (fun x => (t, x) : ℝ × I → ℝ × ℝ × I) := by fun_prop
  exact γ.truncate_continuous_family.comp key

@[simp]
/-
**Path.truncate_self** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：truncate_self {a b : X} (γ : Path a b) (t : Real) : γ.truncate t t = (Path
.refl <| γ.extend t).cast (by rw [min_self]) rfl
参数：γ : Path a b；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `ContinuousMap.mk.congr_simp`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (toFun toFun_1 : X → Y)   (e_toFu
n : toFun = toFun…
· 使用定理 `Path.mk.congr_simp`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : 
X} (toContinuousMap toContinuousMap_1 : C(↑unitInterval, X))   (e_toContinuousMa
p : toCo…
· 使用定理 `Path.refl_apply`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (x
_1 : ↑unitInterval), (Path.refl x) x_1 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem truncate_self {a b : X} (γ : Path a b) (t : ℝ) :
    γ.truncate t t = (Path.refl <| γ.extend t).cast (by rw [min_self]) rfl := by
  ext x
  by_cases hx : x ≤ t <;> simp [truncate]
/-
**Path.truncate_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：truncate_zero_zero {a b : X} (γ : Path a b) : γ.truncate 0 0 = (Path.refl 
a).cast (by rw [min_self, γ.extend_zero]) γ.extend_zero
参数：γ : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.extend_zero`：extend_zero : γ.extend 0 = x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Path.truncate_self`：truncate_self {a b : X} (γ : Path a b) (t : Real) : 
γ.truncate t t = (Path.refl <| γ.extend t).cast (by rw [min_self]) rfl
-/
theorem truncate_zero_zero {a b : X} (γ : Path a b) :
    γ.truncate 0 0 = (Path.refl a).cast (by rw [min_self, γ.extend_zero]) γ.extend_zero := by
  convert! γ.truncate_self 0
/-
**Path.truncate_one_one** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：truncate_one_one {a b : X} (γ : Path a b) : γ.truncate 1 1 = (Path.refl b)
.cast (by rw [min_self, γ.extend_one]) γ.extend_one
参数：γ : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.extend_one`：extend_one : γ.extend 1 = y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Path.truncate_self`：truncate_self {a b : X} (γ : Path a b) (t : Real) : 
γ.truncate t t = (Path.refl <| γ.extend t).cast (by rw [min_self]) rfl
-/
theorem truncate_one_one {a b : X} (γ : Path a b) :
    γ.truncate 1 1 = (Path.refl b).cast (by rw [min_self, γ.extend_one]) γ.extend_one := by
  convert! γ.truncate_self 1

@[simp]
/-
**Path.truncate_zero_one** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：truncate_zero_one {a b : X} (γ : Path a b) : γ.truncate 0 1 = γ.cast (by s
imp) (by simp)
参数：γ : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.cast_coe`：cast_coe (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = 
y) : (γ.cast hx hy : I -> X) = γ
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Path.truncate.eq_1`：∀ {X : Type u_4} [inst : TopologicalSpace X] {a b : 
X} (γ : Path a b) (t₀ t₁ : ℝ),   γ.truncate t₀ t₁ =     { toFun := fun s => γ.ex
tend (mi…
· 使用定理 `Path.coe_mk_mk`：coe_mk_mk (f : I -> X) (h₁) (h₂ : f 0 = x) (h₃ : f 1 = y
) : ⇑(mk ⟨f, h₁⟩ h₂ h₃ : Path x y) = f
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Path.extend_extends'`：extend_extends' {a b : X} (γ : Path a b) (t : (Icc
 0 1 : Set Real)) : γ.extend t = γ t
-/
theorem truncate_zero_one {a b : X} (γ : Path a b) :
    γ.truncate 0 1 = γ.cast (by simp) (by simp) := by
  ext x
  rw [cast_coe]
  have : ↑x ∈ (Icc 0 1 : Set ℝ) := x.2
  rw [truncate, coe_mk_mk, max_eq_left this.1, min_eq_left this.2, extend_extends']

/-! #### Reparametrising a path -/


/-- Given a path `γ` and a function `f : I → I` where `f 0 = 0` and `f 1 = 1`, `γ.reparam f` is the
path defined by `γ ∘ f`.
-/
/-
**Path.reparam** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：reparam (γ : Path x y) (f : I -> I) (hfcont : Continuous f) (hf₀ : f 0 = 0
) (hf₁ : f 1 = 1) : Path x y where toFun
参数：γ : Path x y；f : I -> I；hfcont : Continuous f；hf₀ : f 0 = 0；hf₁ : f 1 = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a path `γ` and a function `f : I → I` where `f 0 = 0` and `f 1 = 1`, `γ.re
param f` is the
path defined by `γ ∘ f`.
-/
def reparam (γ : Path x y) (f : I → I) (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Path x y where
  toFun := γ ∘ f
  continuous_toFun := by fun_prop
  source' := by simp [hf₀]
  target' := by simp [hf₁]

@[simp]
/-
**Path.coe_reparam** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：coe_reparam (γ : Path x y) {f : I -> I} (hfcont : Continuous f) (hf₀ : f 0
 = 0) (hf₁ : f 1 = 1) : ⇑(γ.reparam f hfcont hf₀ hf₁) = γ ∘ f
参数：γ : Path x y；hfcont : Continuous f；hf₀ : f 0 = 0；hf₁ : f 1 = 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_reparam (γ : Path x y) {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) : ⇑(γ.reparam f hfcont hf₀ hf₁) = γ ∘ f :=
  rfl

@[simp]
/-
**Path.reparam_id** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：reparam_id (γ : Path x y) : γ.reparam id continuous_id rfl rfl = γ
参数：γ : Path x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem reparam_id (γ : Path x y) : γ.reparam id continuous_id rfl rfl = γ := by
  ext
  rfl
/-
**Path.range_reparam** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：range_reparam (γ : Path x y) {f : I -> I} (hfcont : Continuous f) (hf₀ : f
 0 = 0) (hf₁ : f 1 = 1) : range (γ.reparam f hfcont hf₀ hf₁) = range γ
参数：γ : Path x y；hfcont : Continuous f；hf₀ : f 0 = 0；hf₁ : f 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用引理 `zero_le_one'`：zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α
] : (0 : α) <= 1
· 使用定理 `Continuous.Icc_extend'`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOr
der α] {a b : α} {h : a ≤ b} [inst_1 : TopologicalSpace α]   [OrderTopology α] [
inst_3 : Top…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `intermediate_value_Icc`：intermediate_value_Icc {a b : α} (hab : a <= b) 
{f : α -> δ} (hf : ContinuousOn f (Icc a b)) : Icc (f a) (f b) subseteq f '' Icc
 a b
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Subtype.instOrderClosedTopology`：∀ {α : Type u} [inst : TopologicalSpace
 α] [inst_1 : Preorder α] [t : OrderClosedTopology α] {p : α → Prop},   OrderClo
sedTopology (Subtype …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `Set.Icc.mk_one`：mk_one (h : (1 : R) in Icc (0 : R) 1) : (⟨1, h⟩ : Icc (0
 : R) 1) = 1
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Set.Icc.mk_zero`：mk_zero (h : (0 : R) in Icc (0 : R) 1) : (⟨0, h⟩ : Icc 
(0 : R) 1) = 0
· 使用定理 `Set.IccExtend_right`：IccExtend_right (f : Icc a b -> β) : IccExtend h f 
b = f ⟨b, right_mem_Icc.2 h⟩
· 使用定理 `Set.IccExtend_left`：IccExtend_left (f : Icc a b -> β) : IccExtend h f a 
= f ⟨a, left_mem_Icc.2 h⟩
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.IccExtend_of_mem`：IccExtend_of_mem (f : Icc a b -> β) (hx : x in Icc
 a b) : IccExtend h f x = f ⟨x, hx⟩
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
theorem range_reparam (γ : Path x y) {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) : range (γ.reparam f hfcont hf₀ hf₁) = range γ := by
  change range (γ ∘ f) = range γ
  have : range f = univ := by
    rw [range_eq_univ]
    intro t
    have h₁ : Continuous (Set.IccExtend (zero_le_one' ℝ) f) := by fun_prop
    have := intermediate_value_Icc (zero_le_one' ℝ) h₁.continuousOn
    · rw [IccExtend_left, IccExtend_right, Icc.mk_zero, Icc.mk_one, hf₀, hf₁] at this
      rcases this t.2 with ⟨w, hw₁, hw₂⟩
      rw [IccExtend_of_mem _ _ hw₁] at hw₂
      exact ⟨_, hw₂⟩
  rw [range_comp, this, image_univ]
/-
**Path.refl_reparam** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：refl_reparam {f : I -> I} (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f
 1 = 1) : (refl x).reparam f hfcont hf₀ hf₁ = refl x
参数：hfcont : Continuous f；hf₀ : f 0 = 0；hf₁ : f 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.refl_apply`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (x
_1 : ↑unitInterval), (Path.refl x) x_1 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem refl_reparam {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    (refl x).reparam f hfcont hf₀ hf₁ = refl x := by
  ext
  simp

end Path

