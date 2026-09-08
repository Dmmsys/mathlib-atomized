/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
## Continuous representations

This file defines continuous representations of a monoid `G` on a `R`-module `V` and
related basic results.

## Main Results

* `ContRepresentation R G V` is the type of continuous representations of a monoid `G` on a
  `R`-module `V` which is a topological addgroup (where the action of `G` on `V` is
  *not* assumed to be continuous). The reason for this more general definition is that it allows us
  to define the coinduced representation of a continuous representation as also a continuous
  representation without any restriction on the topology on `G`.

* `ContIntertwiningMap π₁ π₂` is the type of continuous intertwining maps between two continuous
  representations `π₁` and `π₂`.

* `ContRepresentation.coind₁ π` is the coinduced continuous representation on the space of
  continuous functions from `G` to `V` for a continuous representation `π`.

* `ContIntertwiningMap.mapInvariantsOfRes φ f` is the continuous linear map
  `π.invariants →L[R] π'.invariants` induced by a monoid homomorphism `φ : H →* G` and a
  continuous intertwining map `f : π.restrict φ →ⁱL π'`.

* `ContRepresentation.coind₁ResMap φ f` is the continuous intertwining map
  `π.coind₁.restrict φ →ⁱL π'.coind₁` induced by a continuous group homomorphism `φ : H →ₜ* G`
  and a continuous intertwining map `f : π.restrict φ →ⁱL π'`, given by `F ↦ f ∘ F ∘ φ`.

## Tags
continuous representation, algebra
-/

@[expose] public section

variable (R G V W U : Type*) [Monoid G] [Ring R] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V] [AddCommGroup W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [Module R W] [AddCommGroup U] [Module R U] [TopologicalSpace U]
  [IsTopologicalAddGroup U]

/-- A continuous representation of a group `G` on a `R`-module `V` which is a topological addgroup
  is a homomorphism `G →* V →L[R] V`. -/
/-
**ContRepresentation** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (G : Type u_2) →     (V : Type u_3) →       [Monoid G] 
→         [inst : Ring R] →           [inst_1 : AddCommGroup V] →             [i
nst_2 : TopologicalSpace V] → [IsTopologicalAddGroup V] → [_root_.Module R V] → 
Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous representation of a group `G` on a `R`-module `V` which is a topolo
gical addgroup
  is a homomorphism `G →* V →L[R] V`.
-/
structure ContRepresentation where
  ofMonoidHom ::
  /-- The underlying monoid homomorphism of a continuous representation. -/
  toMonoidHom : G →* V →L[R] V
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (ContRepresentation R G V) G (V →L[R] V) where
  coe π := π.toMonoidHom
  coe_injective π₁ π₂ _ := by cases π₁; cases π₂; simp_all
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidHomClass (ContRepresentation R G V) G (V →L[R] V) where
  map_one π := π.toMonoidHom.map_one
  map_mul π := π.toMonoidHom.map_mul
/-
**ContRepresentation.toMonoidHom_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContRepresentation.toMonoidHom_apply (π : ContRepresentation R G V) (g : G
) : π.toMonoidHom g = π g
参数：π : ContRepresentation R G V；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
lemma ContRepresentation.toMonoidHom_apply (π : ContRepresentation R G V) (g : G) :
    π.toMonoidHom g = π g := rfl

/-- Every continuous representation "is" a representation. -/
/-
**ContRepresentation.toRepresentation** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ContRepresentation.toRepresentation (π : ContRepresentation R G V) : Repre
sentation R G V
参数：π : ContRepresentation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every continuous representation "is" a representation.
-/
abbrev ContRepresentation.toRepresentation (π : ContRepresentation R G V) :
    Representation R G V :=
  .comp ContinuousLinearMap.toLinearMapRingHom.toMonoidHom π.toMonoidHom

variable {R G V W U}

/-- A continuous intertwining map between two continuous representations is an intertwining map
  which is also continuous. -/
/-
**ContIntertwiningMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} →   {G : Type u_2} →     {V : Type u_3} →       {W : Type u
_4} →         [inst : Monoid G] →           [inst_1 : Ring R] →             [ins
t_2 : AddCommGroup V] →               [inst_3 : TopologicalSpace V] →           
      [inst_4 : IsTopologicalAddGroup V] →                   [inst_5 : _root_.Mo
dule R V] →                     [inst_6 : AddCommGroup W] →                     
  [inst_7 : TopologicalSpace W] →                         [inst_8 : IsTopologica
lAddGroup W] →                           [inst_9 : _root_.Module R W] →         
                    ContRepresentation R G V → ContRepresentation R G W → Type (
max u_3 u_4)
参数：max u_3 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous intertwining map between two continuous representations is an inter
twining map
  which is also continuous.
-/
structure ContIntertwiningMap (π₁ : ContRepresentation R G V) (π₂ : ContRepresentation R G W)
    extends V →L[R] W where
  isIntertwining' (g : G) : toContinuousLinearMap ∘L π₁ g = π₂ g ∘L toContinuousLinearMap

/-- notation for continuous intertwining maps -/
scoped[ContRepresentation] notation:30 π₁ " →ⁱL " π₂ =>
  ContIntertwiningMap π₁ π₂

namespace ContIntertwiningMap

open ContRepresentation

variable {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
  {π₃ : ContRepresentation R G U}

/-- Any continuous intertwining map is an intertwining map. -/
/-
**ContIntertwiningMap.toIntertwiningMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `ContIntertw
iningMap`。
形式化陈述：toIntertwiningMap (f : π₁ ->ⁱL π₂) : Representation.IntertwiningMap π₁.toR
epresentation π₂.toRepresentation where __
参数：f : π₁ ->ⁱL π₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any continuous intertwining map is an intertwining map.
-/
abbrev toIntertwiningMap (f : π₁ →ⁱL π₂) :
    Representation.IntertwiningMap π₁.toRepresentation π₂.toRepresentation where
  __ := f.toContinuousLinearMap.toLinearMap
  isIntertwining' g := congr(ContinuousLinearMap.toLinearMap $(f.2 g))

/-- The identity continuous intertwining map. -/
/-
**ContIntertwiningMap.id** 是 Mathlib 中的一个定义，位于命名空间 `ContIntertwiningMap`。
形式化陈述：id : π₁ ->ⁱL π₁ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity continuous intertwining map.
-/
def id : π₁ →ⁱL π₁ where
  __ := ContinuousLinearMap.id R V
  isIntertwining' g := by simp

@[simp]
/-
**ContIntertwiningMap.toContinuousLinearMap_id** 是 Mathlib 中的一个引理，位于命名空间 `ContIn
tertwiningMap`。
形式化陈述：toContinuousLinearMap_id : (id : π₁ ->ⁱL π₁).toContinuousLinearMap = Conti
nuousLinearMap.id R V
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousLinearMap_id :
    (id : π₁ →ⁱL π₁).toContinuousLinearMap = ContinuousLinearMap.id R V := rfl

@[ext]
/-
**ContIntertwiningMap.ext** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwiningMap`。
形式化陈述：ext {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} {f g :
 π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toContinuousLinearMap) : f = g
参数：h : f.toContinuousLinearMap = g.toContinuousLinearMap。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ext {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    {f g : π₁ →ⁱL π₂} (h : f.toContinuousLinearMap = g.toContinuousLinearMap) : f = g := by
  cases f; cases g; congr
/-
**ContIntertwiningMap.toContinuousLinearMap_injective** 是 Mathlib 中的一个引理，位于命名空间 
`ContIntertwiningMap`。
形式化陈述：toContinuousLinearMap_injective {π₁ : ContRepresentation R G V} {π₂ : Cont
Representation R G W} : Function.Injective fun f : π₁ ->ⁱL π₂ => f.toContinuousL
inearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContIntertwiningMap.ext`：ext {π₁ : ContRepresentation R G V} {π₂ : ContR
epresentation R G W} {f g : π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toConti
nuousLinearMa…
-/
lemma toContinuousLinearMap_injective {π₁ : ContRepresentation R G V}
    {π₂ : ContRepresentation R G W} :
    Function.Injective fun f : π₁ →ⁱL π₂ ↦ f.toContinuousLinearMap :=
  fun _ _ ↦ ext
/-
**ContIntertwiningMap.toIntertwiningMap_injective** 是 Mathlib 中的一个引理，位于命名空间 `Con
tIntertwiningMap`。
形式化陈述：toIntertwiningMap_injective {π₁ : ContRepresentation R G V} {π₂ : ContRepr
esentation R G W} : Function.Injective fun f : π₁ ->ⁱL π₂ => f.toIntertwiningMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContIntertwiningMap.ext`：ext {π₁ : ContRepresentation R G V} {π₂ : ContR
epresentation R G W} {f g : π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toConti
nuousLinearMa…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.IntertwiningMap.mk.injEq`：∀ {A : Type u_1} {G : Type u_2}
 {V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   [inst_2
 : AddCommMonoid V] [inst_3 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toIntertwiningMap_injective {π₁ : ContRepresentation R G V}
    {π₂ : ContRepresentation R G W} :
    Function.Injective fun f : π₁ →ⁱL π₂ ↦ f.toIntertwiningMap :=
  fun _ _ _ ↦ by ext; simp_all
/-
**ContIntertwiningMap.toFun_injective** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwinin
gMap`。
形式化陈述：toFun_injective {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R
 G W} : Function.Injective fun f : π₁ ->ⁱL π₂ => f.toFun
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContIntertwiningMap.ext`：ext {π₁ : ContRepresentation R G V} {π₂ : ContR
epresentation R G W} {f g : π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toConti
nuousLinearMa…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
lemma toFun_injective {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} :
    Function.Injective fun f : π₁ →ⁱL π₂ ↦ f.toFun := fun f g h ↦ by
  ext x; exact congr_fun h x
/-
**ContIntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContIntertwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} :
    FunLike (π₁ →ⁱL π₂) V W where
  coe f := f.toFun
  coe_injective := toFun_injective
/-
**ContIntertwiningMap.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwiningMap`。
形式化陈述：id_apply (v : V) : (.id : π₁ ->ⁱL π₁) v = v
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_apply (v : V) : (.id : π₁ →ⁱL π₁) v = v := rfl
/-
**ContIntertwiningMap.toContinuousLinearMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `Con
tIntertwiningMap`。
形式化陈述：toContinuousLinearMap_apply (f : π₁ ->ⁱL π₂) (v : V) : f.toContinuousLinea
rMap v = f v
参数：f : π₁ ->ⁱL π₂；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousLinearMap_apply (f : π₁ →ⁱL π₂) (v : V) :
  f.toContinuousLinearMap v = f v := rfl
/-
**ContIntertwiningMap.isIntertwining** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwining
Map`。
形式化陈述：isIntertwining {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R 
G W} (f : π₁ ->ⁱL π₂) (g : G) (v : V) : f (π₁ g v) = π₂ g (f v)
参数：f : π₁ ->ⁱL π₂；g : G；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.isIntertwining`：isIntertwining (f : Inter
twiningMap ρ σ) (g : G) (v : V) : f (ρ g v) = σ g (f v)
-/
lemma isIntertwining {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    (f : π₁ →ⁱL π₂) (g : G) (v : V) : f (π₁ g v) = π₂ g (f v) :=
  f.toIntertwiningMap.isIntertwining _ _ g v
/-
**ContIntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContIntertwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} :
    ContinuousLinearMapClass (π₁ →ⁱL π₂) R V W where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul
  map_continuous f := f.cont

open ContinuousLinearMap in
/-- The composition of two continuous intertwining maps is a continuous intertwining map. -/
/-
**ContIntertwiningMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `ContIntertwiningMap`。
形式化陈述：comp {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} {π₃ :
 ContRepresentation R G U} (f : π₂ ->ⁱL π₃) (g : π₁ ->ⁱL π₂) : π₁ ->ⁱL π₃ where 
__
参数：f : π₂ ->ⁱL π₃；g : π₁ ->ⁱL π₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two continuous intertwining maps is a continuous intertwining
 map.
-/
def comp {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    {π₃ : ContRepresentation R G U} (f : π₂ →ⁱL π₃) (g : π₁ →ⁱL π₂) : π₁ →ⁱL π₃ where
  __ := f.toContinuousLinearMap.comp g.toContinuousLinearMap
  isIntertwining' h := by rw [comp_assoc, g.2, ← comp_assoc, f.2, comp_assoc]

@[simp]
/-
**ContIntertwiningMap.toContinuousLinearMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `Cont
IntertwiningMap`。
形式化陈述：toContinuousLinearMap_comp {π₁ : ContRepresentation R G V} {π₂ : ContRepre
sentation R G W} {π₃ : ContRepresentation R G U} (f : π₂ ->ⁱL π₃) (g : π₁ ->ⁱL π
₂) : (f.comp g).toContinuousLinearMap = f.toContinuousLinearMap.comp g.toContinu
ousLinearMap
参数：f : π₂ ->ⁱL π₃；g : π₁ ->ⁱL π₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousLinearMap_comp {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    {π₃ : ContRepresentation R G U} (f : π₂ →ⁱL π₃) (g : π₁ →ⁱL π₂) :
    (f.comp g).toContinuousLinearMap = f.toContinuousLinearMap.comp g.toContinuousLinearMap := rfl
/-
**ContIntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContIntertwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (π₁ →ⁱL π₂) where
  add f g := ⟨f.toContinuousLinearMap + g.toContinuousLinearMap, by simp [g.2, f.2]⟩

@[simp]
/-
**ContIntertwiningMap.toContinuousLinearMap_add** 是 Mathlib 中的一个引理，位于命名空间 `ContI
ntertwiningMap`。
形式化陈述：toContinuousLinearMap_add (f g : π₁ ->ⁱL π₂) : (f + g).toContinuousLinearM
ap = f.toContinuousLinearMap + g.toContinuousLinearMap
参数：f g : π₁ ->ⁱL π₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousLinearMap_add (f g : π₁ →ⁱL π₂) :
    (f + g).toContinuousLinearMap = f.toContinuousLinearMap + g.toContinuousLinearMap := rfl
/-
**ContIntertwiningMap.add_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwiningMap`。
形式化陈述：add_apply (f g : π₁ ->ⁱL π₂) (v : V) : (f + g) v = f v + g v
参数：f g : π₁ ->ⁱL π₂；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma add_apply (f g : π₁ →ⁱL π₂) (v : V) : (f + g) v = f v + g v := rfl
/-
**ContIntertwiningMap.comp_add** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwiningMap`。
形式化陈述：comp_add (f : π₂ ->ⁱL π₃) (g h : π₁ ->ⁱL π₂) : f.comp (g + h) = f.comp g +
 f.comp h
参数：f : π₂ ->ⁱL π₃；g h : π₁ ->ⁱL π₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContIntertwiningMap.ext`：ext {π₁ : ContRepresentation R G V} {π₂ : ContR
epresentation R G W} {f g : π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toConti
nuousLinearMa…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.comp_add`：comp_add [ContinuousAdd M₂] [ContinuousAdd
 M₃] (g : M₂ ->SL[σ₂₃] M₃) (f₁ f₂ : M₁ ->SL[σ₁₂] M₂) : g ∘SL (f₁ + f₂) = g ∘SL f
₁ + g ∘SL f₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_add (f : π₂ →ⁱL π₃) (g h : π₁ →ⁱL π₂) :
    f.comp (g + h) = f.comp g + f.comp h := by ext; simp
/-
**ContIntertwiningMap.add_comp** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwiningMap`。
形式化陈述：add_comp (f g : π₂ ->ⁱL π₃) (h : π₁ ->ⁱL π₂) : (f + g).comp h = f.comp h +
 g.comp h
参数：f g : π₂ ->ⁱL π₃；h : π₁ ->ⁱL π₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContIntertwiningMap.ext`：ext {π₁ : ContRepresentation R G V} {π₂ : ContR
epresentation R G W} {f g : π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toConti
nuousLinearMa…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.add_comp`：add_comp [ContinuousAdd M₃] (g₁ g₂ : M₂ ->
SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) : (g₁ + g₂) ∘SL f = g₁ ∘SL f + g₂ ∘SL f
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_comp (f g : π₂ →ⁱL π₃) (h : π₁ →ⁱL π₂) :
    (f + g).comp h = f.comp h + g.comp h := by ext; simp
/-
**ContIntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContIntertwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (π₁ →ⁱL π₁) where one := .id
/-
**ContIntertwiningMap.one_def** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwiningMap`。
形式化陈述：one_def : (1 : π₁ ->ⁱL π₁) = .id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_def : (1 : π₁ →ⁱL π₁) = .id := rfl

@[simp]
/-
**ContIntertwiningMap.toContinuousLinearMap_one** 是 Mathlib 中的一个引理，位于命名空间 `ContI
ntertwiningMap`。
形式化陈述：toContinuousLinearMap_one : (1 : π₁ ->ⁱL π₁).toContinuousLinearMap = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousLinearMap_one : (1 : π₁ →ⁱL π₁).toContinuousLinearMap = 1 := rfl
/-
**ContIntertwiningMap.one_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwiningMap`。
形式化陈述：one_apply (v : V) : (1 : π₁ ->ⁱL π₁) v = v
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_apply (v : V) : (1 : π₁ →ⁱL π₁) v = v := rfl
/-
**ContIntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContIntertwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (π₁ →ⁱL π₂) where zero := ⟨0, by simp⟩

@[simp]
/-
**ContIntertwiningMap.toContinuousLinearMap_zero** 是 Mathlib 中的一个引理，位于命名空间 `Cont
IntertwiningMap`。
形式化陈述：toContinuousLinearMap_zero : (0 : π₁ ->ⁱL π₂).toContinuousLinearMap = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousLinearMap_zero : (0 : π₁ →ⁱL π₂).toContinuousLinearMap = 0 := rfl
/-
**ContIntertwiningMap.zero_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwiningMap`
。
形式化陈述：zero_apply (v : V) : (0 : π₁ ->ⁱL π₂) v = 0
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_apply (v : V) : (0 : π₁ →ⁱL π₂) v = 0 := rfl
/-
**ContIntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContIntertwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddZeroClass (π₁ →ⁱL π₂) :=
  fast_instance% toContinuousLinearMap_injective.addZeroClass _
    toContinuousLinearMap_zero toContinuousLinearMap_add
/-
**ContIntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContIntertwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommSemigroup (π₁ →ⁱL π₂) :=
  fast_instance% toContinuousLinearMap_injective.addCommSemigroup _
    toContinuousLinearMap_add
/-
**ContIntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContIntertwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (π₁ →ⁱL π₂) where
  neg f := ⟨-f.toContinuousLinearMap, by simp [f.2]⟩

@[simp]
/-
**ContIntertwiningMap.toContinuousLinearMap_neg** 是 Mathlib 中的一个引理，位于命名空间 `ContI
ntertwiningMap`。
形式化陈述：toContinuousLinearMap_neg (f : π₁ ->ⁱL π₂) : (-f).toContinuousLinearMap = 
-f.toContinuousLinearMap
参数：f : π₁ ->ⁱL π₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousLinearMap_neg (f : π₁ →ⁱL π₂) :
    (-f).toContinuousLinearMap = -f.toContinuousLinearMap := rfl
/-
**ContIntertwiningMap.neg_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwiningMap`。
形式化陈述：neg_apply (f : π₁ ->ⁱL π₂) (v : V) : (-f) v = -f v
参数：f : π₁ ->ⁱL π₂；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma neg_apply (f : π₁ →ⁱL π₂) (v : V) : (-f) v = -f v := rfl
/-
**ContIntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContIntertwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (π₁ →ⁱL π₂) where
  sub f g := ⟨f.toContinuousLinearMap - g.toContinuousLinearMap, by simp [g.2, f.2]⟩

@[simp]
/-
**ContIntertwiningMap.toContinuousLinearMap_sub** 是 Mathlib 中的一个引理，位于命名空间 `ContI
ntertwiningMap`。
形式化陈述：toContinuousLinearMap_sub (f g : π₁ ->ⁱL π₂) : (f - g).toContinuousLinearM
ap = f.toContinuousLinearMap - g.toContinuousLinearMap
参数：f g : π₁ ->ⁱL π₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousLinearMap_sub (f g : π₁ →ⁱL π₂) :
    (f - g).toContinuousLinearMap = f.toContinuousLinearMap - g.toContinuousLinearMap := rfl
/-
**ContIntertwiningMap.sub_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwiningMap`。
形式化陈述：sub_apply (f g : π₁ ->ⁱL π₂) (v : V) : (f - g) v = f v - g v
参数：f g : π₁ ->ⁱL π₂；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sub_apply (f g : π₁ →ⁱL π₂) (v : V) : (f - g) v = f v - g v := rfl
/-
**ContIntertwiningMap.sub_comp** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwiningMap`。
形式化陈述：sub_comp (f g : π₂ ->ⁱL π₃) (h : π₁ ->ⁱL π₂) : (f - g).comp h = f.comp h -
 g.comp h
参数：f g : π₂ ->ⁱL π₃；h : π₁ ->ⁱL π₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContIntertwiningMap.ext`：ext {π₁ : ContRepresentation R G V} {π₂ : ContR
epresentation R G W} {f g : π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toConti
nuousLinearMa…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.sub_comp`：sub_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [
IsTopologicalAddGroup M₃] (g₁ g₂ : M₂ ->SL[σ₂₃] M₃) (f : M ->SL[σ₁₂] M₂) : (g₁ -
 g₂) ∘SL f = g₁ ∘S…
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sub_comp (f g : π₂ →ⁱL π₃) (h : π₁ →ⁱL π₂) :
    (f - g).comp h = f.comp h - g.comp h := by
  ext; simp
/-
**ContIntertwiningMap.comp_sub** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwiningMap`。
形式化陈述：comp_sub (f : π₂ ->ⁱL π₃) (g h : π₁ ->ⁱL π₂) : f.comp (g - h) = f.comp g -
 f.comp h
参数：f : π₂ ->ⁱL π₃；g h : π₁ ->ⁱL π₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContIntertwiningMap.ext`：ext {π₁ : ContRepresentation R G V} {π₂ : ContR
epresentation R G W} {f g : π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toConti
nuousLinearMa…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.comp_sub`：comp_sub [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [
IsTopologicalAddGroup M₂] [IsTopologicalAddGroup M₃] (g : M₂ ->SL[σ₂₃] M₃) (f₁ f
₂ : M ->SL[σ₁₂] M₂…
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_sub (f : π₂ →ⁱL π₃) (g h : π₁ →ⁱL π₂) :
    f.comp (g - h) = f.comp g - f.comp h := by
  ext; simp
/-
**ContIntertwiningMap.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `ContIntertwiningMap`。
形式化陈述：instSMul {S : Type*} [Monoid S] [DistribMulAction S W] [SMulCommClass R S 
W] [ContinuousConstSMul S W] [LinearMap.CompatibleSMul W W S R] : SMul S (π₁ ->ⁱ
L π₂) where smul s f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul {S : Type*} [Monoid S] [DistribMulAction S W] [SMulCommClass R S W]
    [ContinuousConstSMul S W] [LinearMap.CompatibleSMul W W S R] :
    SMul S (π₁ →ⁱL π₂) where
  smul s f := ⟨s • f.toContinuousLinearMap, fun g ↦ by
    rw [ContinuousLinearMap.smul_comp, f.2, ContinuousLinearMap.comp_smul]⟩

section addcommgroup

variable {S : Type*} [Monoid S] [DistribMulAction S W] [SMulCommClass R S W]
  [ContinuousConstSMul S W] [LinearMap.CompatibleSMul W W S R]

@[simp]
/-
**ContIntertwiningMap.toContinuousLinearMap_smul** 是 Mathlib 中的一个引理，位于命名空间 `Cont
IntertwiningMap`。
形式化陈述：toContinuousLinearMap_smul (s : S) (f : π₁ ->ⁱL π₂) : (s • f).toContinuous
LinearMap = s • f.toContinuousLinearMap
参数：s : S；f : π₁ ->ⁱL π₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousLinearMap_smul (s : S) (f : π₁ →ⁱL π₂) :
    (s • f).toContinuousLinearMap = s • f.toContinuousLinearMap := rfl
/-
**ContIntertwiningMap.smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwiningMap`
。
形式化陈述：smul_apply (s : S) (f : π₁ ->ⁱL π₂) (v : V) : (s • f) v = s • f v
参数：s : S；f : π₁ ->ⁱL π₂；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_apply (s : S) (f : π₁ →ⁱL π₂) (v : V) : (s • f) v = s • f v := rfl
/-
**ContIntertwiningMap.smul_comp** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwiningMap`。
形式化陈述：smul_comp {S : Type*} [Monoid S] [DistribMulAction S U] [SMulCommClass R S
 U] [ContinuousConstSMul S U] [LinearMap.CompatibleSMul U U S R] (s : S) (f : π₂
 ->ⁱL π₃) (g : π₁ ->ⁱL π₂) : (s • f).comp g = s • (f.comp g)
参数：s : S；f : π₂ ->ⁱL π₃；g : π₁ ->ⁱL π₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContIntertwiningMap.ext`：ext {π₁ : ContRepresentation R G V} {π₂ : ContR
epresentation R G W} {f g : π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toConti
nuousLinearMa…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_comp {S : Type*} [Monoid S] [DistribMulAction S U] [SMulCommClass R S U]
    [ContinuousConstSMul S U] [LinearMap.CompatibleSMul U U S R]
    (s : S) (f : π₂ →ⁱL π₃) (g : π₁ →ⁱL π₂) : (s • f).comp g = s • (f.comp g) := by
  ext; simp
/-
**ContIntertwiningMap.comp_smul** 是 Mathlib 中的一个引理，位于命名空间 `ContIntertwiningMap`。
形式化陈述：comp_smul {S : Type*} [Monoid S] [DistribMulAction S U] [SMulCommClass R S
 U] [ContinuousConstSMul S U] [LinearMap.CompatibleSMul U U S R] [DistribMulActi
on S W] [SMulCommClass R S W] [ContinuousConstSMul S W] [LinearMap.CompatibleSMu
l W W S R] [LinearMap.CompatibleSMul W U S R] (s : S) (f : π₂ ->ⁱL π₃) (g : π₁ -
>ⁱL π₂) : f.comp (s • g) = s • (f.comp g)
参数：s : S；f : π₂ ->ⁱL π₃；g : π₁ ->ⁱL π₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContIntertwiningMap.ext`：ext {π₁ : ContRepresentation R G V} {π₂ : ContR
epresentation R G W} {f g : π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toConti
nuousLinearMa…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.comp_smul`：comp_smul [LinearMap.CompatibleSMul N₂ N₃
 S R] (hₗ : N₂ ->L[R] N₃) (c : S) (fₗ : M ->L[R] N₂) : hₗ ∘L (c • fₗ) = c • hₗ ∘
L fₗ
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_smul {S : Type*} [Monoid S] [DistribMulAction S U] [SMulCommClass R S U]
    [ContinuousConstSMul S U] [LinearMap.CompatibleSMul U U S R]
    [DistribMulAction S W] [SMulCommClass R S W] [ContinuousConstSMul S W]
    [LinearMap.CompatibleSMul W W S R] [LinearMap.CompatibleSMul W U S R]
    (s : S) (f : π₂ →ⁱL π₃) (g : π₁ →ⁱL π₂) : f.comp (s • g) = s • (f.comp g) := by
  ext; simp
/-
**ContIntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContIntertwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (π₁ →ⁱL π₂) :=
  fast_instance% toContinuousLinearMap_injective.addCommGroup _ toContinuousLinearMap_zero
    toContinuousLinearMap_add toContinuousLinearMap_neg toContinuousLinearMap_sub
    (fun _ _ ↦ toContinuousLinearMap_smul _ _) (fun _ _ ↦ toContinuousLinearMap_smul _ _)
/-
**ContIntertwiningMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContIntertwiningMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribMulAction S (π₁ →ⁱL π₂) where
  one_smul _ := by ext; simp
  mul_smul _ _ _ := by ext; simp [mul_smul]
  smul_zero _ := by ext; simp
  smul_add _ _ _ := by ext; simp [smul_add]
/-
**ContIntertwiningMap.instModule** 是 Mathlib 中的一个实例，位于命名空间 `ContIntertwiningMap`
。
形式化陈述：instModule {S : Type*} [Ring S] [Module S W] [SMulCommClass R S W] [Contin
uousConstSMul S W] [LinearMap.CompatibleSMul W W S R] : Module S (π₁ ->ⁱL π₂) wh
ere add_smul _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule {S : Type*} [Ring S] [Module S W] [SMulCommClass R S W]
    [ContinuousConstSMul S W] [LinearMap.CompatibleSMul W W S R] :
    Module S (π₁ →ⁱL π₂) where
  add_smul _ _ _ := by ext; simp [add_smul]
  zero_smul _ := by ext; simp

end addcommgroup

end ContIntertwiningMap

namespace ContRepresentation

/-- The equivalence between continuous representations. -/
/-
**ContRepresentation.Equiv** 是 Mathlib 中的一个归纳类型，位于命名空间 `ContRepresentation`。
形式化陈述：{R : Type u_1} →   {G : Type u_2} →     {V : Type u_3} →       {W : Type u
_4} →         [inst : Monoid G] →           [inst_1 : Ring R] →             [ins
t_2 : AddCommGroup V] →               [inst_3 : TopologicalSpace V] →           
      [inst_4 : IsTopologicalAddGroup V] →                   [inst_5 : _root_.Mo
dule R V] →                     [inst_6 : AddCommGroup W] →                     
  [inst_7 : TopologicalSpace W] →                         [inst_8 : IsTopologica
lAddGroup W] →                           [inst_9 : _root_.Module R W] →         
                    ContRepresentation R G V → ContRepresentation R G W → Type (
max u_3 u_4)
参数：max u_3 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between continuous representations.
-/
structure Equiv (π₁ : ContRepresentation R G V) (π₂ : ContRepresentation R G W) extends
    V ≃L[R] W, ContIntertwiningMap π₁ π₂  where mk'' ::

attribute [coe] Equiv.toContIntertwiningMap

/-- Underlying continuous linear isomorphism of an equivalence of continuous representations. -/
add_decl_doc Equiv.toContinuousLinearEquiv

/-- The continuous intertwining map underlying an equivalence of continuous representations. -/
add_decl_doc Equiv.toContIntertwiningMap

namespace Equiv

variable {ρ : ContRepresentation R G V} {σ : ContRepresentation R G W}
  {τ : ContRepresentation R G U} (φ : Equiv ρ σ)

/-
**ContRepresentation.Equiv.isIntertwining** 是 Mathlib 中的一个引理，位于命名空间 `ContReprese
ntation.Equiv`。
形式化陈述：isIntertwining (g : G) : φ.toContinuousLinearEquiv.toContinuousLinearMap ∘
L (ρ g) = (σ g) ∘L φ.toContinuousLinearEquiv.toContinuousLinearMap
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContRepresentation.Equiv.isIntertwining'`：∀ {R : Type u_1} {G : Type u_2
} {V : Type u_3} {W : Type u_4} [inst : Monoid G] [inst_1 : Ring R]   [inst_2 : 
AddCommGroup V] [inst_3 : Topo…
-/
lemma isIntertwining (g : G) :
    φ.toContinuousLinearEquiv.toContinuousLinearMap ∘L (ρ g) =
      (σ g) ∘L φ.toContinuousLinearEquiv.toContinuousLinearMap :=
  φ.isIntertwining' g

/-- An `Equiv` between representations could be built from a `LinearEquiv` and an assumption
  proving the `G`-equivariance. -/
/-
**ContRepresentation.Equiv.mk** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation.Equi
v`。
形式化陈述：mk (e : V ≃L[R] W) (he : forall g, e ∘L (ρ g) = (σ g) ∘L e) : ρ.Equiv σ wh
ere __
参数：e : V ≃L[R] W；he : forall g, e ∘L (ρ g) = (σ g) ∘L e。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `Equiv` between representations could be built from a `LinearEquiv` and an as
sumption
  proving the `G`-equivariance.
-/
def mk (e : V ≃L[R] W) (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) : ρ.Equiv σ where
  __ := e
  cont := e.continuous
  isIntertwining' := he
/-
**ContRepresentation.Equiv.toContinuousLinearEquiv_mk'** 是 Mathlib 中的一个引理，位于命名空间
 `ContRepresentation.Equiv`。
形式化陈述：toContinuousLinearEquiv_mk' {e : V ≃L[R] W} (he : forall g, e ∘L (ρ g) = (
σ g) ∘L e) : (mk e he).toContinuousLinearEquiv = e
参数：he : forall g, e ∘L (ρ g) = (σ g) ∘L e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousLinearEquiv_mk' {e : V ≃L[R] W} (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).toContinuousLinearEquiv = e := rfl
/-
**ContRepresentation.Equiv.toContIntertwiningMap_mk'** 是 Mathlib 中的一个引理，位于命名空间 `
ContRepresentation.Equiv`。
形式化陈述：toContIntertwiningMap_mk' (e : V ≃L[R] W) (he : forall g, e ∘L (ρ g) = (σ 
g) ∘L e) : (mk e he).toContIntertwiningMap = ⟨e.toContinuousLinearMap, he⟩
参数：e : V ≃L[R] W；he : forall g, e ∘L (ρ g) = (σ g) ∘L e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContIntertwiningMap_mk' (e : V ≃L[R] W) (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).toContIntertwiningMap = ⟨e.toContinuousLinearMap, he⟩ := rfl

@[simp]
/-
**ContRepresentation.Equiv.toContinuousLinearMap_mk'** 是 Mathlib 中的一个引理，位于命名空间 `
ContRepresentation.Equiv`。
形式化陈述：toContinuousLinearMap_mk' (e : V ≃L[R] W) (he : forall g, e ∘L (ρ g) = (σ 
g) ∘L e) : (mk e he).toContinuousLinearMap = e.toContinuousLinearMap
参数：e : V ≃L[R] W；he : forall g, e ∘L (ρ g) = (σ g) ∘L e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousLinearMap_mk' (e : V ≃L[R] W) (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).toContinuousLinearMap = e.toContinuousLinearMap := rfl
/-
**ContRepresentation.Equiv.toContinuousLinearEquiv_injective** 是 Mathlib 中的一个引理，
位于命名空间 `ContRepresentation.Equiv`。
形式化陈述：toContinuousLinearEquiv_injective : Function.Injective (toContinuousLinear
Equiv : (σ.Equiv ρ) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContRepresentation.Equiv.mk''.injEq`：∀ {R : Type u_1} {G : Type u_2} {V 
: Type u_3} {W : Type u_4} [inst : Monoid G] [inst_1 : Ring R]   [inst_2 : AddCo
mmGroup V] [inst_3 : Topo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma toContinuousLinearEquiv_injective :
    Function.Injective (toContinuousLinearEquiv : (σ.Equiv ρ) → _) :=
  fun φ ψ h ↦ by cases φ; cases ψ; simpa [ContIntertwiningMap.ext_iff] using h
/-
**ContRepresentation.Equiv.toContinuousLinearEquiv_inj** 是 Mathlib 中的一个引理，位于命名空间
 `ContRepresentation.Equiv`。
形式化陈述：toContinuousLinearEquiv_inj (φ ψ : σ.Equiv ρ) : φ.toContinuousLinearEquiv 
= ψ.toContinuousLinearEquiv ↔ φ = ψ
参数：φ ψ : σ.Equiv ρ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `ContRepresentation.Equiv.toContinuousLinearEquiv_injective`：toContinuous
LinearEquiv_injective : Function.Injective (toContinuousLinearEquiv : (σ.Equiv ρ
) -> _)
-/
lemma toContinuousLinearEquiv_inj (φ ψ : σ.Equiv ρ) :
    φ.toContinuousLinearEquiv = ψ.toContinuousLinearEquiv ↔ φ = ψ :=
  toContinuousLinearEquiv_injective.eq_iff
/-
**ContRepresentation.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContRepresentation.Equiv`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (Equiv ρ σ) V W where
  coe φ := φ.toContinuousLinearEquiv
  inv φ := φ.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' φ ψ h1 h2 := by cases φ; cases ψ; simp_all
/-
**ContRepresentation.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContRepresentation.Equiv`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousLinearEquivClass (σ.Equiv ρ) R W V where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul
  map_continuous f := f.cont
  inv_continuous f := f.continuous_invFun

@[simp]
/-
**ContRepresentation.Equiv.mk_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContRepresentatio
n.Equiv`。
形式化陈述：mk_apply {e : V ≃L[R] W} (he : forall g, e ∘L (ρ g) = (σ g) ∘L e) (v : V) 
: (mk e he) v = e v
参数：he : forall g, e ∘L (ρ g) = (σ g) ∘L e；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_apply {e : V ≃L[R] W} (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) (v : V) :
    (mk e he) v = e v := rfl

@[ext]
/-
**ContRepresentation.Equiv.ext** 是 Mathlib 中的一个引理，位于命名空间 `ContRepresentation.Equ
iv`。
形式化陈述：ext {φ ψ : Equiv ρ σ} (h : (φ : V -> W) = ψ) : φ = ψ
参数：h : (φ : V -> W) = ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContRepresentation.Equiv.mk''.injEq`：∀ {R : Type u_1} {G : Type u_2} {V 
: Type u_3} {W : Type u_4} [inst : Monoid G] [inst_1 : Ring R]   [inst_2 : AddCo
mmGroup V] [inst_3 : Topo…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ext {φ ψ : Equiv ρ σ} (h : (φ : V → W) = ψ) : φ = ψ := by
  cases φ; cases ψ
  simpa using h

variable (ρ) in
/-- Any continuous representation is equivalent to itself. -/
/-
**ContRepresentation.Equiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation.Eq
uiv`。
形式化陈述：refl : Equiv ρ ρ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any continuous representation is equivalent to itself.
-/
def refl : Equiv ρ ρ := mk (ContinuousLinearEquiv.refl R V) (by simp)
/-
**ContRepresentation.Equiv.toContIntertwiningMap_refl** 是 Mathlib 中的一个定理，位于命名空间 
`ContRepresentation.Equiv`。
形式化陈述：∀ {R : Type u_1} {G : Type u_2} {V : Type u_3} [inst : Monoid G] [inst_1 :
 Ring R] [inst_2 : AddCommGroup V]   [inst_3 : TopologicalSpace V] [inst_4 : IsT
opologicalAddGroup V] [inst_5 : _root_.Module R V]   {ρ : ContRepresentation R G
 V}, ↑(ContRepresentation.Equiv.refl ρ) = ContIntertwiningMap.id
参数：ContRepresentation.Equiv.refl ρ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toContIntertwiningMap_refl : (refl ρ).toContIntertwiningMap = .id := rfl
/-
**ContRepresentation.Equiv.toContinuousLinearMap_refl** 是 Mathlib 中的一个定理，位于命名空间 
`ContRepresentation.Equiv`。
形式化陈述：∀ {R : Type u_1} {G : Type u_2} {V : Type u_3} [inst : Monoid G] [inst_1 :
 Ring R] [inst_2 : AddCommGroup V]   [inst_3 : TopologicalSpace V] [inst_4 : IsT
opologicalAddGroup V] [inst_5 : _root_.Module R V]   {ρ : ContRepresentation R G
 V},   ↑(ContRepresentation.Equiv.refl ρ).toContinuousLinearEquiv = ContinuousLi
nearMap.id R V
参数：ContRepresentation.Equiv.refl ρ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toContinuousLinearMap_refl :
    (refl ρ).toContinuousLinearMap = ContinuousLinearMap.id R V := rfl
/-
**ContRepresentation.Equiv.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContRepresentat
ion.Equiv`。
形式化陈述：∀ {R : Type u_1} {G : Type u_2} {V : Type u_3} [inst : Monoid G] [inst_1 :
 Ring R] [inst_2 : AddCommGroup V]   [inst_3 : TopologicalSpace V] [inst_4 : IsT
opologicalAddGroup V] [inst_5 : _root_.Module R V]   {ρ : ContRepresentation R G
 V} (v : V), (ContRepresentation.Equiv.refl ρ) v = v
参数：v : V；ContRepresentation.Equiv.refl ρ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma refl_apply (v : V) : refl ρ v = v := rfl
/-
**ContRepresentation.Equiv.coe_toContIntertwiningMap** 是 Mathlib 中的一个定理，位于命名空间 `
ContRepresentation.Equiv`。
形式化陈述：∀ {R : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Mono
id G] [inst_1 : Ring R]   [inst_2 : AddCommGroup V] [inst_3 : TopologicalSpace V
] [inst_4 : IsTopologicalAddGroup V]   [inst_5 : _root_.Module R V] [inst_6 : Ad
dCommGroup W] [inst_7 : TopologicalSpace W]   [inst_8 : IsTopologicalAddGroup W]
 [inst_9 : _root_.Module R W] {ρ : ContRepresentation R G V}   {σ : ContRepresen
tation R G W} (φ : ρ.Equiv σ), ⇑↑φ = ⇑φ
参数：φ : ρ.Equiv σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toContIntertwiningMap : ⇑φ.toContIntertwiningMap = φ := rfl
/-
**ContRepresentation.Equiv.coe_toContinuousLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `
ContRepresentation.Equiv`。
形式化陈述：coe_toContinuousLinearMap : ⇑φ.toContinuousLinearMap = φ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toContinuousLinearMap : ⇑φ.toContinuousLinearMap = φ := rfl
/-
**ContRepresentation.Equiv.coe_invFun** 是 Mathlib 中的一个引理，位于命名空间 `ContRepresentat
ion.Equiv`。
形式化陈述：coe_invFun : φ.invFun = φ.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_invFun : φ.invFun = φ.symm := rfl
/-
**ContRepresentation.Equiv.toContinuousLinearEquiv_toContinuousLinearMap** 是 Mat
hlib 中的一个定理，位于命名空间 `ContRepresentation.Equiv`。
形式化陈述：toContinuousLinearEquiv_toContinuousLinearMap : φ.toContinuousLinearEquiv.
toContinuousLinearMap = φ.toContIntertwiningMap.toContinuousLinearMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousLinearEquiv_toContinuousLinearMap :
    φ.toContinuousLinearEquiv.toContinuousLinearMap =
      φ.toContIntertwiningMap.toContinuousLinearMap := rfl
/-
**ContRepresentation.Equiv.toContinuousLinearEquiv_apply** 是 Mathlib 中的一个定理，位于命名
空间 `ContRepresentation.Equiv`。
形式化陈述：toContinuousLinearEquiv_apply (v : V) : φ.toContinuousLinearEquiv v = φ.to
ContIntertwiningMap v
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousLinearEquiv_apply (v : V) :
    φ.toContinuousLinearEquiv v = φ.toContIntertwiningMap v := rfl

open ContinuousLinearMap in
/-- The equiv between continuous representations are symmetric. -/
@[symm]
/-
**ContRepresentation.Equiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation.Eq
uiv`。
形式化陈述：symm : Equiv σ ρ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equiv between continuous representations are symmetric.
-/
def symm : Equiv σ ρ := mk φ.toContinuousLinearEquiv.symm <| fun g ↦ by
  rw [← cancel_left' (g := φ.toContinuousLinearEquiv.toContinuousLinearMap)
    φ.toContinuousLinearEquiv.injective, ← comp_assoc, ← comp_assoc]
  simp [φ.isIntertwining g, comp_assoc]

open ContinuousLinearMap
/-
**ContRepresentation.Equiv._root_.ContinuousLinearEquiv.isIntertwining_symm_isIn
tertwining** 是 Mathlib 中的一个引理，位于命名空间 `ContRepresentation.Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousLinearEquiv.isIntertwining_symm_isIntertwining {e : V ≃L[R] W}
    (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) (g : G) :
    e.symm ∘L (σ g) = (ρ g) ∘L e.symm :=
  (mk e he).symm.isIntertwining g

@[simp]
/-
**ContRepresentation.Equiv.mk_symm** 是 Mathlib 中的一个引理，位于命名空间 `ContRepresentation
.Equiv`。
形式化陈述：mk_symm {e : V ≃L[R] W} (he : forall g, e ∘L (ρ g) = (σ g) ∘L e) : (mk e h
e).symm = mk e.symm (e.isIntertwining_symm_isIntertwining he)
参数：he : forall g, e ∘L (ρ g) = (σ g) ∘L e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_symm {e : V ≃L[R] W} (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).symm = mk e.symm (e.isIntertwining_symm_isIntertwining he) := rfl
/-
**ContRepresentation.Equiv.toLinearMap_symm** 是 Mathlib 中的一个引理，位于命名空间 `ContRepre
sentation.Equiv`。
形式化陈述：toLinearMap_symm (φ : Equiv ρ σ) : (symm φ).toLinearMap = φ.toLinearEquiv.
symm
参数：φ : Equiv ρ σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_symm (φ : Equiv ρ σ) : (symm φ).toLinearMap = φ.toLinearEquiv.symm := rfl
/-
**ContRepresentation.Equiv.coe_symm** 是 Mathlib 中的一个引理，位于命名空间 `ContRepresentatio
n.Equiv`。
形式化陈述：coe_symm (φ : Equiv ρ σ) : ⇑φ.toLinearEquiv.symm = φ.symm
参数：φ : Equiv ρ σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_symm (φ : Equiv ρ σ) : ⇑φ.toLinearEquiv.symm = φ.symm := rfl

/-- Composition of two `Equiv`s. -/
@[trans]
/-
**ContRepresentation.Equiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation.E
quiv`。
形式化陈述：trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) : Equiv ρ τ
参数：φ : Equiv ρ σ；ψ : Equiv σ τ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of two `Equiv`s.
-/
def trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) : Equiv ρ τ := mk
  (φ.toContinuousLinearEquiv.trans ψ.toContinuousLinearEquiv) <| fun g ↦ by
  rw [← ContinuousLinearEquiv.comp_coe, comp_assoc,
    φ.isIntertwining, ← comp_assoc, ψ.isIntertwining, comp_assoc]

@[simp]
/-
**ContRepresentation.Equiv.toContIntertwiningMap_trans** 是 Mathlib 中的一个引理，位于命名空间
 `ContRepresentation.Equiv`。
形式化陈述：toContIntertwiningMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) : (φ.trans ψ).
toContIntertwiningMap = ψ.toContIntertwiningMap.comp φ.toContIntertwiningMap
参数：φ : Equiv ρ σ；ψ : Equiv σ τ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContIntertwiningMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) :
    (φ.trans ψ).toContIntertwiningMap = ψ.toContIntertwiningMap.comp φ.toContIntertwiningMap := rfl

@[simp]
/-
**ContRepresentation.Equiv.toContinuousLinearMap_trans** 是 Mathlib 中的一个引理，位于命名空间
 `ContRepresentation.Equiv`。
形式化陈述：toContinuousLinearMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) : (trans φ ψ).
toContinuousLinearMap = ψ.toContinuousLinearMap.comp φ.toContinuousLinearMap
参数：φ : Equiv ρ σ；ψ : Equiv σ τ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousLinearMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) :
    (trans φ ψ).toContinuousLinearMap = ψ.toContinuousLinearMap.comp φ.toContinuousLinearMap := rfl

@[simp]
/-
**ContRepresentation.Equiv.trans_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContRepresenta
tion.Equiv`。
形式化陈述：trans_apply (φ : Equiv ρ σ) (ψ : Equiv σ τ) (v : V) : trans φ ψ v = ψ (φ v
)
参数：φ : Equiv ρ σ；ψ : Equiv σ τ；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trans_apply (φ : Equiv ρ σ) (ψ : Equiv σ τ) (v : V) :
    trans φ ψ v = ψ (φ v) := rfl

@[simp]
/-
**ContRepresentation.Equiv.apply_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContRepre
sentation.Equiv`。
形式化陈述：apply_symm_apply (φ : Equiv ρ σ) (v : W) : φ (φ.symm v) = v
参数：φ : Equiv ρ σ；v : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
-/
lemma apply_symm_apply (φ : Equiv ρ σ) (v : W) : φ (φ.symm v) = v := φ.right_inv v

@[simp]
/-
**ContRepresentation.Equiv.symm_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContRepre
sentation.Equiv`。
形式化陈述：symm_apply_apply (φ : Equiv ρ σ) (v : V) : φ.symm (φ v) = v
参数：φ : Equiv ρ σ；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
-/
lemma symm_apply_apply (φ : Equiv ρ σ) (v : V) : φ.symm (φ v) = v := φ.left_inv v

@[simp]
/-
**ContRepresentation.Equiv.trans_symm** 是 Mathlib 中的一个引理，位于命名空间 `ContRepresentat
ion.Equiv`。
形式化陈述：trans_symm (φ : Equiv ρ σ) : φ.trans φ.symm = .refl ρ
参数：φ : Equiv ρ σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContRepresentation.Equiv.ext`：ext {φ ψ : Equiv ρ σ} (h : (φ : V -> W) = 
ψ) : φ = ψ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContRepresentation.Equiv.symm_apply_apply`：symm_apply_apply (φ : Equiv ρ
 σ) (v : V) : φ.symm (φ v) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trans_symm (φ : Equiv ρ σ) : φ.trans φ.symm = .refl ρ := by ext; simp

@[simp]
/-
**ContRepresentation.Equiv.symm_trans** 是 Mathlib 中的一个引理，位于命名空间 `ContRepresentat
ion.Equiv`。
形式化陈述：symm_trans (φ : Equiv ρ σ) : φ.symm.trans φ = .refl σ
参数：φ : Equiv ρ σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContRepresentation.Equiv.ext`：ext {φ ψ : Equiv ρ σ} (h : (φ : V -> W) = 
ψ) : φ = ψ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContRepresentation.Equiv.apply_symm_apply`：apply_symm_apply (φ : Equiv ρ
 σ) (v : W) : φ (φ.symm v) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symm_trans (φ : Equiv ρ σ) : φ.symm.trans φ = .refl σ := by ext; simp

end Equiv

variable (R G V) in
/-- The trivial continuous representation of a group `G` on a `R`-module `V`. -/
/-
**ContRepresentation.trivial** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：trivial : ContRepresentation R G V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial continuous representation of a group `G` on a `R`-module `V`.
-/
def trivial : ContRepresentation R G V := ofMonoidHom 1

@[simp]
/-
**ContRepresentation.trivial_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContRepresentation
`。
形式化陈述：trivial_apply (g : G) (v : V) : trivial R G V g v = v
参数：g : G；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trivial_apply (g : G) (v : V) : trivial R G V g v = v := rfl

/-- The restriction of a continuous representation along a monoid homomorphism. -/
@[implicit_reducible]
/-
**ContRepresentation.restrict** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：restrict {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : H ->* 
G) : ContRepresentation R H V
参数：π : ContRepresentation R G V；φ : H ->* G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a continuous representation along a monoid homomorphism.
-/
def restrict {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : H →* G) :
    ContRepresentation R H V := ofMonoidHom (π.toMonoidHom.comp φ)
/-
**ContRepresentation.restrict_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContRepresentatio
n`。
形式化陈述：restrict_apply {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : 
H ->* G) (h : H) : π.restrict φ h = π (φ h)
参数：π : ContRepresentation R G V；φ : H ->* G；h : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrict_apply {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : H →* G)
    (h : H) : π.restrict φ h = π (φ h) := rfl

@[simp]
/-
**ContRepresentation.restrict_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContReprese
ntation`。
形式化陈述：restrict_apply_apply {H : Type*} [Monoid H] (π : ContRepresentation R G V)
 (φ : H ->* G) (h : H) (v : V) : π.restrict φ h v = π (φ h) v
参数：π : ContRepresentation R G V；φ : H ->* G；h : H；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrict_apply_apply {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : H →* G)
    (h : H) (v : V) : π.restrict φ h v = π (φ h) v := rfl

/-- The restriction of a continuous intertwining map along a monoid homomorphism. -/
/-
**ContRepresentation._root_.ContIntertwiningMap.restrict** 是 Mathlib 中的一个定义，位于命名
空间 `ContRepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a continuous intertwining map along a monoid homomorphism.
-/
def _root_.ContIntertwiningMap.restrict {H : Type*} [Monoid H] {π : ContRepresentation R G V}
    {π' : ContRepresentation R G W} (φ : H →* G) (f : π →ⁱL π') :
    π.restrict φ →ⁱL π'.restrict φ where
  __ := f.toContinuousLinearMap
  isIntertwining' h := by
    ext; simp [f.toContinuousLinearMap_apply, f.isIntertwining]
/-
**ContRepresentation._root_.ContIntertwiningMap.restrict_toContinuousLinearMap**
 是 Mathlib 中的一个引理，位于命名空间 `ContRepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContIntertwiningMap.restrict_toContinuousLinearMap {H : Type*} [Monoid H]
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W} (φ : H →* G) (f : π →ⁱL π') :
    (f.restrict φ).toContinuousLinearMap = f.toContinuousLinearMap := rfl
/-
**ContRepresentation._root_.ContIntertwiningMap.restrict_apply** 是 Mathlib 中的一个引
理，位于命名空间 `ContRepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.ContIntertwiningMap.restrict_apply {H : Type*} [Monoid H]
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W} (φ : H →* G)
    (f : π →ⁱL π') (v : V) : f.restrict φ v = f v := rfl
/-
**ContRepresentation._root_.ContIntertwiningMap.restrict_sub** 是 Mathlib 中的一个引理，
位于命名空间 `ContRepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContIntertwiningMap.restrict_sub {H : Type*} [Monoid H]
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W} (φ : H →* G)
    (f g : π →ⁱL π') : (f - g).restrict φ = f.restrict φ - g.restrict φ := rfl

/-- The submodule of `G`-invariant elements of a continuous representation. -/
/-
**ContRepresentation.invariants** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：invariants (π : ContRepresentation R G V) : Submodule R V where carrier
参数：π : ContRepresentation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule of `G`-invariant elements of a continuous representation.
-/
def invariants (π : ContRepresentation R G V) : Submodule R V where
  carrier := {v | ∀ g, π g v = v}
  zero_mem' := by simp
  add_mem' _ _ := by simp_all
  smul_mem' _ _ hv g := by simp [hv g]

@[simp]
/-
**ContRepresentation.mem_invariants** 是 Mathlib 中的一个引理，位于命名空间 `ContRepresentatio
n`。
形式化陈述：mem_invariants {π : ContRepresentation R G V} (v : V) : v in π.invariants 
↔ forall g, π g v = v
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_invariants {π : ContRepresentation R G V} (v : V) :
    v ∈ π.invariants ↔ ∀ g, π g v = v := Iff.rfl

/-- The map induced on `G`-invariant elements by a continuous intertwining map. -/
/-
**ContRepresentation._root_.ContIntertwiningMap.mapInvariants** 是 Mathlib 中的一个定义
，位于命名空间 `ContRepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map induced on `G`-invariant elements by a continuous intertwining map.
-/
def _root_.ContIntertwiningMap.mapInvariants
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W}
    (f : π →ⁱL π') : π.invariants →L[R] π'.invariants :=
  f.toContinuousLinearMap.restrict <| by
    simp +contextual [f.toContinuousLinearMap_apply, ← f.isIntertwining]

-- provided for rewrite, this lemma should be used when `mapInvariants` is
-- applied to `(homogeneousCochains X).X 0`
/-
**ContRepresentation._root_.ContIntertwiningMap.mapInvariants_apply** 是 Mathlib 
中的一个引理，位于命名空间 `ContRepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContIntertwiningMap.mapInvariants_apply
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W}
    (f : π →ⁱL π') (v : π.invariants) :
    f.mapInvariants v = f v := rfl

@[simp]
/-
**ContRepresentation._root_.ContIntertwiningMap.mk_mapInvariants_apply** 是 Mathl
ib 中的一个引理，位于命名空间 `ContRepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContIntertwiningMap.mk_mapInvariants_apply
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W}
    (f : π →ⁱL π') (v : V) (hv : v ∈ π.invariants) :
    f.mapInvariants ⟨v, hv⟩ = f v := rfl

variable {H : Type*} [Monoid H]
/-
**ContRepresentation.invariants_le_invariants_restrict** 是 Mathlib 中的一个引理，位于命名空间
 `ContRepresentation`。
形式化陈述：invariants_le_invariants_restrict (π : ContRepresentation R G V) (φ : H ->
* G) : π.invariants <= (π.restrict φ).invariants
参数：π : ContRepresentation R G V；φ : H ->* G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma invariants_le_invariants_restrict (π : ContRepresentation R G V) (φ : H →* G) :
    π.invariants ≤ (π.restrict φ).invariants :=
  fun _ hv h ↦ hv (φ h)

variable {π : ContRepresentation R G V} {π' : ContRepresentation R H W}

/-- Given a monoid homomorphism `φ : H →* G`, a `G`-representation `π` and an
`H`-representation `π'`, a continuous intertwining map `f : π.restrict φ →ⁱL π'` induces a
continuous linear map `π.invariants →L[R] π'.invariants` between the invariant submodules. -/
/-
**ContRepresentation._root_.ContIntertwiningMap.mapInvariantsOfRes** 是 Mathlib 中
的一个定义，位于命名空间 `ContRepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a monoid homomorphism `φ : H →* G`, a `G`-representation `π` and an
`H`-representation `π'`, a continuous intertwining map `f : π.restrict φ →ⁱL π'`
 induces a
continuous linear map `π.invariants →L[R] π'.invariants` between the invariant s
ubmodules.
-/
def _root_.ContIntertwiningMap.mapInvariantsOfRes (φ : H →* G)
    (f : π.restrict φ →ⁱL π') : π.invariants →L[R] π'.invariants :=
  f.toContinuousLinearMap.restrict <| by
    simp +contextual [f.toContinuousLinearMap_apply, ← f.isIntertwining]

-- provided for rewriting
/-
**ContRepresentation._root_.ContIntertwiningMap.mapInvariantsOfRes_apply** 是 Mat
hlib 中的一个引理，位于命名空间 `ContRepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContIntertwiningMap.mapInvariantsOfRes_apply (φ : H →* G)
    (f : π.restrict φ →ⁱL π') (v : π.invariants) :
    f.mapInvariantsOfRes φ v = f v := rfl

@[simp]
/-
**ContRepresentation._root_.ContIntertwiningMap.mk_mapInvariantsOfRes_apply** 是 
Mathlib 中的一个引理，位于命名空间 `ContRepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContIntertwiningMap.mk_mapInvariantsOfRes_apply (φ : H →* G)
    (f : π.restrict φ →ⁱL π') (v : V) (hv : v ∈ π.invariants) :
    f.mapInvariantsOfRes φ ⟨v, hv⟩ = f v := rfl

-- TODO : define `IsTopologicalMonoid` and then replace `Homeomorph.mulLeft g⁻¹` with the
-- `ContinuousMap.mulRight g` to make `coind₁` work for monoids.
variable {G H : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace R]
  [ContinuousSMul R V] [ContinuousSMul R W] [Group H] [TopologicalSpace H]
  (φ : G →ₜ* H) (π : ContRepresentation R G V)

/-- The underlying module of the coinduced continuous representation. -/
@[simps]
/-
**ContRepresentation.coindV** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：coindV : Submodule R C(H, V) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying module of the coinduced continuous representation.
-/
def coindV : Submodule R C(H, V) where
  carrier   := {f | ∀ g h, f (φ g * h) = π g (f h)}
  add_mem'  := by simp +contextual
  zero_mem' := by simp
  smul_mem' := by simp +contextual

@[simp]
/-
**ContRepresentation.mem_coindV** 是 Mathlib 中的一个引理，位于命名空间 `ContRepresentation`。
形式化陈述：mem_coindV (f : C(H, V)) : f in π.coindV φ ↔ forall g h, f (φ g * h) = π g
 (f h)
参数：f : C(H, V)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
-/
lemma mem_coindV (f : C(H, V)) : f ∈ π.coindV φ ↔ ∀ g h, f (φ g * h) = π g (f h) := Iff.rfl
/-
**ContRepresentation.** 是 Mathlib 中的一个实例，位于命名空间 `ContRepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousSMul R (π.coindV φ) where
  continuous_smul := by continuity

variable [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- The coinduced continuous representation where the action of `H` is defined by
  `h ↦ f ↦ f ∘ (· * h)`. -/
@[simps]
/-
**ContRepresentation.coind** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ)
 where toMonoidHom.toFun h
参数：π : ContRepresentation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coinduced continuous representation where the action of `H` is defined by
  `h ↦ f ↦ f ∘ (· * h)`.
-/
def coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ) where
  toMonoidHom.toFun h := {
    toFun | ⟨f, hf⟩ => ⟨f.comp (ContinuousMap.mulRight h), by simp [mul_assoc, hf _]⟩
    map_add' _ _ := by simp
    map_smul' _ _ := by simp
    cont := continuous_induced_rng.2 <| by
      simpa using! (ContinuousMap.mulRight h).continuous_precomp.comp continuous_subtype_val}
  toMonoidHom.map_one' := by ext; simp
  toMonoidHom.map_mul' h1 h2 := by ext; simp [ContinuousMap.mulRight_mul]

open ContinuousMap

/-- Given a continuous representation `π` of `G` on `V`,
this defines a Continuous representation `π.coind₁` of `G` on the function space `C(G,V)`.
The action of an element `g : G` is defined by `f ↦ (x ↦ π g (f (g⁻¹ * x)))`.
This new representation of `G` is isomorphic to the continuous coinduction
of the trivial representation of the trivial subgroup of `G`, but the action has been
twisted so that the map `const : V → C(G,V)` is an intertwining map. -/
/-
**ContRepresentation.coind** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ)
 where toMonoidHom.toFun h
参数：π : ContRepresentation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous representation `π` of `G` on `V`,
this defines a Continuous representation `π.coind₁` of `G` on the function space
 `C(G,V)`.
The action of an element `g : G` is defined by `f ↦ (x ↦ π g (f (g⁻¹ * x)))`.
This new representation of `G` is isomorphic to the continuous coinduction
of the trivial representation of the trivial subgroup of `G`, but the action has
 been
twisted so that the map `const : V → C(G,V)` is an intertwining map.
-/
def coind₁ (π : ContRepresentation R G V) :
    ContRepresentation R G C(G, V) where
  toMonoidHom.toFun g := {
    toFun f := .comp (π g) (f.comp (ContinuousMap.mulLeft g⁻¹))
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
    cont := (continuous_postcomp _).comp (continuous_precomp _)
  }
  toMonoidHom.map_one' := by ext; simp
  toMonoidHom.map_mul' _ _ := by ext; simp [mul_assoc]

@[simp]
/-
**ContRepresentation.coind** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ)
 where toMonoidHom.toFun h
参数：π : ContRepresentation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coind₁_apply_apply (π : ContRepresentation R G V) (g : G) (f : C(G, V)) (x : G) :
    π.coind₁ g f x = π g (f (g⁻¹ * x)) := rfl

/-- The functoriality of `coind₁`. -/
@[simps]
/-
**ContRepresentation.coind** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ)
 where toMonoidHom.toFun h
参数：π : ContRepresentation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functoriality of `coind₁`.
-/
def coind₁Map {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} (f : π₁ →ⁱL π₂) :
    coind₁ π₁ →ⁱL coind₁ π₂ where
  toFun := (f : ContinuousMap _ _).comp
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  isIntertwining' g := by ext; simp [f.isIntertwining]
  cont := continuous_postcomp _

/-- The naturality of the transformation from `𝟭 ⟶ coind₁`. -/
@[simps]
/-
**ContRepresentation.coind** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ)
 where toMonoidHom.toFun h
参数：π : ContRepresentation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The naturality of the transformation from `𝟭 ⟶ coind₁`.
-/
def coind₁ι (π : ContRepresentation R G V) : π →ⁱL coind₁ π where
  toFun := ContinuousMap.const G
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' := by aesop
  cont := continuous_const'

/-- The equivalence between `coind₁` and `coind` of the trivial representation of trivial
  subgroup of `G`. -/
/-
**ContRepresentation.coind** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ)
 where toMonoidHom.toFun h
参数：π : ContRepresentation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `coind₁` and `coind` of the trivial representation of tr
ivial
  subgroup of `G`.
-/
def coind₁Equivcoind : (coind₁ (.trivial R (⊥ : Subgroup G) V)).Equiv
  (coind 1 (.trivial R G V)) := .mk (Submodule.topContEquiv.symm.trans <|
    ContinuousLinearEquiv.ofEq _ _ (by simp [SetLike.ext_iff])) <| fun g ↦ by
    simp [Subsingleton.elim g 1, ContinuousLinearMap.one_def]

section coind₁ResMap

variable [ContinuousSMul R U] {π' : ContRepresentation R H W} {π}

/-- Given a continuous group homomorphism `φ : H →ₜ* G`, precomposition with `φ` defines a
continuous intertwining map `π.coind₁.restrict φ →ⁱL (π.restrict φ).coind₁`. -/
/-
**ContRepresentation.coind** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ)
 where toMonoidHom.toFun h
参数：π : ContRepresentation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous group homomorphism `φ : H →ₜ* G`, precomposition with `φ` def
ines a
continuous intertwining map `π.coind₁.restrict φ →ⁱL (π.restrict φ).coind₁`.
-/
def coind₁Res (φ : H →ₜ* G) (π : ContRepresentation R G V) :
    π.coind₁.restrict (φ : H →* G) →ⁱL (π.restrict (φ : H →* G)).coind₁ where
  __ := ContinuousMap.compCLM R V φ.toContinuousMap
  isIntertwining' h := by
    ext F x
    simp [map_mul, map_inv]

@[simp]
/-
**ContRepresentation.coind** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ)
 where toMonoidHom.toFun h
参数：π : ContRepresentation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coind₁Res_apply (φ : H →ₜ* G) (π : ContRepresentation R G V) (F : C(G, V)) (x : H) :
    coind₁Res φ π F x = F (φ x) := rfl

/-- Given a continuous group homomorphism `φ : H →ₜ* G`, a continuous intertwining map
`f : π.restrict φ →ⁱL π'` induces a continuous intertwining map
`π.coind₁.restrict φ →ⁱL π'.coind₁`, sending `F : C(G, V)` to `f ∘ F ∘ φ : C(H, W)`. -/
/-
**ContRepresentation.coind** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ)
 where toMonoidHom.toFun h
参数：π : ContRepresentation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous group homomorphism `φ : H →ₜ* G`, a continuous intertwining m
ap
`f : π.restrict φ →ⁱL π'` induces a continuous intertwining map
`π.coind₁.restrict φ →ⁱL π'.coind₁`, sending `F : C(G, V)` to `f ∘ F ∘ φ : C(H, 
W)`.
-/
def coind₁ResMap (φ : H →ₜ* G) (f : π.restrict (φ : H →* G) →ⁱL π') :
    π.coind₁.restrict (φ : H →* G) →ⁱL π'.coind₁ :=
  (coind₁Map f).comp (coind₁Res φ π)

@[simp]
/-
**ContRepresentation.coind** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ)
 where toMonoidHom.toFun h
参数：π : ContRepresentation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coind₁ResMap_apply (φ : H →ₜ* G) (f : π.restrict (φ : H →* G) →ⁱL π') (F : C(G, V))
    (x : H) : coind₁ResMap φ f F x = f (F (φ x)) := rfl

/-- The naturality of `coind₁ι` with respect to `coind₁ResMap`. -/
/-
**ContRepresentation.coind** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ)
 where toMonoidHom.toFun h
参数：π : ContRepresentation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The naturality of `coind₁ι` with respect to `coind₁ResMap`.
-/
lemma coind₁ResMap_comp_coind₁ι_restrict (φ : H →ₜ* G) (f : π.restrict (φ : H →* G) →ⁱL π') :
    (coind₁ResMap φ f).comp (π.coind₁ι.restrict (φ : H →* G)) = π'.coind₁ι.comp f := rfl
/-
**ContRepresentation.coind** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ)
 where toMonoidHom.toFun h
参数：π : ContRepresentation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coind₁Map_comp_coind₁ResMap (φ : H →ₜ* G) {σ : ContRepresentation R H U}
    (f : π.restrict φ →ⁱL π') (g : π' →ⁱL σ) :
    (coind₁Map g).comp (coind₁ResMap φ f) = coind₁ResMap φ (g.comp f) := rfl
/-
**ContRepresentation.coind** 是 Mathlib 中的一个定义，位于命名空间 `ContRepresentation`。
形式化陈述：coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ)
 where toMonoidHom.toFun h
参数：π : ContRepresentation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coind₁ResMap_comp_coind₁Map_restrict (φ : H →ₜ* G) {ρ : ContRepresentation R G U}
    (g : ρ →ⁱL π) (f : π.restrict (φ : H →* G) →ⁱL π') :
    (coind₁ResMap φ f).comp ((coind₁Map g).restrict (φ : H →* G)) =
      coind₁ResMap φ (f.comp (g.restrict (φ : H →* G))) := rfl

end coind₁ResMap

end ContRepresentation

