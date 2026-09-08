/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Topology.UniformSpace.ProdApproximation

/-!
# Abstract measures on topological spaces

We define an "abstract measure" on `X`, with values in a normed ring `R`, to be an `R`-linear
functional on continuous maps `X → R`. This is an important construction in p-adic analysis (where
the Iwasawa algebra is defined as the space of abstract measures on `ℤ_[p]` with values in `ℚ_[p]`).
-/

public section

open ContinuousMap

variable {X Y R E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Module R E] --[ContinuousSMul R E]

section Defs

/-!
### Basic definitions
-/

variable (X R E) in
/--
The space of `E`-valued measures on `X`, i.e. continuous linear maps `C(X, R) → E`. (The case
`R = E` is the most important case.)

This is the same space `C(X, R) →L[R] E`, but we do not want it to inherit the default
(norm) topology, so we make a type synonym.
-/
/-
**AbstractMeasure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：(X : Type u_1) →   (R : Type u_3) →     (E : Type u_4) →       [Topologica
lSpace X] →         [inst : AddCommGroup E] →           [TopologicalSpace E] →  
           [inst_2 : CommRing R] →               [inst_3 : TopologicalSpace R] →
 [IsTopologicalRing R] → [_root_.Module R E] → Type (max (max u_3 u_1) u_4)
参数：max u_3 u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of `E`-valued measures on `X`, i.e. continuous linear maps `C(X, R) → 
E`. (The case
`R = E` is the most important case.)

This is the same space `C(X, R) →L[R] E`, but we do not want it to inherit the d
efault
(norm) topology, so we make a type synonym.
-/
@[expose] def AbstractMeasure := C(X, R) →L[R] E

@[inherit_doc]
scoped [AbstractMeasure] notation "D(" X ", " R ")" => AbstractMeasure X R R

end Defs

namespace AbstractMeasure

section NoContinuousSMul

/-- Inherit `FunLike` structure from `C(X, R) →L[R] E`. -/
/-
**AbstractMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `AbstractMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inherit `FunLike` structure from `C(X, R) →L[R] E`.
-/
instance : FunLike (AbstractMeasure X R E) C(X, R) E :=
  inferInstanceAs (FunLike (C(X, R) →L[R] E) C(X, R) E)

/-- Inherit `ContinuousLinearMapClass` structure from `C(X, R) →L[R] E`. -/
/-
**AbstractMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `AbstractMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inherit `ContinuousLinearMapClass` structure from `C(X, R) →L[R] E`.
-/
instance : ContinuousLinearMapClass (AbstractMeasure X R E) R C(X, R) E :=
  inferInstanceAs (ContinuousLinearMapClass (C(X, R) →L[R] E) R C(X, R) E)

/-- Inherit `AddCommGroup` structure from `C(X, R) →L[R] E`. -/
/-
**AbstractMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `AbstractMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inherit `AddCommGroup` structure from `C(X, R) →L[R] E`.
-/
instance : AddCommGroup (AbstractMeasure X R E) :=
  inferInstanceAs (AddCommGroup (C(X, R) →L[R] E))
/-
**AbstractMeasure.isAddApply** 是 Mathlib 中的一个实例，位于命名空间 `AbstractMeasure`。
形式化陈述：isAddApply : IsAddApply (AbstractMeasure X R E) C(X, R) E where add_apply 
_ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isAddApply : IsAddApply (AbstractMeasure X R E) C(X, R) E where
  add_apply _ _ _ := rfl

end NoContinuousSMul

section ContinuousSMul

variable [ContinuousSMul R E]

/-- Inherit `R`-module structure from `C(X, R) →L[R] E`. -/
/-
**AbstractMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `AbstractMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inherit `R`-module structure from `C(X, R) →L[R] E`.
-/
instance : Module R (AbstractMeasure X R E) :=
  inferInstanceAs (Module R (C(X, R) →L[R] E))
/-
**AbstractMeasure.isSMulApply** 是 Mathlib 中的一个实例，位于命名空间 `AbstractMeasure`。
形式化陈述：isSMulApply : IsSMulApply R (AbstractMeasure X R E) C(X, R) E where smul_a
pply _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isSMulApply : IsSMulApply R (AbstractMeasure X R E) C(X, R) E where
  smul_apply _ _ _ := rfl

/-- The defining equivalence between measures and continuous linear maps on continuous functions. -/
/-
**AbstractMeasure.toCLMEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AbstractMeasure`。
形式化陈述：toCLMEquiv : AbstractMeasure X R E ≃ₗ[R] C(X, R) ->L[R] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The defining equivalence between measures and continuous linear maps on continuo
us functions.
-/
def toCLMEquiv : AbstractMeasure X R E ≃ₗ[R] C(X, R) →L[R] E :=
  LinearEquiv.refl _ _
/-
**AbstractMeasure.coe_toCLMEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AbstractMeasure`。
形式化陈述：∀ {X : Type u_1} {R : Type u_3} {E : Type u_4} [inst : TopologicalSpace X]
 [inst_1 : AddCommGroup E]   [inst_2 : TopologicalSpace E] [inst_3 : IsTopologic
alAddGroup E] [inst_4 : CommRing R] [inst_5 : TopologicalSpace R]   [inst_6 : Is
TopologicalRing R] [inst_7 : _root_.Module R E] [inst_8 : ContinuousSMul R E] (μ
 : AbstractMeasure X R E)   (f : C(X, R)), (AbstractMeasure.toCLMEquiv μ) f = μ 
f
参数：μ : AbstractMeasure X R E；f : C(X, R)；AbstractMeasure.toCLMEquiv μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
-/
@[simp] lemma coe_toCLMEquiv (μ : AbstractMeasure X R E) (f : C(X, R)) :
    toCLMEquiv μ f = μ f :=
  (rfl)
/-
**AbstractMeasure.coe_symm_toCLMEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AbstractMeasure
`。
形式化陈述：∀ {X : Type u_1} {R : Type u_3} {E : Type u_4} [inst : TopologicalSpace X]
 [inst_1 : AddCommGroup E]   [inst_2 : TopologicalSpace E] [inst_3 : IsTopologic
alAddGroup E] [inst_4 : CommRing R] [inst_5 : TopologicalSpace R]   [inst_6 : Is
TopologicalRing R] [inst_7 : _root_.Module R E] [inst_8 : ContinuousSMul R E] (L
 : C(X, R) →L[R] E)   (f : C(X, R)), (AbstractMeasure.toCLMEquiv.symm L) f = L f
参数：L : C(X, R) →L[R] E；f : C(X, R)；AbstractMeasure.toCLMEquiv.symm L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
-/
@[simp] lemma coe_symm_toCLMEquiv (L : C(X, R) →L[R] E) (f : C(X, R)) :
    toCLMEquiv.symm L f = L f :=
  (rfl)

variable (R) in
/-- The Dirac measure, "evaluation at `x`". -/
/-
**AbstractMeasure.dirac** 是 Mathlib 中的一个定义，位于命名空间 `AbstractMeasure`。
形式化陈述：dirac (x : X) : D(X, R)
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Dirac measure, "evaluation at `x`".
-/
def dirac (x : X) : D(X, R) :=
  toCLMEquiv.symm (ContinuousMap.evalCLM R x)
/-
**AbstractMeasure.dirac_apply** 是 Mathlib 中的一个定理，位于命名空间 `AbstractMeasure`。
形式化陈述：∀ {X : Type u_1} {R : Type u_3} [inst : TopologicalSpace X] [inst_1 : Comm
Ring R] [inst_2 : TopologicalSpace R]   [inst_3 : IsTopologicalRing R] (x : X) (
f : C(X, R)), (AbstractMeasure.dirac R x) f = f x
参数：x : X；f : C(X, R)；AbstractMeasure.dirac R x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma dirac_apply (x : X) (f : C(X, R)) : dirac R x f = f x := (rfl)

section Map

/-- Measures can be pushed forward (`R`-linearly) along continuous maps. -/
/-
**AbstractMeasure.map** 是 Mathlib 中的一个定义，位于命名空间 `AbstractMeasure`。
形式化陈述：map (f : C(X, Y)) : AbstractMeasure X R E ->ₗ[R] AbstractMeasure Y R E whe
re toFun μ
参数：f : C(X, Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Measures can be pushed forward (`R`-linearly) along continuous maps.
-/
def map (f : C(X, Y)) : AbstractMeasure X R E →ₗ[R] AbstractMeasure Y R E where
  toFun μ := μ ∘L f.compCLM R R
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-
**AbstractMeasure.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `AbstractMeasure`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {R : Type u_3} {E : Type u_4} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : AddCommGroup E] [inst_
3 : TopologicalSpace E] [inst_4 : IsTopologicalAddGroup E] [inst_5 : CommRing R]
   [inst_6 : TopologicalSpace R] [inst_7 : IsTopologicalRing R] [inst_8 : _root_
.Module R E]   [inst_9 : ContinuousSMul R E] (f : C(X, Y)) (μ : AbstractMeasure 
X R E) (g : C(Y, R)),   ((AbstractMeasure.map f) μ) g = μ (g.comp f)
参数：f : C(X, Y)；μ : AbstractMeasure X R E；g : C(Y, R)；(AbstractMeasure.map f) μ；g
.comp f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma map_apply (f : C(X, Y)) (μ : AbstractMeasure X R E) (g : C(Y, R)) :
    map f μ g = μ (g.comp f) :=
  (rfl)
/-
**AbstractMeasure.map_map** 是 Mathlib 中的一个定理，位于命名空间 `AbstractMeasure`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {R : Type u_3} {E : Type u_4} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : AddCommGroup E] [inst_
3 : TopologicalSpace E] [inst_4 : IsTopologicalAddGroup E] [inst_5 : CommRing R]
   [inst_6 : TopologicalSpace R] [inst_7 : IsTopologicalRing R] [inst_8 : _root_
.Module R E]   [inst_9 : ContinuousSMul R E] {Z : Type u_5} [inst_10 : Topologic
alSpace Z] (f : C(X, Y)) (g : C(Y, Z))   (μ : AbstractMeasure X R E), (AbstractM
easure.map g) ((AbstractMeasure.map f) μ) = (AbstractMeasure.map (g.comp f)) μ
参数：f : C(X, Y)；g : C(Y, Z)；μ : AbstractMeasure X R E；AbstractMeasure.map g；(Abst
ractMeasure.map f) μ；AbstractMeasure.map (g.comp f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma map_map {Z : Type*} [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (μ : AbstractMeasure X R E) :
    map g (map f μ) = map (g.comp f) μ :=
  (rfl)

@[simp]
/-
**AbstractMeasure.map_id** 是 Mathlib 中的一个引理，位于命名空间 `AbstractMeasure`。
形式化陈述：map_id (μ : AbstractMeasure X R E) : map (.id X) μ = μ
参数：μ : AbstractMeasure X R E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_id (μ : AbstractMeasure X R E) :
    map (.id X) μ = μ :=
  (rfl)
/-
**AbstractMeasure.map_dirac** 是 Mathlib 中的一个定理，位于命名空间 `AbstractMeasure`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {R : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : CommRing R] [inst_3 : TopologicalSpac
e R] [inst_4 : IsTopologicalRing R] (f : C(X, Y)) (x : X),   (AbstractMeasure.ma
p f) (AbstractMeasure.dirac R x) = AbstractMeasure.dirac R (f x)
参数：f : C(X, Y)；x : X；AbstractMeasure.map f；AbstractMeasure.dirac R x；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
-/
@[simp] lemma map_dirac (f : C(X, Y)) (x : X) :
    map f (dirac R x) = dirac R (f x) :=
  (rfl)

end Map

section Prod

/-!
### Product structure
-/

-- note we define `contractSnd` first, because `f.curry` only works one way round

/-- Send a measure `ν` on `Y` and a function `f` on `X × Y` to the function on `X` given by
`x ↦ ν (f (x, ·))`, or more suggestively, `x ↦ ∫ f(x, y) dμ(y)`. -/
/-
**AbstractMeasure.contractSnd** 是 Mathlib 中的一个定义，位于命名空间 `AbstractMeasure`。
形式化陈述：contractSnd : D(Y, R) ->ₗ[R] C(X × Y, R) ->ₗ[R] C(X, R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Send a measure `ν` on `Y` and a function `f` on `X × Y` to the function on `X` g
iven by
`x ↦ ν (f (x, ·))`, or more suggestively, `x ↦ ∫ f(x, y) dμ(y)`.
-/
def contractSnd : D(Y, R) →ₗ[R] C(X × Y, R) →ₗ[R] C(X, R) :=
  LinearMap.mk₂ R (fun ν f ↦ comp ν f.curry) ?_ ?_ ?_ ?_ where finally
    all_goals intros; ext; simp

/-- Send a measure `μ` on `X` and a function `f` on `X × Y` to the function on `Y` given by
`y ↦ μ (f (·, y))`, or more suggestively, `y ↦ ∫ f(x, y) dμ(x)`. -/
/-
**AbstractMeasure.contractFst** 是 Mathlib 中的一个定义，位于命名空间 `AbstractMeasure`。
形式化陈述：contractFst : D(X, R) ->ₗ[R] C(X × Y, R) ->ₗ[R] C(Y, R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Send a measure `μ` on `X` and a function `f` on `X × Y` to the function on `Y` g
iven by
`y ↦ μ (f (·, y))`, or more suggestively, `y ↦ ∫ f(x, y) dμ(x)`.
-/
def contractFst : D(X, R) →ₗ[R] C(X × Y, R) →ₗ[R] C(Y, R) :=
  ((prodSwap.compCLM R R).toLinearMap.lcomp R _).comp contractSnd

variable (μ : D(X, R)) (ν : D(Y, R))
/-
**AbstractMeasure.contractFst_apply** 是 Mathlib 中的一个定理，位于命名空间 `AbstractMeasure`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {R : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : CommRing R] [inst_3 : TopologicalSpac
e R] [inst_4 : IsTopologicalRing R] (μ : AbstractMeasure X R R)   (f : C(X × Y, 
R)) (y : Y),   ((AbstractMeasure.contractFst μ) f) y = μ { toFun := fun x => f (
x, y), continuous_toFun := ⋯ }
参数：μ : AbstractMeasure X R R；f : C(X × Y, R)；y : Y；(AbstractMeasure.contractFst 
μ) f；x, y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousMap.instSMulCommClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] {R : Type u_3} {R₁ : Type u_4} {M : Type u_5} [inst_1 : TopologicalSpace M
]   [inst_2 : SMul R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma contractFst_apply (f : C(X × Y, R)) (y : Y) :
    contractFst μ f y = μ ⟨fun x ↦ f (x, y), by continuity⟩ :=
  (rfl)
/-
**AbstractMeasure.contractSnd_apply** 是 Mathlib 中的一个定理，位于命名空间 `AbstractMeasure`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {R : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : CommRing R] [inst_3 : TopologicalSpac
e R] [inst_4 : IsTopologicalRing R] (ν : AbstractMeasure Y R R)   (f : C(X × Y, 
R)) (x : X),   ((AbstractMeasure.contractSnd ν) f) x = ν { toFun := fun y => f (
x, y), continuous_toFun := ⋯ }
参数：ν : AbstractMeasure Y R R；f : C(X × Y, R)；x : X；(AbstractMeasure.contractSnd 
ν) f；x, y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousMap.instSMulCommClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] {R : Type u_3} {R₁ : Type u_4} {M : Type u_5} [inst_1 : TopologicalSpace M
]   [inst_2 : SMul R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma contractSnd_apply (f : C(X × Y, R)) (x : X) :
    contractSnd ν f x = ν ⟨fun y ↦ f (x, y), by continuity⟩ :=
  (rfl)
/-
**AbstractMeasure.contractFst_dirac** 是 Mathlib 中的一个引理，位于命名空间 `AbstractMeasure`。
形式化陈述：contractFst_dirac (x : X) (y : Y) (f : C(X × Y, R)) : contractFst (dirac R
 x) f y = f (x, y)
参数：x : X；y : Y；f : C(X × Y, R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousMap.instSMulCommClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] {R : Type u_3} {R₁ : Type u_4} {M : Type u_5} [inst_1 : TopologicalSpace M
]   [inst_2 : SMul R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma contractFst_dirac (x : X) (y : Y) (f : C(X × Y, R)) :
    contractFst (dirac R x) f y = f (x, y) :=
  (rfl)
/-
**AbstractMeasure.contractSnd_dirac** 是 Mathlib 中的一个引理，位于命名空间 `AbstractMeasure`。
形式化陈述：contractSnd_dirac (x : X) (y : Y) (f : C(X × Y, R)) : contractSnd (dirac R
 y) f x = f (x, y)
参数：x : X；y : Y；f : C(X × Y, R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousMap.instSMulCommClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] {R : Type u_3} {R₁ : Type u_4} {M : Type u_5} [inst_1 : TopologicalSpace M
]   [inst_2 : SMul R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma contractSnd_dirac (x : X) (y : Y) (f : C(X × Y, R)) :
    contractSnd (dirac R y) f x = f (x, y) :=
  (rfl)

section LocallyCompact

variable [LocallyCompactSpace X] [LocallyCompactSpace Y]

/-- `AbstractMeasure.contractSnd` bundled with continuity in the function argument. -/
/-
**AbstractMeasure.contractSndCLM** 是 Mathlib 中的一个定义，位于命名空间 `AbstractMeasure`。
形式化陈述：contractSndCLM : D(Y, R) ->ₗ[R] C(X × Y, R) ->L[R] C(X, R) where toFun ν
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AbstractMeasure.contractSnd` bundled with continuity in the function argument.
-/
def contractSndCLM : D(Y, R) →ₗ[R] C(X × Y, R) →L[R] C(X, R) where
  toFun ν := ⟨contractSnd ν, by
    refine continuous_of_continuous_uncurry _ (ν.continuous.comp ?_)
    apply continuous_of_continuous_uncurry
    rw [← (Homeomorph.prodAssoc C(X × Y, R) X Y).symm.comp_continuous_iff']
    exact ContinuousEval.continuous_eval⟩
  map_add' _ _ := ContinuousLinearMap.coe_injective.eq_iff.mp <| contractSnd.map_add _ _
  map_smul' _ _ := ContinuousLinearMap.coe_injective.eq_iff.mp <| contractSnd.map_smul _ _

/-- `AbstractMeasure.contractFst` bundled with continuity in the function argument. -/
/-
**AbstractMeasure.contractFstCLM** 是 Mathlib 中的一个定义，位于命名空间 `AbstractMeasure`。
形式化陈述：contractFstCLM : D(X, R) ->ₗ[R] C(X × Y, R) ->L[R] C(Y, R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AbstractMeasure.contractFst` bundled with continuity in the function argument.
-/
def contractFstCLM : D(X, R) →ₗ[R] C(X × Y, R) →L[R] C(Y, R) :=
  ((ContinuousMap.prodSwap.compCLM R R).lcomp _).comp contractSndCLM

/-- "Left-handed" version of the natural product map on measures (acting on functions
as first integrating along `X`, and then integrating the result along `Y`). -/
/-
**AbstractMeasure.prodMk** 是 Mathlib 中的一个定义，位于命名空间 `AbstractMeasure`。
形式化陈述：prodMk : D(X, R) ->ₗ[R] D(Y, R) ->ₗ[R] D(X × Y, R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
"Left-handed" version of the natural product map on measures (acting on function
s
as first integrating along `X`, and then integrating the result along `Y`).
-/
def prodMk : D(X, R) →ₗ[R] D(Y, R) →ₗ[R] D(X × Y, R) :=
  (ContinuousLinearMap.llcomp _ _ _ R).comp contractFstCLM
/-
**AbstractMeasure.prodMk_apply** 是 Mathlib 中的一个定理，位于命名空间 `AbstractMeasure`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {R : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : CommRing R] [inst_3 : TopologicalSpac
e R] [inst_4 : IsTopologicalRing R] (μ : AbstractMeasure X R R)   (ν : AbstractM
easure Y R R) [inst_5 : LocallyCompactSpace X] [inst_6 : LocallyCompactSpace Y] 
(f : C(X × Y, R)),   ((AbstractMeasure.prodMk μ) ν) f = ν ((AbstractMeasure.cont
ractFst μ) f)
参数：μ : AbstractMeasure X R R；ν : AbstractMeasure Y R R；f : C(X × Y, R)；(Abstract
Measure.prodMk μ) ν；(AbstractMeasure.contractFst μ) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
-/
@[simp] lemma prodMk_apply (f : C(X × Y, R)) :
  prodMk μ ν f = ν (μ.contractFst f) := (rfl)

/-- On functions of the form `(x, y) ↦ f x * g y`, the measure `prodMk μ ν` agrees with the
algebraic tensor product of `μ` and `ν`. -/
/-
**AbstractMeasure.prodMk_prod_apply** 是 Mathlib 中的一个引理，位于命名空间 `AbstractMeasure`。
形式化陈述：prodMk_prod_apply (f : C(X, R)) (g : C(Y, R)) : prodMk μ ν ((f.comp .fst) 
* (g.comp .snd)) = μ f * ν g
参数：f : C(X, R)；g : C(Y, R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMap.instSMulCommClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] {R : Type u_3} {R₁ : Type u_4} {M : Type u_5} [inst_1 : TopologicalSpace M
]   [inst_2 : SMul R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbstractMeasure.prodMk_apply`：∀ {X : Type u_1} {Y : Type u_2} {R : Type 
u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : CommR
ing R] [inst_3 : T…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `AbstractMeasure.instContinuousLinearMapClassContinuousMap`：∀ {X : Type u
_1} {R : Type u_3} {E : Type u_4} [inst : TopologicalSpace X] [inst_1 : AddCommG
roup E]   [inst_2 : TopologicalSpace E] [inst_3…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AbstractMeasure.contractFst_apply`：∀ {X : Type u_1} {Y : Type u_2} {R : 
Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : 
CommRing R] [inst_3 : T…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
On functions of the form `(x, y) ↦ f x * g y`, the measure `prodMk μ ν` agrees w
ith the
algebraic tensor product of `μ` and `ν`.
-/
lemma prodMk_prod_apply (f : C(X, R)) (g : C(Y, R)) :
    prodMk μ ν ((f.comp .fst) * (g.comp .snd)) = μ f * ν g := by
  simp only [← smul_eq_mul, prodMk_apply, ← map_smul]
  congr 1 with y
  simp_rw [contractFst_apply, ContinuousMap.smul_apply, smul_eq_mul, mul_comm (μ f) (g y),
    ← smul_eq_mul, ← map_smul]
  congr 1 with x
  simp_rw [ContinuousMap.smul_apply, smul_eq_mul, mul_comm (g y) (f x)]
  rfl

/-- "Right-handed" version of the natural product map on measures (acting on functions
as first integrating along `Y`, and then integrating the result along `X`). -/
/-
**AbstractMeasure.prodMk'** 是 Mathlib 中的一个定义，位于命名空间 `AbstractMeasure`。
形式化陈述：prodMk' : D(X, R) ->ₗ[R] D(Y, R) ->ₗ[R] D(X × Y, R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
"Right-handed" version of the natural product map on measures (acting on functio
ns
as first integrating along `Y`, and then integrating the result along `X`).
-/
def prodMk' : D(X, R) →ₗ[R] D(Y, R) →ₗ[R] D(X × Y, R) :=
  ((ContinuousLinearMap.llcomp R _ _ R).comp contractSndCLM).flip

@[simp]
/-
**AbstractMeasure.prodMk'_apply** 是 Mathlib 中的一个定理，位于命名空间 `AbstractMeasure`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {R : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : CommRing R] [inst_3 : TopologicalSpac
e R] [inst_4 : IsTopologicalRing R] (μ : AbstractMeasure X R R)   (ν : AbstractM
easure Y R R) [inst_5 : LocallyCompactSpace X] [inst_6 : LocallyCompactSpace Y] 
(f : C(X × Y, R)),   ((AbstractMeasure.prodMk' μ) ν) f = μ ((AbstractMeasure.con
tractSnd ν) f)
参数：μ : AbstractMeasure X R R；ν : AbstractMeasure Y R R；f : C(X × Y, R)；(Abstract
Measure.prodMk' μ) ν；(AbstractMeasure.contractSnd ν) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
-/
lemma prodMk'_apply (f : C(X × Y, R)) : (μ.prodMk' ν) f = μ (ν.contractSnd f) := (rfl)
/-
**AbstractMeasure.prodMk'_flip** 是 Mathlib 中的一个定理，位于命名空间 `AbstractMeasure`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {R : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : CommRing R] [inst_3 : TopologicalSpac
e R] [inst_4 : IsTopologicalRing R] (μ : AbstractMeasure X R R)   (ν : AbstractM
easure Y R R) [inst_5 : LocallyCompactSpace X] [inst_6 : LocallyCompactSpace Y] 
(f : C(X × Y, R)),   ((AbstractMeasure.prodMk' μ) ν) f = ((AbstractMeasure.prodM
k ν) μ) (f.comp ContinuousMap.prodSwap)
参数：μ : AbstractMeasure X R R；ν : AbstractMeasure Y R R；f : C(X × Y, R)；(Abstract
Measure.prodMk' μ) ν；(AbstractMeasure.prodMk ν) μ；f.comp ContinuousMap.prodSwap。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
-/
lemma prodMk'_flip (f : C(X × Y, R)) :
    (μ.prodMk' ν) f = (ν.prodMk μ) (f.comp ContinuousMap.prodSwap) := (rfl)
/-
**AbstractMeasure.prodMk'_prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `AbstractMeasure`
。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {R : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : CommRing R] [inst_3 : TopologicalSpac
e R] [inst_4 : IsTopologicalRing R] (μ : AbstractMeasure X R R)   (ν : AbstractM
easure Y R R) [inst_5 : LocallyCompactSpace X] [inst_6 : LocallyCompactSpace Y] 
(f : C(X, R))   (g : C(Y, R)), ((AbstractMeasure.prodMk' μ) ν) (f.comp Continuou
sMap.fst * g.comp ContinuousMap.snd) = μ f * ν g
参数：μ : AbstractMeasure X R R；ν : AbstractMeasure Y R R；f : C(X, R)；g : C(Y, R)；(
AbstractMeasure.prodMk' μ) ν；f.comp ContinuousMap.fst * g.comp ContinuousMap.snd
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMap.instSMulCommClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] {R : Type u_3} {R₁ : Type u_4} {M : Type u_5} [inst_1 : TopologicalSpace M
]   [inst_2 : SMul R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbstractMeasure.prodMk'_apply`：∀ {X : Type u_1} {Y : Type u_2} {R : Type
 u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : Comm
Ring R] [inst_3 : T…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `AbstractMeasure.instContinuousLinearMapClassContinuousMap`：∀ {X : Type u
_1} {R : Type u_3} {E : Type u_4} [inst : TopologicalSpace X] [inst_1 : AddCommG
roup E]   [inst_2 : TopologicalSpace E] [inst_3…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AbstractMeasure.contractSnd_apply`：∀ {X : Type u_1} {Y : Type u_2} {R : 
Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : 
CommRing R] [inst_3 : T…
-/
lemma prodMk'_prod_apply (f : C(X, R)) (g : C(Y, R)) :
    prodMk' μ ν ((f.comp .fst) * (g.comp .snd)) = μ f * ν g := by
  simp only [prodMk'_apply, mul_comm (μ f) (ν g), ← smul_eq_mul, ← map_smul]
  congr 1 with x
  simp_rw [ContinuousMap.smul_apply, smul_eq_mul, mul_comm (ν g) (f x), contractSnd_apply,
    ← smul_eq_mul, ← map_smul]
  rfl

end LocallyCompact

section Profinite

variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y] [TotallyDisconnectedSpace X]
  [T0Space R]

/-- For profinite spaces, the two product structures on measures agree. -/
/-
**AbstractMeasure.prodMk_eq_prodMk'** 是 Mathlib 中的一个引理，位于命名空间 `AbstractMeasure`。
形式化陈述：prodMk_eq_prodMk' : prodMk μ ν = prodMk' μ ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `WeaklyLocallyCompactSpace.locallyCompactSpace`：∀ {X : Type u_1} [inst : 
TopologicalSpace X] [R1Space X] [WeaklyLocallyCompactSpace X], LocallyCompactSpa
ce X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `DenseRange.equalizer`：DenseRange.equalizer (hfd : DenseRange f) {g h : β
 -> γ} (hg : Continuous g) (hh : Continuous h) (H : g ∘ f = h ∘ f) : g = h
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用引理 `ContinuousMap.denseRange_tensorHom`：denseRange_tensorHom [CompactSpace X
] [T2Space X] [CompactSpace Y] [TotallyDisconnectedSpace X] : DenseRange (tensor
Hom : C(X, R) otimes[R] …
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `AbstractMeasure.instContinuousLinearMapClassContinuousMap`：∀ {X : Type u
_1} {R : Type u_3} {E : Type u_4} [inst : TopologicalSpace X] [inst_1 : AddCommG
roup E]   [inst_2 : TopologicalSpace E] [inst_3…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.instSMulCommClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] {R : Type u_3} {R₁ : Type u_4} {M : Type u_5} [inst_1 : TopologicalSpace M
]   [inst_2 : SMul R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
For profinite spaces, the two product structures on measures agree.
-/
lemma prodMk_eq_prodMk' : prodMk μ ν = prodMk' μ ν := by
  apply DFunLike.coe_injective
  apply denseRange_tensorHom.equalizer (by fun_prop) (by fun_prop) (funext fun h ↦ ?_)
  induction h with
  | zero => simp
  | add => grind
  | tmul f g => simp [prodMul_def, prodMk_prod_apply μ, prodMk'_prod_apply μ]

end Profinite

end Prod

end ContinuousSMul

end AbstractMeasure

end

