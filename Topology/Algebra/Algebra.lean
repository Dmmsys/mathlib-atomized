/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Algebra.Order.Interval.Set.Instances

/-!
# Topological (sub)algebras

A topological algebra over a topological semiring `R` is a topological semiring with a compatible
continuous scalar multiplication by elements of `R`. We reuse typeclass `ContinuousSMul` for
topological algebras.

## Results

The topological closure of a subalgebra is still a subalgebra, which as an algebra is a
topological algebra.

In this file we define continuous algebra homomorphisms, as algebra homomorphisms between
topological (semi-)rings which are continuous. The type `ContinuousAlgHom R A B` of continuous
algebra homomorphisms between the topological `R`-algebras `A` and `B` is denoted by `A →A[R] B`.

See also `ContinuousAlgEquiv R A B`, denoted by `A ≃A[R] B`, for the type of isomorphisms between
the topological `R`-algebras `A` and `B`.

-/

@[expose] public section

assert_not_exists Module.Basis

open Algebra Set TopologicalSpace Topology

universe u v w

section TopologicalAlgebra

variable (R : Type*) (A : Type u)
variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [TopologicalSpace R] [TopologicalSpace A]

@[continuity, fun_prop]
/-
**continuous_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_algebraMap [ContinuousSMul R A] : Continuous (algebraMap R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one'`：algebraMap_eq_smul_one' : ⇑(algebraMap 
R A) = fun r => r • (1 : A)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem continuous_algebraMap [ContinuousSMul R A] : Continuous (algebraMap R A) := by
  rw [algebraMap_eq_smul_one']
  fun_prop
/-
**continuous_algebraMap_iff_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_algebraMap_iff_smul [ContinuousMul A] : Continuous (algebraMap 
R A) ↔ Continuous fun p : R × A => p.1 • p.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
-/
theorem continuous_algebraMap_iff_smul [ContinuousMul A] :
    Continuous (algebraMap R A) ↔ Continuous fun p : R × A => p.1 • p.2 := by
  refine ⟨fun h => ?_, fun h => have : ContinuousSMul R A := ⟨h⟩; continuous_algebraMap _ _⟩
  simp only [Algebra.smul_def]
  exact (h.comp continuous_fst).mul continuous_snd
/-
**continuousSMul_of_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousSMul_of_algebraMap [ContinuousMul A] (h : Continuous (algebraMap
 R A)) : ContinuousSMul R A
参数：h : Continuous (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_algebraMap_iff_smul`：continuous_algebraMap_iff_smul [Continuo
usMul A] : Continuous (algebraMap R A) ↔ Continuous fun p : R × A => p.1 • p.2
-/
theorem continuousSMul_of_algebraMap [ContinuousMul A] (h : Continuous (algebraMap R A)) :
    ContinuousSMul R A :=
  ⟨(continuous_algebraMap_iff_smul R A).1 h⟩
/-
**Subalgebra.continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subalgebra.continuousSMul (S : Subalgebra R A) (X) [TopologicalSpace X] [M
ulAction A X] [ContinuousSMul A X] : ContinuousSMul S X
参数：S : Subalgebra R A；X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subalgebra.continuousSMul (S : Subalgebra R A) (X) [TopologicalSpace X] [MulAction A X]
    [ContinuousSMul A X] : ContinuousSMul S X :=
  Subsemiring.continuousSMul S.toSubsemiring X
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder A] [IsOrderedRing A] [ContinuousMul A] :
    ContinuousMul (Icc (0 : A) 1) :=
  Topology.IsInducing.subtypeVal.continuousMul Icc.coeMonoidWithZeroHom
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder A] [IsOrderedRing A] [ContinuousMul A] :
    ContinuousMul (Ico (0 : A) 1) :=
  Topology.IsInducing.subtypeVal.continuousMul Ico.coeMulHom
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder A] [IsStrictOrderedRing A] [ContinuousMul A] :
    ContinuousMul (Ioc (0 : A) 1) :=
  Topology.IsInducing.subtypeVal.continuousMul Ioc.coeMonoidHom
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder A] [IsStrictOrderedRing A] [ContinuousMul A] :
    ContinuousMul (Ioo (0 : A) 1) :=
  Topology.IsInducing.subtypeVal.continuousMul Ioo.coeMulHom

section
variable [ContinuousSMul R A]

/-- The inclusion of the base ring in a topological algebra as a continuous linear map. -/
@[simps]
/-
**algebraMapCLM** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：algebraMapCLM : R ->L[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the base ring in a topological algebra as a continuous linear m
ap.
-/
def algebraMapCLM : R →L[R] A :=
  { Algebra.linearMap R A with
    toFun := algebraMap R A }
/-
**coe_algebraMapCLM** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_algebraMapCLM : ⇑(algebraMapCLM R A) = algebraMap R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_algebraMapCLM : ⇑(algebraMapCLM R A) = algebraMap R A :=
  rfl
/-
**toLinearMap_algebraMapCLM** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toLinearMap_algebraMapCLM : (algebraMapCLM R A).toLinearMap = Algebra.line
arMap R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_algebraMapCLM : (algebraMapCLM R A).toLinearMap = Algebra.linearMap R A :=
  rfl
/-
**ContinuousLinearMap.toSpanSingleton_one_eq_algebraMapCLM** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：ContinuousLinearMap.toSpanSingleton_one_eq_algebraMapCLM : toSpanSingleton
 R (M₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext_ring`：ext_ring [TopologicalSpace R₁] {f g : R₁ -
>L[R₁] M₁} (h : f 1 = g 1) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `algebraMapCLM_apply`：∀ (R : Type u_1) (A : Type u) [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : TopologicalSpace R] 
[inst_4 :…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ContinuousLinearMap.toSpanSingleton_one_eq_algebraMapCLM :
    toSpanSingleton R (M₁ := A) 1 = algebraMapCLM R A := by
  ext; simp

end

/-- If `R` is a discrete topological ring, then any topological ring `S` which is an `R`-algebra
is also a topological `R`-algebra.

NB: This could be an instance but the signature makes it very expensive in search.
See https://github.com/leanprover-community/mathlib4/pull/15339
for the regressions caused by making this an instance. -/
/-
**DiscreteTopology.instContinuousSMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DiscreteTopology.instContinuousSMul [IsTopologicalSemiring A] [DiscreteTop
ology R] : ContinuousSMul R A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousSMul_of_algebraMap`：continuousSMul_of_algebraMap [ContinuousMu
l A] (h : Continuous (algebraMap R A)) : ContinuousSMul R A
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f

--- 原说明 ---
If `R` is a discrete topological ring, then any topological ring `S` which is an
 `R`-algebra
is also a topological `R`-algebra.

NB: This could be an instance but the signature makes it very expensive in searc
h.
See https://github.com/leanprover-community/mathlib4/pull/15339
for the regressions caused by making this an instance.
-/
theorem DiscreteTopology.instContinuousSMul [IsTopologicalSemiring A] [DiscreteTopology R] :
    ContinuousSMul R A := continuousSMul_of_algebraMap _ _ continuous_of_discreteTopology

end TopologicalAlgebra

section TopologicalAlgebra

section

variable (R : Type*) [CommSemiring R]
  (A : Type*) [Semiring A]

/-- Continuous algebra homomorphisms between algebras. We only put the type classes that are
necessary for the definition, although in applications `M` and `B` will be topological algebras
over the topological ring `R`. -/
/-
**ContinuousAlgHom** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：ContinuousAlgHom (R : Type*) [CommSemiring R] (A : Type*) [Semiring A] [To
pologicalSpace A] (B : Type*) [Semiring B] [TopologicalSpace B] [Algebra R A] [A
lgebra R B] extends A ->ₐ[R] B where cont : Continuous toFun
参数：R : Type*；A : Type*；B : Type*。
继承自：A ->ₐ[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous algebra homomorphisms between algebras. We only put the type classes 
that are
necessary for the definition, although in applications `M` and `B` will be topol
ogical algebras
over the topological ring `R`.
-/
structure ContinuousAlgHom (R : Type*) [CommSemiring R] (A : Type*) [Semiring A]
    [TopologicalSpace A] (B : Type*) [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
    extends A →ₐ[R] B where
  cont : Continuous toFun := by fun_prop

@[inherit_doc]
notation:25 A " →A[" R "] " B => ContinuousAlgHom R A B

namespace ContinuousAlgHom

open Subalgebra

section Semiring

variable {R} {A}
variable [TopologicalSpace A]

variable {B : Type*} [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]

/-
**ContinuousAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (A →A[R] B) A B where
  coe f := f.toAlgHom
  coe_injective f g h := by
    cases f; cases g
    simp only [mk.injEq]
    exact AlgHom.ext (congrFun h)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**ContinuousAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AlgHomClass (A →A[R] B) R A B where
  map_mul f x y := map_mul f.toAlgHom x y
  map_one f     := map_one f.toAlgHom
  map_add f     := map_add f.toAlgHom
  map_zero f    := map_zero f.toAlgHom
  commutes f r  := f.toAlgHom.commutes r

attribute [coe] ContinuousAlgHom.toAlgHom
/-
**ContinuousAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (A →A[R] B) (A →ₐ[R] B) where coe := toAlgHom

@[deprecated "Now a syntactic equality" (since := "2026-04-29"), nolint synTaut]
/-
**ContinuousAlgHom.toAlgHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：toAlgHom_eq_coe (f : A ->A[R] B) : f.toAlgHom = f
参数：f : A ->A[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlgHom_eq_coe (f : A →A[R] B) : f.toAlgHom = f := rfl

@[simp, norm_cast]
/-
**ContinuousAlgHom.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_inj {f g : A ->A[R] B} : (f : A ->ₐ[R] B) = g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAlgHom.mk.injEq`：∀ {R : Type u_3} [inst : CommSemiring R] {A :
 Type u_4} [inst_1 : Semiring A] [inst_2 : TopologicalSpace A]   {B : Type u_5} 
[inst_3 : Semir…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coe_inj {f g : A →A[R] B} : (f : A →ₐ[R] B) = g ↔ f = g := by
  cases f; cases g; simp only [mk.injEq]
/-
**ContinuousAlgHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_mk (f : A ->ₐ[R] B) (h) : (mk f h : A ->ₐ[R] B) = f
参数：f : A ->ₐ[R] B；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : A →ₐ[R] B) (h) : (mk f h : A →ₐ[R] B) = f := rfl

@[simp]
/-
**ContinuousAlgHom.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_mk' (f : A ->ₐ[R] B) (h) : (mk f h : A -> B) = f
参数：f : A ->ₐ[R] B；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk' (f : A →ₐ[R] B) (h) : (mk f h : A → B) = f := rfl

@[simp, norm_cast]
/-
**ContinuousAlgHom.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_coe (f : A ->A[R] B) : ⇑(f : A ->ₐ[R] B) = f
参数：f : A ->A[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe (f : A →A[R] B) : ⇑(f : A →ₐ[R] B) = f := rfl
/-
**ContinuousAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousMapClass (A →A[R] B) A B where
  map_continuous f := f.2

@[fun_prop]
/-
**ContinuousAlgHom.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {A : Type u_2} [inst_1 : Semiring
 A] [inst_2 : TopologicalSpace A]   {B : Type u_3} [inst_3 : Semiring B] [inst_4
 : TopologicalSpace B] [inst_5 : Algebra R A] [inst_6 : Algebra R B]   (f : A →A
[R] B), Continuous ⇑f
参数：f : A →A[R] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgHom.cont`：∀ {R : Type u_3} [inst : CommSemiring R] {A : Typ
e u_4} [inst_1 : Semiring A] [inst_2 : TopologicalSpace A]   {B : Type u_5} [ins
t_3 : Semir…
-/
protected theorem continuous (f : A →A[R] B) : Continuous f := f.2
/-
**ContinuousAlgHom.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom
`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {E₁ : Type u_4} {E₂ : Type u_5} [
inst_1 : UniformSpace E₁]   [inst_2 : UniformSpace E₂] [inst_3 : Ring E₁] [inst_
4 : Ring E₂] [inst_5 : Algebra R E₁] [inst_6 : Algebra R E₂]   [IsUniformAddGrou
p E₁] [IsUniformAddGroup E₂] (f : E₁ →A[R] E₂), UniformContinuous ⇑f
参数：f : E₁ →A[R] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_addMonoidHom_of_continuous`：∀ {α : Type u_1} {β : Type
 u_2} [inst : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {hom :
 Type u_3}   [inst_3 : UniformSpac…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `ContinuousAlgHom.instAlgHomClass`：∀ {R : Type u_1} [inst : CommSemiring 
R] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : TopologicalSpace A]   {B : Typ
e u_3} [inst_3 : Semir…
· 使用定理 `ContinuousAlgHom.continuous`：∀ {R : Type u_1} [inst : CommSemiring R] {A
 : Type u_2} [inst_1 : Semiring A] [inst_2 : TopologicalSpace A]   {B : Type u_3
} [inst_3 : Semir…
-/
protected theorem uniformContinuous {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [Ring E₁] [Ring E₂] [Algebra R E₁] [Algebra R E₂] [IsUniformAddGroup E₁]
    [IsUniformAddGroup E₂] (f : E₁ →A[R] E₂) : UniformContinuous f :=
  uniformContinuous_addMonoidHom_of_continuous f.continuous

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
/-
**ContinuousAlgHom.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgHom.Simps
`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     {A : Type u_2} →       [i
nst_1 : Semiring A] →         [inst_2 : TopologicalSpace A] →           {B : Typ
e u_3} →             [inst_3 : Semiring B] →               [inst_4 : Topological
Space B] → [inst_5 : Algebra R A] → [inst_6 : Algebra R B] → (A →A[R] B) → A → B
参数：A →A[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
because it is a composition of multiple projections.
-/
def Simps.apply (h : A →A[R] B) : A → B := h

/-- See Note [custom simps projection]. -/
/-
**ContinuousAlgHom.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgHom.Simps`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     {A : Type u_2} →       [i
nst_1 : Semiring A] →         [inst_2 : TopologicalSpace A] →           {B : Typ
e u_3} →             [inst_3 : Semiring B] →               [inst_4 : Topological
Space B] → [inst_5 : Algebra R A] → [inst_6 : Algebra R B] → (A →A[R] B) → A →ₐ[
R] B
参数：A →A[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.coe (h : A →A[R] B) : A →ₐ[R] B := h

initialize_simps_projections ContinuousAlgHom (toFun → apply, toAlgHom → coe)

@[ext]
/-
**ContinuousAlgHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：ext {f g : A ->A[R] B} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : A →A[R] B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/-- Copy of a `ContinuousAlgHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
/-
**ContinuousAlgHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgHom`。
形式化陈述：copy (f : A ->A[R] B) (f' : A -> B) (h : f' = ⇑f) : A ->A[R] B where toAlg
Hom
参数：f : A ->A[R] B；f' : A -> B；h : f' = ⇑f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `ContinuousAlgHom` with a new `toFun` equal to the old one. Useful to 
fix
definitional equalities.
-/
def copy (f : A →A[R] B) (f' : A → B) (h : f' = ⇑f) : A →A[R] B where
  toAlgHom := {
    toRingHom := (f : A →A[R] B).toRingHom.copy f' h
    commutes' := fun r => by
      simp only [AlgHom.toRingHom_eq_coe, h, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_copy, AlgHomClass.commutes f r] }
  cont := show Continuous f' from h.symm ▸ f.continuous

@[simp]
/-
**ContinuousAlgHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_copy (f : A ->A[R] B) (f' : A -> B) (h : f' = ⇑f) : ⇑(f.copy f' h) = f
'
参数：f : A ->A[R] B；f' : A -> B；h : f' = ⇑f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : A →A[R] B) (f' : A → B) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' := rfl
/-
**ContinuousAlgHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：copy_eq (f : A ->A[R] B) (f' : A -> B) (h : f' = ⇑f) : f.copy f' h = f
参数：f : A ->A[R] B；f' : A -> B；h : f' = ⇑f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : A →A[R] B) (f' : A → B) (h : f' = ⇑f) : f.copy f' h = f := DFunLike.ext' h
/-
**ContinuousAlgHom.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {A : Type u_2} [inst_1 : Semiring
 A] [inst_2 : TopologicalSpace A]   {B : Type u_3} [inst_3 : Semiring B] [inst_4
 : TopologicalSpace B] [inst_5 : Algebra R A] [inst_6 : Algebra R B]   (f : A →A
[R] B), f 0 = 0
参数：f : A →A[R] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `ContinuousAlgHom.instAlgHomClass`：∀ {R : Type u_1} [inst : CommSemiring 
R] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : TopologicalSpace A]   {B : Typ
e u_3} [inst_3 : Semir…
-/
protected theorem map_zero (f : A →A[R] B) : f (0 : A) = 0 := map_zero f
/-
**ContinuousAlgHom.map_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {A : Type u_2} [inst_1 : Semiring
 A] [inst_2 : TopologicalSpace A]   {B : Type u_3} [inst_3 : Semiring B] [inst_4
 : TopologicalSpace B] [inst_5 : Algebra R A] [inst_6 : Algebra R B]   (f : A →A
[R] B) (x y : A), f (x + y) = f x + f y
参数：f : A →A[R] B；x y : A；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `ContinuousAlgHom.instAlgHomClass`：∀ {R : Type u_1} [inst : CommSemiring 
R] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : TopologicalSpace A]   {B : Typ
e u_3} [inst_3 : Semir…
-/
protected theorem map_add (f : A →A[R] B) (x y : A) : f (x + y) = f x + f y := map_add f x y
/-
**ContinuousAlgHom.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {A : Type u_2} [inst_1 : Semiring
 A] [inst_2 : TopologicalSpace A]   {B : Type u_3} [inst_3 : Semiring B] [inst_4
 : TopologicalSpace B] [inst_5 : Algebra R A] [inst_6 : Algebra R B]   (f : A →A
[R] B) (c : R) (x : A), f (c • x) = c • f x
参数：f : A →A[R] B；c : R；x : A；c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `ContinuousAlgHom.instAlgHomClass`：∀ {R : Type u_1} [inst : CommSemiring 
R] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : TopologicalSpace A]   {B : Typ
e u_3} [inst_3 : Semir…
-/
protected theorem map_smul (f : A →A[R] B) (c : R) (x : A) :
    f (c • x) = c • f x :=
  map_smul ..
/-
**ContinuousAlgHom.map_smul_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom
`。
形式化陈述：map_smul_of_tower {R S : Type*} [CommSemiring S] [SMul R A] [Algebra S A] 
[SMul R B] [Algebra S B] [MulActionHomClass (A ->A[S] B) R A B] (f : A ->A[S] B)
 (c : R) (x : A) : f (c • x) = c • f x
参数：A ->A[S] B；f : A ->A[S] B；c : R；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
-/
theorem map_smul_of_tower {R S : Type*} [CommSemiring S] [SMul R A] [Algebra S A] [SMul R B]
    [Algebra S B] [MulActionHomClass (A →A[S] B) R A B] (f : A →A[S] B) (c : R) (x : A) :
    f (c • x) = c • f x :=
  map_smul f c x
/-
**ContinuousAlgHom.map_sum** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {A : Type u_2} [inst_1 : Semiring
 A] [inst_2 : TopologicalSpace A]   {B : Type u_3} [inst_3 : Semiring B] [inst_4
 : TopologicalSpace B] [inst_5 : Algebra R A] [inst_6 : Algebra R B]   {ι : Type
 u_4} (f : A →A[R] B) (s : Finset ι) (g : ι → A), f (∑ i ∈ s, g i) = ∑ i ∈ s, f 
(g i)
参数：f : A →A[R] B；s : Finset ι；g : ι → A；∑ i ∈ s, g i；g i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `ContinuousAlgHom.instAlgHomClass`：∀ {R : Type u_1} [inst : CommSemiring 
R] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : TopologicalSpace A]   {B : Typ
e u_3} [inst_3 : Semir…
-/
protected theorem map_sum {ι : Type*} (f : A →A[R] B) (s : Finset ι) (g : ι → A) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) :=
  map_sum ..

/-- Any two continuous `R`-algebra morphisms from `R` are equal -/
@[ext (iff := false)]
/-
**ContinuousAlgHom.ext_ring** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：ext_ring [TopologicalSpace R] {f g : R ->A[R] A} : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousAlgHom.coe_inj`：coe_inj {f g : A ->A[R] B} : (f : A ->ₐ[R] B) 
= g ↔ f = g
· 使用定理 `Algebra.ext_id`：ext_id (f g : R ->ₐ[R] A) : f = g

--- 原说明 ---
Any two continuous `R`-algebra morphisms from `R` are equal
-/
theorem ext_ring [TopologicalSpace R] {f g : R →A[R] A} : f = g :=
  coe_inj.mp (ext_id _ _ _)
/-
**ContinuousAlgHom.ext_ring_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：ext_ring_iff [TopologicalSpace R] {f g : R ->A[R] A} : f = g ↔ f 1 = g 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgHom.ext_ring`：ext_ring [TopologicalSpace R] {f g : R ->A[R]
 A} : f = g
-/
theorem ext_ring_iff [TopologicalSpace R] {f g : R →A[R] A} : f = g ↔ f 1 = g 1 :=
  ⟨fun h => h ▸ rfl, fun _ => ext_ring ⟩

/-- If two continuous algebra maps are equal on a set `s`, then they are equal on the closure
of the `Algebra.adjoin` of this set. -/
/-
**ContinuousAlgHom.eqOn_closure_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgH
om`。
形式化陈述：eqOn_closure_adjoin [T2Space B] {s : Set A} {f g : A ->A[R] B} (h : Set.Eq
On f g s) : Set.EqOn f g (closure (Algebra.adjoin R s : Set A))
参数：h : Set.EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace Y] [T2Space X] {s : Set Y}   {f g : Y → X}, Set
.EqOn …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgHom.eqOn_adjoin_iff`：eqOn_adjoin_iff {φ ψ : A ->ₐ[R] B} {s : Set A} :
 Set.EqOn φ ψ (adjoin R s) ↔ Set.EqOn φ ψ s
· 使用定理 `ContinuousAlgHom.continuous`：∀ {R : Type u_1} [inst : CommSemiring R] {A
 : Type u_2} [inst_1 : Semiring A] [inst_2 : TopologicalSpace A]   {B : Type u_3
} [inst_3 : Semir…

--- 原说明 ---
If two continuous algebra maps are equal on a set `s`, then they are equal on th
e closure
of the `Algebra.adjoin` of this set.
-/
theorem eqOn_closure_adjoin [T2Space B] {s : Set A} {f g : A →A[R] B} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure (Algebra.adjoin R s : Set A)) :=
  Set.EqOn.closure (AlgHom.eqOn_adjoin_iff.mpr h) f.continuous g.continuous

/-- If the subalgebra generated by a set `s` is dense in the ambient module, then two continuous
algebra maps equal on `s` are equal. -/
/-
**ContinuousAlgHom.ext_on** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：ext_on [T2Space B] {s : Set A} (hs : Dense (Algebra.adjoin R s : Set A)) {
f g : A ->A[R] B} (h : Set.EqOn f g s) : f = g
参数：hs : Dense (Algebra.adjoin R s : Set A)；h : Set.EqOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgHom.ext`：ext {f g : A ->A[R] B} (h : forall x, f x = g x) :
 f = g
· 使用定理 `ContinuousAlgHom.eqOn_closure_adjoin`：eqOn_closure_adjoin [T2Space B] {s
 : Set A} {f g : A ->A[R] B} (h : Set.EqOn f g s) : Set.EqOn f g (closure (Algeb
ra.adjoin R s : Set A))

--- 原说明 ---
If the subalgebra generated by a set `s` is dense in the ambient module, then tw
o continuous
algebra maps equal on `s` are equal.
-/
theorem ext_on [T2Space B] {s : Set A} (hs : Dense (Algebra.adjoin R s : Set A))
    {f g : A →A[R] B} (h : Set.EqOn f g s) : f = g :=
  ext fun x => eqOn_closure_adjoin h (hs x)

/-- Interpret a `ContinuousAlgHom` as a `ContinuousLinearMap`. -/
/-
**ContinuousAlgHom.toContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAl
gHom`。
形式化陈述：toContinuousLinearMap (e : A ->A[R] B) : A ->L[R] B where toLinearMap
参数：e : A ->A[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a `ContinuousAlgHom` as a `ContinuousLinearMap`.
-/
def toContinuousLinearMap (e : A →A[R] B) : A →L[R] B where
  toLinearMap := e.toAlgHom.toLinearMap
/-
**ContinuousAlgHom.coe_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usAlgHom`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {A : Type u_2} [inst_1 : Semiring
 A] [inst_2 : TopologicalSpace A]   {B : Type u_3} [inst_3 : Semiring B] [inst_4
 : TopologicalSpace B] [inst_5 : Algebra R A] [inst_6 : Algebra R B]   (e : A →A
[R] B), ⇑e.toContinuousLinearMap = ⇑e
参数：e : A →A[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_toContinuousLinearMap (e : A →A[R] B) : ⇑e.toContinuousLinearMap = e := rfl

variable [IsSemitopologicalSemiring A]

/-- The topological closure of a subalgebra -/
/-
**ContinuousAlgHom._root_.Subalgebra.topologicalClosure** 是 Mathlib 中的一个定义，位于命名空
间 `ContinuousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topological closure of a subalgebra
-/
def _root_.Subalgebra.topologicalClosure (s : Subalgebra R A) : Subalgebra R A where
  toSubsemiring := s.toSubsemiring.topologicalClosure
  algebraMap_mem' r := by
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subsemiring.topologicalClosure_coe,
      Subalgebra.coe_toSubsemiring]
    apply subset_closure
    exact algebraMap_mem s r

/-- Under a continuous algebra map, the image of the `TopologicalClosure` of a subalgebra is
contained in the `TopologicalClosure` of its image. -/
/-
**ContinuousAlgHom._root_.Subalgebra.map_topologicalClosure_le** 是 Mathlib 中的一个定
理，位于命名空间 `ContinuousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Under a continuous algebra map, the image of the `TopologicalClosure` of a subal
gebra is
contained in the `TopologicalClosure` of its image.
-/
theorem _root_.Subalgebra.map_topologicalClosure_le
    [IsSemitopologicalSemiring B] (f : A →A[R] B) (s : Subalgebra R A) :
    map f s.topologicalClosure ≤ (map f.toAlgHom s).topologicalClosure :=
  image_closure_subset_closure_image f.continuous
/-
**ContinuousAlgHom._root_.Subalgebra.topologicalClosure_map_le** 是 Mathlib 中的一个引
理，位于命名空间 `ContinuousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Subalgebra.topologicalClosure_map_le [IsSemitopologicalSemiring B]
    (f : A →ₐ[R] B) (hf : IsClosedMap f) (s : Subalgebra R A) :
    (map f s).topologicalClosure ≤ map f s.topologicalClosure :=
  hf.closure_image_subset _
/-
**ContinuousAlgHom._root_.Subalgebra.topologicalClosure_map** 是 Mathlib 中的一个引理，位
于命名空间 `ContinuousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Subalgebra.topologicalClosure_map [IsSemitopologicalSemiring B]
    (f : A →A[R] B) (hf : IsClosedMap f) (s : Subalgebra R A) :
    (map f.toAlgHom s).topologicalClosure = map f.toAlgHom s.topologicalClosure :=
  SetLike.coe_injective <| hf.closure_image_eq_of_continuous f.continuous _

@[simp]
/-
**ContinuousAlgHom._root_.Subalgebra.topologicalClosure_coe** 是 Mathlib 中的一个定理，位
于命名空间 `ContinuousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subalgebra.topologicalClosure_coe (s : Subalgebra R A) :
    (s.topologicalClosure : Set A) = closure ↑s := rfl

/-- Under a dense continuous algebra map, a subalgebra
whose `TopologicalClosure` is `⊤` is sent to another such submodule.
That is, the image of a dense subalgebra under a map with dense range is dense.
-/
/-
**ContinuousAlgHom._root_.DenseRange.topologicalClosure_map_subalgebra** 是 Mathl
ib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Under a dense continuous algebra map, a subalgebra
whose `TopologicalClosure` is `⊤` is sent to another such submodule.
That is, the image of a dense subalgebra under a map with dense range is dense.
-/
theorem _root_.DenseRange.topologicalClosure_map_subalgebra
    [IsSemitopologicalSemiring B] {f : A →A[R] B} (hf' : DenseRange f) {s : Subalgebra R A}
    (hs : s.topologicalClosure = ⊤) : (s.map (f : A →ₐ[R] B)).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Subalgebra.topologicalClosure_coe, coe_top, ← dense_iff_closure_eq,
    Subalgebra.coe_map] at hs ⊢
  exact hf'.dense_image f.continuous hs

end Semiring

section id

variable [TopologicalSpace A]
variable [Algebra R A]

/-- The identity map as a continuous algebra homomorphism. -/
/-
**ContinuousAlgHom.id** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgHom`。
形式化陈述：(R : Type u_1) →   [inst : CommSemiring R] →     (A : Type u_2) → [inst_1 
: Semiring A] → [inst_2 : TopologicalSpace A] → [inst_3 : Algebra R A] → A →A[R]
 A
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
The identity map as a continuous algebra homomorphism.
-/
protected def id : A →A[R] A := ⟨AlgHom.id R A, continuous_id⟩
/-
**ContinuousAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (A →A[R] A) := ⟨ContinuousAlgHom.id R A⟩
/-
**ContinuousAlgHom.one_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：one_def : (1 : A ->A[R] A) = ContinuousAlgHom.id R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : A →A[R] A) = ContinuousAlgHom.id R A := rfl
/-
**ContinuousAlgHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：id_apply (x : A) : ContinuousAlgHom.id R A x = x
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (x : A) : ContinuousAlgHom.id R A x = x := rfl

@[simp, norm_cast]
/-
**ContinuousAlgHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_id : ((ContinuousAlgHom.id R A) : A ->ₐ[R] A) = AlgHom.id R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ((ContinuousAlgHom.id R A) : A →ₐ[R] A) = AlgHom.id R A := rfl

@[simp, norm_cast]
/-
**ContinuousAlgHom.coe_id'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_id' : ⇑(ContinuousAlgHom.id R A) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id' : ⇑(ContinuousAlgHom.id R A) = _root_.id := rfl

@[simp, norm_cast]
/-
**ContinuousAlgHom.coe_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_eq_id {f : A ->A[R] A} : (f : A ->ₐ[R] A) = AlgHom.id R A ↔ f = Contin
uousAlgHom.id R A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousAlgHom.coe_id`：coe_id : ((ContinuousAlgHom.id R A) : A ->ₐ[R] 
A) = AlgHom.id R A
· 使用定理 `ContinuousAlgHom.coe_inj`：coe_inj {f g : A ->A[R] B} : (f : A ->ₐ[R] B) 
= g ↔ f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_eq_id {f : A →A[R] A} :
    (f : A →ₐ[R] A) = AlgHom.id R A ↔ f = ContinuousAlgHom.id R A := by
  rw [← coe_id, coe_inj]

@[simp]
/-
**ContinuousAlgHom.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：one_apply (x : A) : (1 : A ->A[R] A) x = x
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (x : A) : (1 : A →A[R] A) x = x := rfl

end id

section comp

variable {R} {A}
variable [TopologicalSpace A]
variable {B : Type*} [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
  {C : Type*} [Semiring C] [Algebra R C] [TopologicalSpace C]

/-- Composition of continuous algebra homomorphisms. -/
/-
**ContinuousAlgHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgHom`。
形式化陈述：comp (g : B ->A[R] C) (f : A ->A[R] B) : A ->A[R] C
参数：g : B ->A[R] C；f : A ->A[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of continuous algebra homomorphisms.
-/
def comp (g : B →A[R] C) (f : A →A[R] B) : A →A[R] C :=
  ⟨(g : B →ₐ[R] C).comp (f : A →ₐ[R] B), g.2.comp f.2⟩

@[simp, norm_cast]
/-
**ContinuousAlgHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_comp (h : B ->A[R] C) (f : A ->A[R] B) : (h.comp f : A ->ₐ[R] C) = (h 
: B ->ₐ[R] C).comp (f : A ->ₐ[R] B)
参数：h : B ->A[R] C；f : A ->A[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (h : B →A[R] C) (f : A →A[R] B) :
    (h.comp f : A →ₐ[R] C) = (h : B →ₐ[R] C).comp (f : A →ₐ[R] B) := rfl

@[simp, norm_cast]
/-
**ContinuousAlgHom.coe_comp'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_comp' (h : B ->A[R] C) (f : A ->A[R] B) : ⇑(h.comp f) = h ∘ f
参数：h : B ->A[R] C；f : A ->A[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp' (h : B →A[R] C) (f : A →A[R] B) : ⇑(h.comp f) = h ∘ f := rfl
/-
**ContinuousAlgHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：comp_apply (g : B ->A[R] C) (f : A ->A[R] B) (x : A) : (g.comp f) x = g (f
 x)
参数：g : B ->A[R] C；f : A ->A[R] B；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (g : B →A[R] C) (f : A →A[R] B) (x : A) : (g.comp f) x = g (f x) := rfl

@[simp]
/-
**ContinuousAlgHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：comp_id (f : A ->A[R] B) : f.comp (ContinuousAlgHom.id R A) = f
参数：f : A ->A[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgHom.ext`：ext {f g : A ->A[R] B} (h : forall x, f x = g x) :
 f = g
-/
theorem comp_id (f : A →A[R] B) : f.comp (ContinuousAlgHom.id R A) = f :=
  ext fun _x => rfl

@[simp]
/-
**ContinuousAlgHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：id_comp (f : A ->A[R] B) : (ContinuousAlgHom.id R B).comp f = f
参数：f : A ->A[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgHom.ext`：ext {f g : A ->A[R] B} (h : forall x, f x = g x) :
 f = g
-/
theorem id_comp (f : A →A[R] B) : (ContinuousAlgHom.id R B).comp f = f :=
  ext fun _x => rfl
/-
**ContinuousAlgHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：comp_assoc {D : Type*} [Semiring D] [Algebra R D] [TopologicalSpace D] (h 
: C ->A[R] D) (g : B ->A[R] C) (f : A ->A[R] B) : (h.comp g).comp f = h.comp (g.
comp f)
参数：h : C ->A[R] D；g : B ->A[R] C；f : A ->A[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc {D : Type*} [Semiring D] [Algebra R D] [TopologicalSpace D] (h : C →A[R] D)
    (g : B →A[R] C) (f : A →A[R] B) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
/-
**ContinuousAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (A →A[R] A) := ⟨comp⟩
/-
**ContinuousAlgHom.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：mul_def (f g : A ->A[R] A) : f * g = f.comp g
参数：f g : A ->A[R] A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (f g : A →A[R] A) : f * g = f.comp g := rfl

@[simp]
/-
**ContinuousAlgHom.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_mul (f g : A ->A[R] A) : ⇑(f * g) = f ∘ g
参数：f g : A ->A[R] A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (f g : A →A[R] A) : ⇑(f * g) = f ∘ g := rfl
/-
**ContinuousAlgHom.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：mul_apply (f g : A ->A[R] A) (x : A) : (f * g) x = f (g x)
参数：f g : A ->A[R] A；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (f g : A →A[R] A) (x : A) : (f * g) x = f (g x) := rfl
/-
**ContinuousAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (A →A[R] A) where
  mul_one _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  mul_assoc _ _ _ := ext fun _ => rfl
/-
**ContinuousAlgHom.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_pow (f : A ->A[R] A) (n : Nat) : ⇑(f ^ n) = f^[n]
参数：f : A ->A[R] A；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hom_coe_pow`：∀ {M : Type u_4} {F : Type u_5} [inst : Monoid F] (c : F → 
M → M),   c 1 = id → (∀ (f g : F), c (f * g) = c f ∘ c g) → ∀ (f : F) (n : ℕ), c
 …
-/
theorem coe_pow (f : A →A[R] A) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- coercion from `ContinuousAlgHom` to `AlgHom` as a `RingHom`. -/
@[simps]
/-
**ContinuousAlgHom.toAlgHomMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgHom
`。
形式化陈述：toAlgHomMonoidHom : (A ->A[R] A) ->* A ->ₐ[R] A where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
coercion from `ContinuousAlgHom` to `AlgHom` as a `RingHom`.
-/
def toAlgHomMonoidHom : (A →A[R] A) →* A →ₐ[R] A where
  toFun        := (↑)
  map_one'     := rfl
  map_mul' _ _ := rfl

end comp

section prod

variable {R} {A}
variable [TopologicalSpace A]
variable {B : Type*} [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
  {C : Type*} [Semiring C] [Algebra R C] [TopologicalSpace C]

/-- The Cartesian product of two continuous algebra morphisms as a continuous algebra morphism. -/
/-
**ContinuousAlgHom.prod** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgHom`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     {A : Type u_2} →       [i
nst_1 : Semiring A] →         [inst_2 : TopologicalSpace A] →           {B : Typ
e u_3} →             [inst_3 : Semiring B] →               [inst_4 : Topological
Space B] →                 [inst_5 : Algebra R A] →                   [inst_6 : 
Algebra R B] →                     {C : Type u_4} →                       [inst_
7 : Semiring C] →                         [inst_8 : Algebra R C] →              
             [inst_9 : TopologicalSpace C] → (A →A[R] B) → (A →A[R] C) → A →A[R]
 B × C
参数：A →A[R] B；A →A[R] C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartesian product of two continuous algebra morphisms as a continuous algebr
a morphism.
-/
protected def prod (f₁ : A →A[R] B) (f₂ : A →A[R] C) :
    A →A[R] B × C :=
  ⟨(f₁ : A →ₐ[R] B).prod f₂, f₁.2.prodMk f₂.2⟩

@[simp, norm_cast]
/-
**ContinuousAlgHom.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_prod (f₁ : A ->A[R] B) (f₂ : A ->A[R] C) : (f₁.prod f₂ : A ->ₐ[R] B × 
C) = AlgHom.prod f₁ f₂
参数：f₁ : A ->A[R] B；f₂ : A ->A[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (f₁ : A →A[R] B) (f₂ : A →A[R] C) :
    (f₁.prod f₂ : A →ₐ[R] B × C) = AlgHom.prod f₁ f₂ :=
  rfl

@[simp, norm_cast]
/-
**ContinuousAlgHom.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：prod_apply (f₁ : A ->A[R] B) (f₂ : A ->A[R] C) (x : A) : f₁.prod f₂ x = (f
₁ x, f₂ x)
参数：f₁ : A ->A[R] B；f₂ : A ->A[R] C；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_apply (f₁ : A →A[R] B) (f₂ : A →A[R] C) (x : A) :
    f₁.prod f₂ x = (f₁ x, f₂ x) :=
  rfl
/-
**ContinuousAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [UniformSpace D] [CompleteSpace D]
    [Semiring D] [Algebra R D] [T2Space B]
    (f g : D →A[R] B) : CompleteSpace (AlgHom.equalizer f.toAlgHom g.toAlgHom) :=
  isClosed_eq (map_continuous f) (map_continuous g) |>.completeSpace_coe

variable (R A B)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- `Prod.fst` as a `ContinuousAlgHom`. -/
/-
**ContinuousAlgHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgHom`。
形式化陈述：fst : A × B ->A[R] A where cont
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)

--- 原说明 ---
`Prod.fst` as a `ContinuousAlgHom`.
-/
def fst : A × B →A[R] A where
  cont     := continuous_fst
  toAlgHom := AlgHom.fst R A B

/-- `Prod.snd` as a `ContinuousAlgHom`. -/
/-
**ContinuousAlgHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgHom`。
形式化陈述：snd : A × B ->A[R] B where cont
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
`Prod.snd` as a `ContinuousAlgHom`.
-/
def snd : A × B →A[R] B where
  cont := continuous_snd
  toAlgHom := AlgHom.snd R A B

variable {R A B}

@[simp, norm_cast]
/-
**ContinuousAlgHom.coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_fst : ↑(fst R A B) = AlgHom.fst R A B
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fst : ↑(fst R A B) = AlgHom.fst R A B :=
  rfl

@[simp, norm_cast]
/-
**ContinuousAlgHom.coe_fst'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_fst' : ⇑(fst R A B) = Prod.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fst' : ⇑(fst R A B) = Prod.fst :=
  rfl

@[simp, norm_cast]
/-
**ContinuousAlgHom.coe_snd** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_snd : ↑(snd R A B) = AlgHom.snd R A B
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_snd : ↑(snd R A B) = AlgHom.snd R A B :=
  rfl

@[simp, norm_cast]
/-
**ContinuousAlgHom.coe_snd'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_snd' : ⇑(snd R A B) = Prod.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_snd' : ⇑(snd R A B) = Prod.snd :=
  rfl

@[simp]
/-
**ContinuousAlgHom.fst_prod_snd** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：fst_prod_snd : (fst R A B).prod (snd R A B) = ContinuousAlgHom.id R (A × B
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgHom.ext`：ext {f g : A ->A[R] B} (h : forall x, f x = g x) :
 f = g
-/
theorem fst_prod_snd : (fst R A B).prod (snd R A B) = ContinuousAlgHom.id R (A × B) :=
  ext fun ⟨_x, _y⟩ => rfl

@[simp]
/-
**ContinuousAlgHom.fst_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：fst_comp_prod (f : A ->A[R] B) (g : A ->A[R] C) : (fst R B C).comp (f.prod
 g) = f
参数：f : A ->A[R] B；g : A ->A[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgHom.ext`：ext {f g : A ->A[R] B} (h : forall x, f x = g x) :
 f = g
-/
theorem fst_comp_prod (f : A →A[R] B) (g : A →A[R] C) :
    (fst R B C).comp (f.prod g) = f :=
  ext fun _x => rfl

@[simp]
/-
**ContinuousAlgHom.snd_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：snd_comp_prod (f : A ->A[R] B) (g : A ->A[R] C) : (snd R B C).comp (f.prod
 g) = g
参数：f : A ->A[R] B；g : A ->A[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgHom.ext`：ext {f g : A ->A[R] B} (h : forall x, f x = g x) :
 f = g
-/
theorem snd_comp_prod (f : A →A[R] B) (g : A →A[R] C) :
    (snd R B C).comp (f.prod g) = g :=
  ext fun _x => rfl

/-- `Prod.map` of two continuous algebra homomorphisms. -/
/-
**ContinuousAlgHom.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgHom`。
形式化陈述：prodMap {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : 
A ->A[R] B) (f₂ : C ->A[R] D) : A × C ->A[R] B × D
参数：f₁ : A ->A[R] B；f₂ : C ->A[R] D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.map` of two continuous algebra homomorphisms.
-/
def prodMap {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A →A[R] B)
    (f₂ : C →A[R] D) : A × C →A[R] B × D :=
  (f₁.comp (fst R A C)).prod (f₂.comp (snd R A C))


@[simp, norm_cast]
/-
**ContinuousAlgHom.coe_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_prodMap {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f
₁ : A ->A[R] B) (f₂ : C ->A[R] D) : (f₁.prodMap f₂ : A × C ->ₐ[R] B × D) = (f₁ :
 A ->ₐ[R] B).prodMap (f₂ : C ->ₐ[R] D)
参数：f₁ : A ->A[R] B；f₂ : C ->A[R] D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodMap {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A →A[R] B)
    (f₂ : C →A[R] D) :
    (f₁.prodMap f₂ : A × C →ₐ[R] B × D) = (f₁ : A →ₐ[R] B).prodMap (f₂ : C →ₐ[R] D) :=
  rfl

@[simp, norm_cast]
/-
**ContinuousAlgHom.coe_prodMap'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_prodMap' {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (
f₁ : A ->A[R] B) (f₂ : C ->A[R] D) : ⇑(f₁.prodMap f₂) = Prod.map f₁ f₂
参数：f₁ : A ->A[R] B；f₂ : C ->A[R] D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodMap' {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A →A[R] B)
    (f₂ : C →A[R] D) : ⇑(f₁.prodMap f₂) = Prod.map f₁ f₂ :=
  rfl

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- `ContinuousAlgHom.prod` as an `Equiv`. -/
@[simps apply]
/-
**ContinuousAlgHom.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgHom`。
形式化陈述：prodEquiv : (A ->A[R] B) × (A ->A[R] C) ≃ (A ->A[R] B × C) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousAlgHom.prod` as an `Equiv`.
-/
def prodEquiv : (A →A[R] B) × (A →A[R] C) ≃ (A →A[R] B × C) where
  toFun f  := f.1.prod f.2
  invFun f := ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩

end prod

section subalgebra

variable {R A}
variable [TopologicalSpace A]
variable {B : Type*} [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Restrict codomain of a continuous algebra morphism. -/
/-
**ContinuousAlgHom.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgHom`。
形式化陈述：codRestrict (f : A ->A[R] B) (p : Subalgebra R B) (h : forall x, f x in p)
 : A ->A[R] p where cont
参数：f : A ->A[R] B；p : Subalgebra R B；h : forall x, f x in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict codomain of a continuous algebra morphism.
-/
def codRestrict (f : A →A[R] B) (p : Subalgebra R B) (h : ∀ x, f x ∈ p) : A →A[R] p where
  cont     := f.continuous.subtype_mk _
  toAlgHom := (f : A →ₐ[R] B).codRestrict p h

@[norm_cast]
/-
**ContinuousAlgHom.coe_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：coe_codRestrict (f : A ->A[R] B) (p : Subalgebra R B) (h : forall x, f x i
n p) : (f.codRestrict p h : A ->ₐ[R] p) = (f : A ->ₐ[R] B).codRestrict p h
参数：f : A ->A[R] B；p : Subalgebra R B；h : forall x, f x in p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_codRestrict (f : A →A[R] B) (p : Subalgebra R B) (h : ∀ x, f x ∈ p) :
    (f.codRestrict p h : A →ₐ[R] p) = (f : A →ₐ[R] B).codRestrict p h :=
  rfl

@[simp]
/-
**ContinuousAlgHom.coe_codRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAl
gHom`。
形式化陈述：coe_codRestrict_apply (f : A ->A[R] B) (p : Subalgebra R B) (h : forall x,
 f x in p) (x) : (f.codRestrict p h x : B) = f x
参数：f : A ->A[R] B；p : Subalgebra R B；h : forall x, f x in p；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_codRestrict_apply (f : A →A[R] B) (p : Subalgebra R B) (h : ∀ x, f x ∈ p) (x) :
    (f.codRestrict p h x : B) = f x :=
  rfl

/-- Restrict the codomain of a continuous algebra homomorphism `f` to `f.range`. -/
@[reducible]
/-
**ContinuousAlgHom.rangeRestrict** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgHom`。
形式化陈述：rangeRestrict (f : A ->A[R] B)
参数：f : A ->A[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the codomain of a continuous algebra homomorphism `f` to `f.range`.
-/
def rangeRestrict (f : A →A[R] B) :=
  f.codRestrict (@AlgHom.range R A B _ _ _ _ _ f) (@AlgHom.mem_range_self R A B _ _ _ _ _ f)

@[simp]
/-
**ContinuousAlgHom.coe_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom
`。
形式化陈述：coe_rangeRestrict (f : A ->A[R] B) : (f.rangeRestrict : A ->ₐ[R] (@AlgHom.
range R A B _ _ _ _ _ f)) = (f : A ->ₐ[R] B).rangeRestrict
参数：f : A ->A[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_rangeRestrict (f : A →A[R] B) :
    (f.rangeRestrict : A →ₐ[R] (@AlgHom.range R A B _ _ _ _ _ f)) =
      (f : A →ₐ[R] B).rangeRestrict :=
  rfl

/-- `Subalgebra.val` as a `ContinuousAlgHom`. -/
/-
**ContinuousAlgHom._root_.Subalgebra.valA** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousA
lgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Subalgebra.val` as a `ContinuousAlgHom`.
-/
def _root_.Subalgebra.valA (p : Subalgebra R A) : p →A[R] A where
  cont := continuous_subtype_val
  toAlgHom := p.val

@[simp, norm_cast]
/-
**ContinuousAlgHom._root_.Subalgebra.coe_valA** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subalgebra.coe_valA (p : Subalgebra R A) : p.valA = p.subtype :=
  rfl

@[simp]
/-
**ContinuousAlgHom._root_.Subalgebra.coe_valA'** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subalgebra.coe_valA' (p : Subalgebra R A) : ⇑p.valA = p.subtype :=
  rfl

@[simp]
/-
**ContinuousAlgHom._root_.Subalgebra.valA_apply** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subalgebra.valA_apply (p : Subalgebra R A) (x : p) : p.valA x = x :=
  rfl

@[simp]
/-
**ContinuousAlgHom._root_.Submodule.range_valA** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Submodule.range_valA (p : Subalgebra R A) :
    @AlgHom.range R p A _ _ _ _ _ p.valA = p :=
  Subalgebra.range_val p

end subalgebra

section Ring


variable {S : Type*} [Ring S] [TopologicalSpace S] [Algebra R S] {B : Type*} [Ring B]
  [TopologicalSpace B] [Algebra R B]

/-
**ContinuousAlgHom.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：∀ (R : Type u_1) [inst : CommSemiring R] {S : Type u_3} [inst_1 : Ring S] 
[inst_2 : TopologicalSpace S]   [inst_3 : Algebra R S] {B : Type u_4} [inst_4 : 
Ring B] [inst_5 : TopologicalSpace B] [inst_6 : Algebra R B]   (f : S →A[R] B) (
x : S), f (-x) = -f x
参数：R : Type u_1；f : S →A[R] B；x : S；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `ContinuousAlgHom.instAlgHomClass`：∀ {R : Type u_1} [inst : CommSemiring 
R] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : TopologicalSpace A]   {B : Typ
e u_3} [inst_3 : Semir…
-/
protected theorem map_neg (f : S →A[R] B) (x : S) : f (-x) = -f x := map_neg f x
/-
**ContinuousAlgHom.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgHom`。
形式化陈述：∀ (R : Type u_1) [inst : CommSemiring R] {S : Type u_3} [inst_1 : Ring S] 
[inst_2 : TopologicalSpace S]   [inst_3 : Algebra R S] {B : Type u_4} [inst_4 : 
Ring B] [inst_5 : TopologicalSpace B] [inst_6 : Algebra R B]   (f : S →A[R] B) (
x y : S), f (x - y) = f x - f y
参数：R : Type u_1；f : S →A[R] B；x y : S；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `ContinuousAlgHom.instAlgHomClass`：∀ {R : Type u_1} [inst : CommSemiring 
R] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : TopologicalSpace A]   {B : Typ
e u_3} [inst_3 : Semir…
-/
protected theorem map_sub (f : S →A[R] B) (x y : S) : f (x - y) = f x - f y := map_sub f x y

end Ring


section RestrictScalars

variable {S : Type*} [CommSemiring S] [Algebra R S] {B : Type*} [Ring B] [TopologicalSpace B]
  [Algebra R B] [Algebra S B] [IsScalarTower R S B] {C : Type*} [Ring C] [TopologicalSpace C]
  [Algebra R C] [Algebra S C] [IsScalarTower R S C]

/-- If `A` is an `R`-algebra, then a continuous `A`-algebra morphism can be interpreted as a
continuous `R`-algebra morphism. -/
/-
**ContinuousAlgHom.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgHom`。
形式化陈述：restrictScalars (f : B ->A[S] C) : B ->A[R] C
参数：f : B ->A[S] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is an `R`-algebra, then a continuous `A`-algebra morphism can be interpre
ted as a
continuous `R`-algebra morphism.
-/
def restrictScalars (f : B →A[S] C) : B →A[R] C :=
  ⟨(f : B →ₐ[S] C).restrictScalars R, f.continuous⟩

variable {R}

@[simp]
/-
**ContinuousAlgHom.coe_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgH
om`。
形式化陈述：coe_restrictScalars (f : B ->A[S] C) : (f.restrictScalars R : B ->ₐ[R] C) 
= (f : B ->ₐ[S] C).restrictScalars R
参数：f : B ->A[S] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalars (f : B →A[S] C) :
    (f.restrictScalars R : B →ₐ[R] C) = (f : B →ₐ[S] C).restrictScalars R :=
  rfl

@[simp]
/-
**ContinuousAlgHom.coe_restrictScalars'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlg
Hom`。
形式化陈述：coe_restrictScalars' (f : B ->A[S] C) : ⇑(f.restrictScalars R) = f
参数：f : B ->A[S] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalars' (f : B →A[S] C) : ⇑(f.restrictScalars R) = f :=
  rfl

end RestrictScalars

end ContinuousAlgHom

end

variable {R : Type*} [CommSemiring R]
variable {A : Type u} [TopologicalSpace A]
variable [Semiring A] [Algebra R A]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTopologicalSemiring A] (s : Subalgebra R A) : IsTopologicalSemiring s :=
  s.toSubsemiring.topologicalSemiring
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsSemitopologicalSemiring A] (s : Subalgebra R A) : IsSemitopologicalSemiring s :=
  s.toSubsemiring.semitopologicalSemiring

variable [IsSemitopologicalSemiring A]
/-
**Subalgebra.le_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.le_topologicalClosure (s : Subalgebra R A) : s <= s.topological
Closure
参数：s : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Subalgebra.le_topologicalClosure (s : Subalgebra R A) : s ≤ s.topologicalClosure :=
  subset_closure
/-
**Subalgebra.isClosed_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.isClosed_topologicalClosure (s : Subalgebra R A) : IsClosed (s.
topologicalClosure : Set A)
参数：s : Subalgebra R A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem Subalgebra.isClosed_topologicalClosure (s : Subalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) := by convert! @isClosed_closure A _ s
/-
**Subalgebra.topologicalClosure_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.topologicalClosure_minimal {s t : Subalgebra R A} (h : s <= t) 
(ht : IsClosed (t : Set A)) : s.topologicalClosure <= t
参数：h : s <= t；ht : IsClosed (t : Set A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
-/
theorem Subalgebra.topologicalClosure_minimal {s t : Subalgebra R A} (h : s ≤ t)
    (ht : IsClosed (t : Set A)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

@[gcongr]
/-
**Subalgebra.topologicalClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.topologicalClosure_mono {s t : Subalgebra R A} (h : s <= t) : s
.topologicalClosure <= t.topologicalClosure
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem Subalgebra.topologicalClosure_mono {s t : Subalgebra R A} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  closure_mono h

variable (R) in
open Algebra in
/-
**Subalgebra.topologicalClosure_adjoin_le_centralizer_centralizer** 是 Mathlib 中的
一个引理，位于命名空间 ``。
形式化陈述：Subalgebra.topologicalClosure_adjoin_le_centralizer_centralizer [T2Space A
] (s : Set A) : (adjoin R s).topologicalClosure <= centralizer R (centralizer R 
s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.topologicalClosure_minimal`：Subalgebra.topologicalClosure_min
imal {s t : Subalgebra R A} (h : s <= t) (ht : IsClosed (t : Set A)) : s.topolog
icalClosure <= t
· 使用引理 `Algebra.adjoin_le_centralizer_centralizer`：adjoin_le_centralizer_central
izer (s : Set A) : adjoin R s <= Subalgebra.centralizer R (Subalgebra.centralize
r R s)
· 使用引理 `Set.isClosed_centralizer`：Set.isClosed_centralizer {M : Type*} (s : Set 
M) [Mul M] [TopologicalSpace M] [SeparatelyContinuousMul M] [T2Space M] : IsClos
ed (centralize…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
lemma Subalgebra.topologicalClosure_adjoin_le_centralizer_centralizer [T2Space A] (s : Set A) :
    (adjoin R s).topologicalClosure ≤ centralizer R (centralizer R s) :=
  topologicalClosure_minimal (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

/-- If a subalgebra of a topological algebra is commutative, then so is its topological closure.

See note [reducible non-instances]. -/
/-
**Subalgebra.commSemiringTopologicalClosure** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Subalgebra.commSemiringTopologicalClosure [T2Space A] (s : Subalgebra R A)
 (hs : forall x y : s, x * y = y * x) : CommSemiring s.topologicalClosure
参数：s : Subalgebra R A；hs : forall x y : s, x * y = y * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a subalgebra of a topological algebra is commutative, then so is its topologi
cal closure.

See note [reducible non-instances].
-/
abbrev Subalgebra.commSemiringTopologicalClosure [T2Space A] (s : Subalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }

/-- This is really a statement about topological algebra isomorphisms,
but we don't have those, so we use the clunky approach of talking about
an algebra homomorphism, and a separate homeomorphism,
along with a witness that as functions they are the same.
-/
/-
**Subalgebra.topologicalClosure_comap_homeomorph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.topologicalClosure_comap_homeomorph (s : Subalgebra R A) {B : T
ype*} [TopologicalSpace B] [Ring B] [IsSemitopologicalRing B] [Algebra R B] (f :
 B ->ₐ[R] A) (f' : B ≃ₜ A) (w : (f : B -> A) = f') : s.topologicalClosure.comap 
f = (s.comap f).topologicalClosure
参数：s : Subalgebra R A；f : B ->ₐ[R] A；f' : B ≃ₜ A；w : (f : B -> A) = f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.coe_comap`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring
 B] [inst_…
· 使用定理 `Homeomorph.preimage_closure`：preimage_closure (h : X ≃ₜ Y) (s : Set Y) :
 h ⁻¹' closure s = closure (h ⁻¹' s)

--- 原说明 ---
This is really a statement about topological algebra isomorphisms,
but we don't have those, so we use the clunky approach of talking about
an algebra homomorphism, and a separate homeomorphism,
along with a witness that as functions they are the same.
-/
theorem Subalgebra.topologicalClosure_comap_homeomorph (s : Subalgebra R A) {B : Type*}
    [TopologicalSpace B] [Ring B] [IsSemitopologicalRing B] [Algebra R B] (f : B →ₐ[R] A)
    (f' : B ≃ₜ A) (w : (f : B → A) = f') :
    s.topologicalClosure.comap f = (s.comap f).topologicalClosure := by
  apply SetLike.ext'
  simp only [Subalgebra.topologicalClosure_coe]
  simp only [Subalgebra.coe_comap]
  rw [w]
  exact f'.preimage_closure _

variable (R)

open Subalgebra

/-- The topological closure of the subalgebra generated by a single element. -/
/-
**Algebra.elemental** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Algebra.elemental (x : A) : Subalgebra R A
参数：x : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topological closure of the subalgebra generated by a single element.
-/
def Algebra.elemental (x : A) : Subalgebra R A :=
  (Algebra.adjoin R ({x} : Set A)).topologicalClosure

namespace Algebra.elemental

@[simp, aesop safe (rule_sets := [SetLike])]
/-
**Algebra.elemental.self_mem** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.elemental`。
形式化陈述：self_mem (x : A) : x in elemental R x
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.le_topologicalClosure`：Subalgebra.le_topologicalClosure (s : 
Subalgebra R A) : s <= s.topologicalClosure
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
-/
theorem self_mem (x : A) : x ∈ elemental R x :=
  le_topologicalClosure _ <| self_mem_adjoin_singleton R x

variable {R} in
/-
**Algebra.elemental.le_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.elemental`。
形式化陈述：le_of_mem {x : A} {s : Subalgebra R A} (hs : IsClosed (s : Set A)) (hx : x
 in s) : elemental R x <= s
参数：hs : IsClosed (s : Set A)；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.topologicalClosure_minimal`：Subalgebra.topologicalClosure_min
imal {s t : Subalgebra R A} (h : s <= t) (ht : IsClosed (t : Set A)) : s.topolog
icalClosure <= t
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem le_of_mem {x : A} {s : Subalgebra R A} (hs : IsClosed (s : Set A)) (hx : x ∈ s) :
    elemental R x ≤ s :=
  topologicalClosure_minimal (adjoin_le <| by simpa using hx) hs

variable {R} in
/-
**Algebra.elemental.le_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.elemental`。
形式化陈述：le_iff_mem {x : A} {s : Subalgebra R A} (hs : IsClosed (s : Set A)) : elem
ental R x <= s ↔ x in s
参数：hs : IsClosed (s : Set A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.elemental.self_mem`：self_mem (x : A) : x in elemental R x
· 使用定理 `Algebra.elemental.le_of_mem`：le_of_mem {x : A} {s : Subalgebra R A} (hs 
: IsClosed (s : Set A)) (hx : x in s) : elemental R x <= s
-/
theorem le_iff_mem {x : A} {s : Subalgebra R A} (hs : IsClosed (s : Set A)) :
    elemental R x ≤ s ↔ x ∈ s :=
  ⟨fun h ↦ h (self_mem R x), fun h ↦ le_of_mem hs h⟩
/-
**Algebra.elemental.isClosed** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.elemental`。
形式化陈述：isClosed (x : A) : IsClosed (elemental R x : Set A)
参数：x : A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.isClosed_topologicalClosure`：Subalgebra.isClosed_topologicalC
losure (s : Subalgebra R A) : IsClosed (s.topologicalClosure : Set A)
-/
instance isClosed (x : A) : IsClosed (elemental R x : Set A) :=
  isClosed_topologicalClosure _

open scoped IsMulCommutative in
/-
**Algebra.elemental.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.elemental`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space A] {x : A} : CommSemiring (elemental R x) :=
  fast_instance% commSemiringTopologicalClosure _ mul_comm
/-
**Algebra.elemental.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.elemental`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type*} [UniformSpace A] [CompleteSpace A] [Semiring A]
    [IsSemitopologicalSemiring A] [Algebra R A] (x : A) :
    CompleteSpace (elemental R x) :=
  isClosed_closure.completeSpace_coe

/-- The coercion from an elemental algebra to the full algebra is a `IsClosedEmbedding`. -/
/-
**Algebra.elemental.isClosedEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.ele
mental`。
形式化陈述：isClosedEmbedding_coe (x : A) : IsClosedEmbedding ((↑) : elemental R x -> 
A) where eq_induced
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }

--- 原说明 ---
The coercion from an elemental algebra to the full algebra is a `IsClosedEmbeddi
ng`.
-/
theorem isClosedEmbedding_coe (x : A) : IsClosedEmbedding ((↑) : elemental R x → A) where
  eq_induced := rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x
/-
**Algebra.elemental.le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.elemental`。
形式化陈述：le_centralizer_centralizer [T2Space A] (x : A) : elemental R x <= centrali
zer R (centralizer R {x})
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subalgebra.topologicalClosure_adjoin_le_centralizer_centralizer`：Subalge
bra.topologicalClosure_adjoin_le_centralizer_centralizer [T2Space A] (s : Set A)
 : (adjoin R s).topologicalClosure <= centralizer R (…
-/
lemma le_centralizer_centralizer [T2Space A] (x : A) :
    elemental R x ≤ centralizer R (centralizer R {x}) :=
  topologicalClosure_adjoin_le_centralizer_centralizer ..

end Algebra.elemental

end TopologicalAlgebra

section Ring

variable {R : Type*} [CommRing R]
variable {A : Type u} [TopologicalSpace A]
variable [Ring A]
variable [Algebra R A] [IsSemitopologicalRing A]

/-- If a subalgebra of a topological algebra is commutative, then so is its topological closure.
See note [reducible non-instances]. -/
/-
**Subalgebra.commRingTopologicalClosure** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Subalgebra.commRingTopologicalClosure [T2Space A] (s : Subalgebra R A) (hs
 : forall x y : s, x * y = y * x) : CommRing s.topologicalClosure
参数：s : Subalgebra R A；hs : forall x y : s, x * y = y * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a subalgebra of a topological algebra is commutative, then so is its topologi
cal closure.
See note [reducible non-instances].
-/
abbrev Subalgebra.commRingTopologicalClosure [T2Space A] (s : Subalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : CommRing s.topologicalClosure :=
  { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space A] {x : A} : CommRing (elemental R x) where
  mul_comm := mul_comm

end Ring

