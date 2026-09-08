/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin

/-!
# Weak Dual in Topological Vector Spaces

We prove that the weak topology induced by a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` is locally
convex and we explicitly give a neighborhood basis in terms of the family of seminorms
`fun x => ‖B x y‖` for `y : F`.

## Main definitions

* `LinearMap.toSeminorm`: turn a linear form `f : E →ₗ[𝕜] 𝕜` into a seminorm `fun x => ‖f x‖`.
* `LinearMap.toSeminormFamily`: turn a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` into a map
  `F → Seminorm 𝕜 E`.

## Main statements

* `LinearMap.hasBasis_weakBilin`: the seminorm balls of `B.toSeminormFamily` form a
  neighborhood basis of `0` in the weak topology.
* `LinearMap.toSeminormFamily.withSeminorms`: the topology of a weak space is induced by the
  family of seminorms `B.toSeminormFamily`.
* `WeakBilin.locallyConvexSpace`: a space endowed with a weak topology is locally convex.
* `LinearMap.rightDualEquiv`: When `B` is right-separating, `F` is linearly equivalent to the
  strong dual of `E` with the weak topology.
* `LinearMap.leftDualEquiv`: When `B` is left-separating, `E` is linearly equivalent to the
  strong dual of `F` with the weak topology.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]
* [Rudin, *Functional Analysis*][rudin1991]

## Tags

weak dual, seminorm
-/

@[expose] public section


variable {𝕜 E F : Type*}

open Topology

section BilinForm

namespace LinearMap

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- Construct a seminorm from a linear form `f : E →ₗ[𝕜] 𝕜` over a normed field `𝕜` by
`fun x => ‖f x‖` -/
/-
**LinearMap.toSeminorm** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toSeminorm (f : E ->ₗ[𝕜] 𝕜) : Seminorm 𝕜 E
参数：f : E ->ₗ[𝕜] 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a seminorm from a linear form `f : E →ₗ[𝕜] 𝕜` over a normed field `𝕜` 
by
`fun x => ‖f x‖`
-/
def toSeminorm (f : E →ₗ[𝕜] 𝕜) : Seminorm 𝕜 E :=
  (normSeminorm 𝕜 𝕜).comp f
/-
**LinearMap.coe_toSeminorm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_toSeminorm {f : E ->ₗ[𝕜] 𝕜} : ⇑f.toSeminorm = fun x => ‖f x‖
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSeminorm {f : E →ₗ[𝕜] 𝕜} : ⇑f.toSeminorm = fun x => ‖f x‖ :=
  rfl

@[simp]
/-
**LinearMap.toSeminorm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toSeminorm_apply {f : E ->ₗ[𝕜] 𝕜} {x : E} : f.toSeminorm x = ‖f x‖
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSeminorm_apply {f : E →ₗ[𝕜] 𝕜} {x : E} : f.toSeminorm x = ‖f x‖ :=
  rfl
/-
**LinearMap.toSeminorm_ball_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toSeminorm_ball_zero {f : E ->ₗ[𝕜] 𝕜} {r : Real} : Seminorm.ball f.toSemin
orm 0 r = { x : E | ‖f x‖ < r }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.ball_zero_eq`：ball_zero_eq : ball p 0 r = { y : E | p y < r }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSeminorm_ball_zero {f : E →ₗ[𝕜] 𝕜} {r : ℝ} :
    Seminorm.ball f.toSeminorm 0 r = { x : E | ‖f x‖ < r } := by
  simp only [Seminorm.ball_zero_eq, toSeminorm_apply]
/-
**LinearMap.toSeminorm_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toSeminorm_comp (f : F ->ₗ[𝕜] 𝕜) (g : E ->ₗ[𝕜] F) : f.toSeminorm.comp g = 
(f.comp g).toSeminorm
参数：f : F ->ₗ[𝕜] 𝕜；g : E ->ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSeminorm_comp (f : F →ₗ[𝕜] 𝕜) (g : E →ₗ[𝕜] F) :
    f.toSeminorm.comp g = (f.comp g).toSeminorm := by
  ext
  simp only [Seminorm.comp_apply, toSeminorm_apply, coe_comp, Function.comp_apply]

/-- Construct a family of seminorms from a bilinear form. -/
/-
**LinearMap.toSeminormFamily** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toSeminormFamily (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) : SeminormFamily 𝕜 E F
参数：B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a family of seminorms from a bilinear form.
-/
def toSeminormFamily (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : SeminormFamily 𝕜 E F := fun y =>
  (B.flip y).toSeminorm

@[simp]
/-
**LinearMap.toSeminormFamily_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toSeminormFamily_apply {B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜} {x y} : (B.toSeminormFami
ly y) x = ‖B x y‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem toSeminormFamily_apply {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {x y} : (B.toSeminormFamily y) x = ‖B x y‖ :=
  rfl
/-
**LinearMap.dualEmbedding_injective_of_separatingRight** 是 Mathlib 中的一个引理，位于命名空间
 `LinearMap`。
形式化陈述：dualEmbedding_injective_of_separatingRight (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) (hr :
 B.SeparatingRight) : Function.Injective (WeakBilin.eval B)
参数：B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜；hr : B.SeparatingRight。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.separatingRight_iff_linear_flip_nontrivial`：separatingRight_if
f_linear_flip_nontrivial {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingRight ↔ f
orall y : M₂, B.flip y = 0 -> y = 0
· 使用定理 `ContinuousLinearMap.coe_inj`：coe_inj {f g : M₁ ->SL[σ₁₂] M₂} : (f : M₁ -
>ₛₗ[σ₁₂] M₂) = g ↔ f = g
-/
lemma dualEmbedding_injective_of_separatingRight (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (hr : B.SeparatingRight) :
    Function.Injective (WeakBilin.eval B) :=
  (injective_iff_map_eq_zero _).mpr (fun f hf ↦
    (separatingRight_iff_linear_flip_nontrivial.mp hr) f (ContinuousLinearMap.coe_inj.mpr hf))

variable {ι 𝕜 E F : Type*}

open Topology TopologicalSpace
open scoped NNReal

section

section TopologicalRing

variable [Finite ι] [Field 𝕜] [t𝕜 : TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [T0Space 𝕜]

/-- A linear functional `φ` can be expressed as a linear combination of linear functionals `f₁,…,fₙ`
if and only if `φ` is continuous with respect to the topology induced by `f₁,…,fₙ`. See
`LinearMap.mem_span_iff_continuous` for a result about arbitrary collections of linear functionals.
-/
/-
**LinearMap.mem_span_iff_continuous_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap`。
形式化陈述：mem_span_iff_continuous_of_finite {f : ι -> E ->ₗ[𝕜] 𝕜} (φ : E ->ₗ[𝕜] 𝕜) :
 φ in Submodule.span 𝕜 (Set.range f) ↔ Continuous[⨅ i, induced (f i) t𝕜, t𝕜] φ
参数：φ : E ->ₗ[𝕜] 𝕜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `continuous_iInf_dom`：continuous_iInf_dom {t₁ : ι -> TopologicalSpace α} 
{t₂ : TopologicalSpace β} {i : ι} : Continuous[t₁ i, t₂] f -> Continuous[iInf t₁
, t₂] f
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
· 使用定理 `continuous_zero`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace M] [inst_2 : Zero M],   Continuous 0
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `mem_span_of_iInf_ker_le_ker`：∀ {ι : Type u_3} {𝕜 : Type u_4} {E : Type u
_5} [inst : Field 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   [F
inite ι] {L : ι →…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_iInf`：nhds_iInf {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α} :
 @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `Inseparable.map`：map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y

--- 原说明 ---
A linear functional `φ` can be expressed as a linear combination of linear funct
ionals `f₁,…,fₙ`
if and only if `φ` is continuous with respect to the topology induced by `f₁,…,f
ₙ`. See
`LinearMap.mem_span_iff_continuous` for a result about arbitrary collections of 
linear functionals.
-/
theorem mem_span_iff_continuous_of_finite {f : ι → E →ₗ[𝕜] 𝕜} (φ : E →ₗ[𝕜] 𝕜) :
    φ ∈ Submodule.span 𝕜 (Set.range f) ↔ Continuous[⨅ i, induced (f i) t𝕜, t𝕜] φ := by
  let _ := ⨅ i, induced (f i) t𝕜
  constructor
  · exact Submodule.span_induction
      (Set.forall_mem_range.mpr fun i ↦ continuous_iInf_dom continuous_induced_dom) continuous_zero
      (fun _ _ _ _ ↦ .add) (fun c _ _ h ↦ h.const_smul c)
  · intro φ_cont
    refine mem_span_of_iInf_ker_le_ker fun x hx ↦ ?_
    simp_rw [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    have : Inseparable x 0 := by
      -- Maybe missing lemmas about `Inseparable`?
      simp_rw [Inseparable, nhds_iInf, nhds_induced, hx, map_zero]
    simpa only [map_zero] using (this.map φ_cont).eq

end TopologicalRing

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- A linear functional `φ` is in the span of a collection of linear functionals if and only if `φ`
is continuous with respect to the topology induced by the collection of linear functionals. See
`LinearMap.mem_span_iff_continuous_of_finite` for a result about finite collections of linear
functionals. -/
/-
**LinearMap.mem_span_iff_continuous** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mem_span_iff_continuous {f : ι -> E ->ₗ[𝕜] 𝕜} (φ : E ->ₗ[𝕜] 𝕜) : φ in Subm
odule.span 𝕜 (Set.range f) ↔ Continuous[⨅ i, induced (f i) inferInstance, inferI
nstance] φ
参数：φ : E ->ₗ[𝕜] 𝕜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `topologicalAddGroup_iInf`：∀ {G : Type w} {ι : Sort u_1} [inst : AddGroup
 G] {ts' : ι → TopologicalSpace G},   (∀ (i : ι), IsTopologicalAddGroup G) → IsT
opologicalAddG…
· 使用定理 `topologicalAddGroup_induced`：∀ {G : Type w} {H : Type x} [inst : Topolog
icalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {F : Type u_1}   [i
nst_3 : AddGroup …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `continuousSMul_iInf`：continuousSMul_iInf {ts' : ι -> TopologicalSpace X}
 (h : forall i, @ContinuousSMul M X _ _ (ts' i)) : @ContinuousSMul M X _ _ (⨅ i,
 ts' i)
· 使用定理 `continuousSMul_induced`：continuousSMul_induced : @ContinuousSMul R M₁ _ 
u (t.induced f)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithSeminorms.continuous_iff_continuous_comp`：continuous_iff_continuous_
comp {q : SeminormFamily 𝕝₂ F ι'} [TopologicalSpace E] [IsTopologicalAddGroup E]
 [TopologicalSpace F] (hq : WithSe…
· 使用定理 `norm_withSeminorms`：norm_withSeminorms (𝕜 E) [NormedField 𝕜] [Seminormed
AddCommGroup E] [NormedSpace 𝕜 E] : WithSeminorms fun _ : Fin 1 => normSeminorm 
𝕜 E
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Seminorm.continuous_iff`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : Nontriv
iallyNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [in
st_3 : Topolo…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `nhds_iInf`：nhds_iInf {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α} :
 @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a
· 使用定理 `iInf_subtype`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α]
 {p : ι → Prop} {f : Subtype p → α},   iInf f = ⨅ i, ⨅ (h : p i), f ⟨i, h⟩
· 使用定理 `Filter.mem_iInf_finite`：mem_iInf_finite {ι : Type*} {f : ι -> Filter α} 
(s) : s in iInf f ↔ exists t : Finset ι, s in ⨅ i in t, f i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
A linear functional `φ` is in the span of a collection of linear functionals if 
and only if `φ`
is continuous with respect to the topology induced by the collection of linear f
unctionals. See
`LinearMap.mem_span_iff_continuous_of_finite` for a result about finite collecti
ons of linear
functionals.
-/
theorem mem_span_iff_continuous {f : ι → E →ₗ[𝕜] 𝕜} (φ : E →ₗ[𝕜] 𝕜) :
    φ ∈ Submodule.span 𝕜 (Set.range f) ↔
    Continuous[⨅ i, induced (f i) inferInstance, inferInstance] φ := by
  let t𝕜 : TopologicalSpace 𝕜 := inferInstance
  let t₁ : TopologicalSpace E := ⨅ i, induced (f i) t𝕜
  let t₂ (s : Finset ι) : TopologicalSpace E := ⨅ i : s, induced (f i) t𝕜
  suffices
      Continuous[t₁, t𝕜] φ ↔ ∃ s : Finset ι, Continuous[t₂ s, t𝕜] φ by
    simp_rw [this, ← mem_span_iff_continuous_of_finite, Submodule.span_range_eq_iSup,
      iSup_subtype]
    rw [Submodule.mem_iSup_iff_exists_finset]
  have t₁_group : @IsTopologicalAddGroup E t₁ _ :=
    topologicalAddGroup_iInf fun _ ↦ topologicalAddGroup_induced _
  have t₂_group (s : Finset ι) : @IsTopologicalAddGroup E (t₂ s) _ :=
    topologicalAddGroup_iInf fun _ ↦ topologicalAddGroup_induced _
  have t₁_smul : @ContinuousSMul 𝕜 E _ _ t₁ :=
    continuousSMul_iInf fun _ ↦ continuousSMul_induced _
  have t₂_smul (s : Finset ι) : @ContinuousSMul 𝕜 E _ _ (t₂ s) :=
    continuousSMul_iInf fun _ ↦ continuousSMul_induced _
  simp_rw [WithSeminorms.continuous_iff_continuous_comp (norm_withSeminorms 𝕜 𝕜), forall_const]
  conv in Continuous _ => rw [Seminorm.continuous_iff one_pos, nhds_iInf]
  conv in Continuous _ =>
    rw [letI := t₂ s; Seminorm.continuous_iff one_pos, nhds_iInf, iInf_subtype]
  rw [Filter.mem_iInf_finite]
/-
**LinearMap.mem_span_iff_bound** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mem_span_iff_bound {f : ι -> E ->ₗ[𝕜] 𝕜} (φ : E ->ₗ[𝕜] 𝕜) : φ in Submodule
.span 𝕜 (Set.range f) ↔ exists s : Finset ι, exists c : Real>=0, φ.toSeminorm <=
 c • (s.sup fun i => (f i).toSeminorm)
参数：φ : E ->ₗ[𝕜] 𝕜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `topologicalAddGroup_iInf`：∀ {G : Type w} {ι : Sort u_1} [inst : AddGroup
 G] {ts' : ι → TopologicalSpace G},   (∀ (i : ι), IsTopologicalAddGroup G) → IsT
opologicalAddG…
· 使用定理 `topologicalAddGroup_induced`：∀ {G : Type w} {H : Type x} [inst : Topolog
icalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {F : Type u_1}   [i
nst_3 : AddGroup …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_iInf`：nhds_iInf {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α} :
 @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_norm_nhds_zero`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Fi
lter.comap norm (nhds 0) = nhds 0
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.mem_span_iff_continuous`：mem_span_iff_continuous {f : ι -> E -
>ₗ[𝕜] 𝕜} (φ : E ->ₗ[𝕜] 𝕜) : φ in Submodule.span 𝕜 (Set.range f) ↔ Continuous[⨅ i
, induced (f i) inferIn…
· 使用引理 `Seminorm.bound_of_continuous`：bound_of_continuous [t : TopologicalSpace 
E] (hp : WithSeminorms p) (q : Seminorm 𝕜 E) (hq : Continuous q) : exists s : Fi
nset ι, exists C :…
· 使用定理 `forall_const`：∀ {b : Prop} (α : Sort u_1) [i : Nonempty α], (∀ (a : α), 
b) ↔ b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `WithSeminorms.continuous_iff_continuous_comp`：continuous_iff_continuous_
comp {q : SeminormFamily 𝕝₂ F ι'} [TopologicalSpace E] [IsTopologicalAddGroup E]
 [TopologicalSpace F] (hq : WithSe…
· 使用定理 `norm_withSeminorms`：norm_withSeminorms (𝕜 E) [NormedField 𝕜] [Seminormed
AddCommGroup E] [NormedSpace 𝕜 E] : WithSeminorms fun _ : Fin 1 => normSeminorm 
𝕜 E
· 使用定理 `WithSeminorms.continuous_normedSpace_rng`：continuous_normedSpace_rng (F)
 [SeminormedAddCommGroup F] [NormedSpace 𝕝₂ F] [TopologicalSpace E] {p : ι -> Se
minorm 𝕝 E} (hp : WithSeminorm…
-/
theorem mem_span_iff_bound {f : ι → E →ₗ[𝕜] 𝕜} (φ : E →ₗ[𝕜] 𝕜) :
    φ ∈ Submodule.span 𝕜 (Set.range f) ↔
    ∃ s : Finset ι, ∃ c : ℝ≥0, φ.toSeminorm ≤
      c • (s.sup fun i ↦ (f i).toSeminorm) := by
  let t𝕜 : TopologicalSpace 𝕜 := inferInstance
  let t := ⨅ i, induced (f i) t𝕜
  have : IsTopologicalAddGroup E := topologicalAddGroup_iInf fun _ ↦ topologicalAddGroup_induced _
  have : WithSeminorms (fun i ↦ (f i).toSeminorm) := by
    simp_rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf, nhds_iInf, nhds_induced, map_zero,
      ← comap_norm_nhds_zero (E := 𝕜), Filter.comap_comap]
    rfl
  rw [LinearMap.mem_span_iff_continuous]
  constructor <;> intro H
  · rw [WithSeminorms.continuous_iff_continuous_comp (norm_withSeminorms 𝕜 𝕜), forall_const] at H
    rcases Seminorm.bound_of_continuous this _ H with ⟨s, C, -, hC⟩
    exact ⟨s, C, hC⟩
  · exact WithSeminorms.continuous_normedSpace_rng _ this _ H

variable [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- The Weak Representation Theorem: Every continuous functional on `E` endowed with
the `σ(E, F; B)`-topology is of the form `x ↦ B(x, y)` for some `y : F`. -/
/-
**LinearMap.dualEmbedding_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：dualEmbedding_surjective : Function.Surjective (WeakBilin.eval B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.coeLM_apply`：∀ {R : Type u_1} (S : Type u_4) [inst :
 Semiring R] [inst_1 : Semiring S] {M : Type u_6} [inst_2 : TopologicalSpace M] 
  [inst_3 : AddCommMo…
· 使用定理 `Continuous.le_induced`：Continuous.le_induced (h : Continuous[t, t'] f) :
 t <= t'.induced f
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.span_coe_eq_restrictScalars`：span_coe_eq_restrictScalars [Semi
ring S] [SMul S R] [Module S M] [IsScalarTower S R M] : span S (p : Set M) = p.r
estrictScalars S
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V

--- 原说明 ---
The Weak Representation Theorem: Every continuous functional on `E` endowed with
the `σ(E, F; B)`-topology is of the form `x ↦ B(x, y)` for some `y : F`.
-/
theorem dualEmbedding_surjective : Function.Surjective (WeakBilin.eval B) := fun f ↦ by
  have : f.toLinearMap ∈
      Submodule.span 𝕜 (ContinuousLinearMap.coeLM 𝕜 ∘ₗ WeakBilin.eval B).range := by
    simpa [coe_range, mem_span_iff_continuous, continuous_iff_le_induced, ← induced_to_pi] using!
      f.continuous.le_induced
  simpa

/-- When `B` is right-separating, `F` is linearly equivalent to the strong dual of `E` with the
weak topology. -/
/-
**LinearMap.rightDualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：rightDualEquiv (hr : B.SeparatingRight) : F ≃ₗ[𝕜] StrongDual 𝕜 (WeakBilin 
B)
参数：hr : B.SeparatingRight。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `B` is right-separating, `F` is linearly equivalent to the strong dual of `
E` with the
weak topology.
-/
noncomputable def rightDualEquiv (hr : B.SeparatingRight) : F ≃ₗ[𝕜] StrongDual 𝕜 (WeakBilin B) :=
  LinearEquiv.ofBijective (WeakBilin.eval B)
    ⟨dualEmbedding_injective_of_separatingRight B hr, dualEmbedding_surjective B⟩

/-- When `B` is left-separating, `E` is linearly equivalent to the strong dual of `F` with the
weak topology. -/
/-
**LinearMap.leftDualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：leftDualEquiv (hl : B.SeparatingLeft) : E ≃ₗ[𝕜] StrongDual 𝕜 (WeakBilin B.
flip)
参数：hl : B.SeparatingLeft。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `B` is left-separating, `E` is linearly equivalent to the strong dual of `F
` with the
weak topology.
-/
noncomputable def leftDualEquiv (hl : B.SeparatingLeft) : E ≃ₗ[𝕜] StrongDual 𝕜 (WeakBilin B.flip) :=
  rightDualEquiv _ (LinearMap.flip_separatingRight.mpr hl)

end NontriviallyNormedField

end

end LinearMap

end BilinForm

section Topology

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-
**LinearMap.weakBilin_withSeminorms** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.weakBilin_withSeminorms (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) : WithSeminorm
s (LinearMap.toSeminormFamily B : F -> Seminorm 𝕜 (WeakBilin B))
参数：B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `WithSeminorms.congr_equiv`：∀ {𝕜 : Type u_2} {E : Type u_6} {ι : Type u_9
} {ι' : Type u_10} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : 
_root_.Module 𝕜…
· 使用定理 `LinearMap.withSeminorms_induced`：LinearMap.withSeminorms_induced {q : Se
minormFamily 𝕜₂ F ι} (hq : WithSeminorms q) (f : E ->ₛₗ[σ₁₂] F) : WithSeminorms 
(topology
· 使用定理 `withSeminorms_pi`：withSeminorms_pi {κ : ι -> Type*} {E : ι -> Type*} [fo
rall i, AddCommGroup (E i)] [forall i, Module 𝕜 (E i)] [forall i, TopologicalSpa
ce (E …
· 使用定理 `norm_withSeminorms`：norm_withSeminorms (𝕜 E) [NormedField 𝕜] [Seminormed
AddCommGroup E] [NormedSpace 𝕜 E] : WithSeminorms fun _ : Fin 1 => normSeminorm 
𝕜 E
-/
theorem LinearMap.weakBilin_withSeminorms (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    WithSeminorms (LinearMap.toSeminormFamily B : F → Seminorm 𝕜 (WeakBilin B)) :=
  let e : F ≃ (Σ _ : F, Fin 1) := .symm <| .sigmaUnique _ _
  withSeminorms_induced (withSeminorms_pi (fun _ ↦ norm_withSeminorms 𝕜 𝕜))
    (LinearMap.ltoFun 𝕜 F 𝕜 𝕜 ∘ₗ B : (WeakBilin B) →ₗ[𝕜] (F → 𝕜)) |>.congr_equiv e
/-
**LinearMap.hasBasis_weakBilin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.hasBasis_weakBilin (B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) : (𝓝 (0 : WeakBilin
 B)).HasBasis (· in B.toSeminormFamily.basisSets) _root_.id
参数：B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `WithSeminorms.hasBasis`：WithSeminorms.hasBasis (hp : WithSeminorms p) : 
(𝓝 (0 : E)).HasBasis (fun s : Set E => s in p.basisSets) id
· 使用定理 `LinearMap.weakBilin_withSeminorms`：LinearMap.weakBilin_withSeminorms (B 
: E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) : WithSeminorms (LinearMap.toSeminormFamily B : F -> Semi
norm 𝕜 (WeakBilin B))
-/
theorem LinearMap.hasBasis_weakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    (𝓝 (0 : WeakBilin B)).HasBasis (· ∈ B.toSeminormFamily.basisSets) _root_.id :=
  LinearMap.weakBilin_withSeminorms B |>.hasBasis

end Topology

section LocallyConvex

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
variable [NormedSpace ℝ 𝕜] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]

/-
**WeakBilin.locallyConvexSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WeakBilin.locallyConvexSpace {B : E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜} : LocallyConvexSpac
e Real (WeakBilin B)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `WithSeminorms.toLocallyConvexSpace`：WithSeminorms.toLocallyConvexSpace {
p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) : LocallyConvexSpace Real E
· 使用定理 `LinearMap.weakBilin_withSeminorms`：LinearMap.weakBilin_withSeminorms (B 
: E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) : WithSeminorms (LinearMap.toSeminormFamily B : F -> Semi
norm 𝕜 (WeakBilin B))
-/
instance WeakBilin.locallyConvexSpace {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} :
    LocallyConvexSpace ℝ (WeakBilin B) :=
  B.weakBilin_withSeminorms.toLocallyConvexSpace

end LocallyConvex

