/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Completion of an inner product space

We show that the separation quotient and the completion of an inner product space are inner
product spaces.
-/

public section

noncomputable section

variable {𝕜 E F : Type*} [RCLike 𝕜]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section SeparationQuotient
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-
**Inseparable.inner_eq_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Inseparable.inner_eq_inner {x₁ x₂ y₁ y₂ : E} (hx : Inseparable x₁ x₂) (hy 
: Inseparable y₁ y₂) : ⟪x₁, y₁⟫ = ⟪x₂, y₂⟫
参数：hx : Inseparable x₁ x₂；hy : Inseparable y₁ y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `Inseparable.map`：map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y
· 使用定理 `Inseparable.prod`：Inseparable.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ᵢ x
₂) (hy : y₁ ~ᵢ y₂) : (x₁, y₁) ~ᵢ (x₂, y₂)
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
-/
theorem Inseparable.inner_eq_inner {x₁ x₂ y₁ y₂ : E}
    (hx : Inseparable x₁ x₂) (hy : Inseparable y₁ y₂) :
    ⟪x₁, y₁⟫ = ⟪x₂, y₂⟫ :=
  ((hx.prod hy).map continuous_inner).eq

namespace SeparationQuotient

/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inner 𝕜 (SeparationQuotient E) where
  inner := SeparationQuotient.lift₂ (inner 𝕜) fun _ _ _ _ => Inseparable.inner_eq_inner

@[simp]
/-
**SeparationQuotient.inner_mk_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：inner_mk_mk (x y : E) : ⟪mk x, mk y⟫ = ⟪x, y⟫
参数：x y : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inner_mk_mk (x y : E) :
    ⟪mk x, mk y⟫ = ⟪x, y⟫ := rfl
/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InnerProductSpace 𝕜 (SeparationQuotient E) where
  norm_sq_eq_re_inner := Quotient.ind norm_sq_eq_re_inner
  conj_inner_symm := Quotient.ind₂ inner_conj_symm
  add_left := Quotient.ind fun x => Quotient.ind₂ <| inner_add_left x
  smul_left := Quotient.ind₂ inner_smul_left

end SeparationQuotient

end SeparationQuotient

section UniformSpace.Completion

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace UniformSpace.Completion

open RCLike Function

/-
**UniformSpace.Completion.toInner** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Comple
tion`。
形式化陈述：toInner {𝕜' E' : Type*} [TopologicalSpace 𝕜'] [UniformSpace E'] [Inner 𝕜' 
E'] : Inner 𝕜' (Completion E') where inner
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toInner {𝕜' E' : Type*} [TopologicalSpace 𝕜'] [UniformSpace E'] [Inner 𝕜' E'] :
    Inner 𝕜' (Completion E') where
  inner := curry <| (isDenseInducing_coe.prodMap isDenseInducing_coe).extend (uncurry (inner 𝕜'))

@[simp]
/-
**UniformSpace.Completion.inner_coe** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Comp
letion`。
形式化陈述：inner_coe (a b : E) : ⟪(a : Completion E), (b : Completion E)⟫ = ⟪a, b⟫
参数：a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_eq`：extend_eq [T2Space γ] (di : IsDenseInducing i
) {f : α -> γ} (hf : Continuous f) (a : α) : di.extend f (i a) = f a
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsDenseInducing.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{δ : Type u_4} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst
_2 : Topologi…
· 使用定理 `UniformSpace.Completion.isDenseInducing_coe`：isDenseInducing_coe : IsDen
seInducing ((↑) : α -> Completion α)
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
-/
theorem inner_coe (a b : E) : ⟪(a : Completion E), (b : Completion E)⟫ = ⟪a, b⟫ :=
  (isDenseInducing_coe.prodMap isDenseInducing_coe).extend_eq
    (continuous_inner : Continuous (uncurry (inner 𝕜))) (a, b)
/-
**UniformSpace.Completion.continuous_inner** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpa
ce.Completion`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E],   Continuous (Function.uncurry (in
ner 𝕜))
参数：Function.uncurry (inner 𝕜)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.toInner.eq_1`：∀ {𝕜' : Type u_4} {E' : Type u_5} 
[inst : TopologicalSpace 𝕜'] [inst_1 : UniformSpace E'] [inst_2 : Inner 𝕜' E'], 
  UniformSpace.Completion.…
· 使用定理 `Inner.inner.eq_1`：∀ (𝕜 : Type u_4) (E : Type u_5) [self : Inner 𝕜 E], in
ner 𝕜 = self.1
· 使用定理 `Function.uncurry_curry`：∀ {α : Type u_1} {β : Type u_2} {φ : Sort u_3} (
f : α × β → φ), Function.uncurry (Function.curry f) = f
· 使用定理 `IsDenseInducing.extend_Z_bilin`：extend_Z_bilin : Continuous (extend (de.
prodMap df) (fun p : β × δ => φ p.1 p.2))
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformSpace.Completion.isDenseInducing_toCompl`：isDenseInducing_toCompl
 : IsDenseInducing (toCompl : α -> Completion α)
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
-/
protected theorem continuous_inner :
    Continuous (uncurry (inner 𝕜 (E := Completion E))) := by
  let inner' : E →+ E →+ 𝕜 :=
    { toFun := fun x => (innerₛₗ 𝕜 x).toAddMonoidHom
      map_zero' := by ext x; exact inner_zero_left _
      map_add' := fun x y => by ext z; exact inner_add_left _ _ _ }
  have : Continuous fun p : E × E => inner' p.1 p.2 := continuous_inner
  rw [Completion.toInner, inner, uncurry_curry _]
  change
    Continuous
      (((isDenseInducing_toCompl E).prodMap (isDenseInducing_toCompl E)).extend fun p : E × E =>
        inner' p.1 p.2)
  exact (isDenseInducing_toCompl E).extend_Z_bilin (isDenseInducing_toCompl E) this

@[fun_prop]
/-
**UniformSpace.Completion.Continuous.inner** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpa
ce.Completion.Continuous`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {α : Type u_4} [inst_3 : Topologi
calSpace α] {f g : α → UniformSpace.Completion E},   Continuous f → Continuous g
 → Continuous fun x => inner 𝕜 (f x) (g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `UniformSpace.Completion.continuous_inner`：∀ {𝕜 : Type u_1} {E : Type u_2
} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSp
ace 𝕜 E],   Continuous (Functi…
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
-/
protected theorem Continuous.inner {α : Type*} [TopologicalSpace α] {f g : α → Completion E}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x : α => ⟪f x, g x⟫) :=
  UniformSpace.Completion.continuous_inner.comp (hf.prodMk hg :)
/-
**UniformSpace.Completion.innerProductSpace** 是 Mathlib 中的一个实例，位于命名空间 `UniformSp
ace.Completion`。
形式化陈述：innerProductSpace : InnerProductSpace 𝕜 (Completion E) where norm_sq_eq_re
_inner x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance innerProductSpace : InnerProductSpace 𝕜 (Completion E) where
  norm_sq_eq_re_inner x :=
    Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop))
      fun a => by simp only [norm_coe, inner_coe, inner_self_eq_norm_sq]
  conj_inner_symm x y :=
    Completion.induction_on₂ x y
      (isClosed_eq (continuous_conj.comp (by fun_prop)) (by fun_prop))
      fun a b => by simp only [inner_coe, inner_conj_symm]
  add_left x y z :=
    Completion.induction_on₃ x y z (isClosed_eq (by fun_prop) (by fun_prop))
      fun a b c => by simp only [← coe_add, inner_coe, inner_add_left]
  smul_left x y c :=
    Completion.induction_on₂ x y
      (isClosed_eq (Continuous.inner (continuous_fst.const_smul c) continuous_snd)
        ((continuous_const_mul _).comp (by fun_prop)))
      fun a b => by simp only [← coe_smul c a, inner_coe, inner_smul_left]

end UniformSpace.Completion

end UniformSpace.Completion

