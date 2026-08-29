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

/--
theorem `Inseparable.inner_eq_inner` / 定理 `Inseparable.inner_eq_inner`

English:
theorem Inseparable.inner_eq_inner
  statement: {x₁ x₂ y₁ y₂ : E}
  proof: ((hx.prod hy).map continuous_inner).eq

中文:
定理 不可分.inner_eq_inner
  结论: {x₁ x₂ y₁ y₂ : E}
  证明: ((hx.prod hy).map continuous_inner).eq

Depends on / 依赖: continuous_inner, hx.prod
-/
theorem Inseparable.inner_eq_inner {x₁ x₂ y₁ y₂ : E}
    (hx : Inseparable x₁ x₂) (hy : Inseparable y₁ y₂) :
    ⟪x₁, y₁⟫ = ⟪x₂, y₂⟫ :=
  ((hx.prod hy).map continuous_inner).eq

namespace SeparationQuotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inner 𝕜 (SeparationQuotient E)
  body: SeparationQuotient.lift₂ (inner 𝕜) fun _ _ _ _ => Inseparable.inner_eq_inner

@[simp]

中文:
实例 :
  签名: 内积 𝕜 (SeparationQuotient E)
  定义体: SeparationQuotient.lift₂ (inner 𝕜) fun _ _ _ _ => Inseparable.inner_eq_inner

@[simp]

Depends on / 依赖: Inseparable, Inseparable.inner_eq_inner, SeparationQuotient, SeparationQuotient.lift, inner_eq_inner
-/
instance : Inner 𝕜 (SeparationQuotient E) where
  inner := SeparationQuotient.lift₂ (inner 𝕜) fun _ _ _ _ => Inseparable.inner_eq_inner

@[simp]
/--
theorem `inner_mk_mk` / 定理 `inner_mk_mk`

English:
theorem inner_mk_mk
  given: (x y : E)
  proof: rfl

中文:
定理 inner_mk_mk
  条件: (x y : E)
  证明: rfl
-/
theorem inner_mk_mk (x y : E) :
    ⟪mk x, mk y⟫ = ⟪x, y⟫ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InnerProductSpace 𝕜 (SeparationQuotient E)
  body: Quotient.ind norm_sq_eq_re_inner
  conj_inner_symm := Quotient.ind₂ inner_conj_symm
add_left := Quotient.ind fun x => Quotient.ind₂ inner_add_left x
  smul_left := Quotient.ind₂ inner_smul_left

中文:
实例 :
  签名: 内积空间 𝕜 (SeparationQuotient E)
  定义体: Quotient.ind norm_sq_eq_re_inner
  conj_inner_symm := Quotient.ind₂ inner_conj_symm
add_left := Quotient.ind fun x => Quotient.ind₂ inner_add_left x
  smul_left := Quotient.ind₂ inner_smul_left

Depends on / 依赖: Quotient, Quotient.ind, norm_sq_eq_re_inner
-/
instance : InnerProductSpace 𝕜 (SeparationQuotient E) where
  norm_sq_eq_re_inner := Quotient.ind norm_sq_eq_re_inner
  conj_inner_symm := Quotient.ind₂ inner_conj_symm
add_left := Quotient.ind fun x => Quotient.ind₂ inner_add_left x
  smul_left := Quotient.ind₂ inner_smul_left

end SeparationQuotient

end SeparationQuotient

section UniformSpace.Completion

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace UniformSpace.Completion

open RCLike Function

/--
Instance `toInner` / 实例 `toInner`

English:
instance toInner
  signature: {𝕜' E' : Type*} [TopologicalSpace 𝕜'] [UniformSpace E'] [Inner 𝕜' E']
  body: curry (isDenseInducing_coe.prodMap isDenseInducing_coe).extend (uncurry (inner 𝕜'))

@[simp]

中文:
实例 toInner
  签名: {𝕜' E' : 类型} [拓扑空间 𝕜'] [一致空间 E'] [内积 𝕜' E']
  定义体: curry (isDenseInducing_coe.prodMap isDenseInducing_coe).extend (uncurry (inner 𝕜'))

@[simp]

Depends on / 依赖: extend, isDenseInducing_coe, isDenseInducing_coe.prodMap, prodMap, uncurry
-/
instance toInner {𝕜' E' : Type*} [TopologicalSpace 𝕜'] [UniformSpace E'] [Inner 𝕜' E'] :
    Inner 𝕜' (Completion E') where
inner := curry (isDenseInducing_coe.prodMap isDenseInducing_coe).extend (uncurry (inner 𝕜'))

@[simp]
/--
theorem `inner_coe` / 定理 `inner_coe`

English:
theorem inner_coe
  given: (a b : E)
  statement: ⟪(a : Completion E), (b : Completion E)⟫ = ⟪a, b⟫
  proof: (isDenseInducing_coe.prodMap isDenseInducing_coe).extend_eq
    (continuous_inner : Continuous (uncurry (inner 𝕜))) (a, b)

中文:
定理 inner_coe
  条件: (a b : E)
  结论: ⟪(a : 完备化 E), (b : 完备化 E)⟫ = ⟪a, b⟫
  证明: (isDenseInducing_coe.prodMap isDenseInducing_coe).extend_eq
    (continuous_inner : Continuous (uncurry (inner 𝕜))) (a, b)

Depends on / 依赖: Continuous, continuous_inner, extend_eq, isDenseInducing_coe, isDenseInducing_coe.prodMap, prodMap, uncurry
-/
theorem inner_coe (a b : E) : ⟪(a : Completion E), (b : Completion E)⟫ = ⟪a, b⟫ :=
  (isDenseInducing_coe.prodMap isDenseInducing_coe).extend_eq
    (continuous_inner : Continuous (uncurry (inner 𝕜))) (a, b)

/--
theorem `continuous_inner` / 定理 `continuous_inner`

English:
theorem continuous_inner
  proof: by
  let inner' : E ->+ E ->+ 𝕜 :=
    { toFun := fun x => (innerₛₗ 𝕜 x).toAddMonoidHom
      map_zero' := by ext x; exact inner_zero_left _
      map_add' := fun x y => by ext z; exact inner_add_left _ _ _ }
  have : Continuous fun p : E × E => inner' p.1 p.2 := continuous_inner
  rw [Completion.toInner]; rw [inner]; rw [uncurry_curry _]
  change
    Continuous
      (((isDenseInducing_toCompl E).prodMap (isDenseInducing_toCompl E)).extend fun p : E × E =>
        inner' p.1 p.2)
  exact (isDenseInducing_toCompl E).extend_Z_bilin (isDenseInducing_toCompl E) this

@[fun_prop]

中文:
定理 continuous_inner
  证明: by
  let inner' : E ->+ E ->+ 𝕜 :=
    { toFun := fun x => (innerₛₗ 𝕜 x).toAddMonoidHom
      map_zero' := by ext x; exact inner_zero_left _
      map_add' := fun x y => by ext z; exact inner_add_left _ _ _ }
  have : Continuous fun p : E × E => inner' p.1 p.2 := continuous_inner
  rw [Completion.toInner]; rw [inner]; rw [uncurry_curry _]
  change
    Continuous
      (((isDenseInducing_toCompl E).prodMap (isDenseInducing_toCompl E)).extend fun p : E × E =>
        inner' p.1 p.2)
  exact (isDenseInducing_toCompl E).extend_Z_bilin (isDenseInducing_toCompl E) this

@[fun_prop]
-/
protected theorem continuous_inner :
    Continuous (uncurry (inner 𝕜 (E := Completion E))) := by
  let inner' : E ->+ E ->+ 𝕜 :=
    { toFun := fun x => (innerₛₗ 𝕜 x).toAddMonoidHom
      map_zero' := by ext x; exact inner_zero_left _
      map_add' := fun x y => by ext z; exact inner_add_left _ _ _ }
  have : Continuous fun p : E × E => inner' p.1 p.2 := continuous_inner
  rw [Completion.toInner]; rw [inner]; rw [uncurry_curry _]
  change
    Continuous
      (((isDenseInducing_toCompl E).prodMap (isDenseInducing_toCompl E)).extend fun p : E × E =>
        inner' p.1 p.2)
  exact (isDenseInducing_toCompl E).extend_Z_bilin (isDenseInducing_toCompl E) this

@[fun_prop]
/--
theorem `Continuous.inner` / 定理 `Continuous.inner`

English:
theorem Continuous.inner
  statement: {α : Type*} [TopologicalSpace α] {f g : α -> Completion E}
  proof: UniformSpace.Completion.continuous_inner.comp (hf.prodMk hg :)

中文:
定理 连续.inner
  结论: {α : 类型} [拓扑空间 α] {f g : α -> 完备化 E}
  证明: UniformSpace.Completion.continuous_inner.comp (hf.prodMk hg :)
-/
protected theorem Continuous.inner {α : Type*} [TopologicalSpace α] {f g : α -> Completion E}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x : α => ⟪f x, g x⟫) :=
  UniformSpace.Completion.continuous_inner.comp (hf.prodMk hg :)

/--
Instance `innerProductSpace` / 实例 `innerProductSpace`

English:
instance innerProductSpace
  signature: : InnerProductSpace 𝕜 (Completion E) where
  body: Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop))
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

中文:
实例 innerProductSpace
  签名: : 内积空间 𝕜 (完备化 E) where
  定义体: Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop))
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

Depends on / 依赖: Completion, Completion.induction, Completion.induction_on, add_left, coe_add, conj_inner_symm, continuous_conj, continuous_conj.comp, fun_prop, induction_on, inner_add_left, inner_coe, inner_conj_symm, inner_self_eq_norm_sq, isClosed_eq, norm_coe, smul_left
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
