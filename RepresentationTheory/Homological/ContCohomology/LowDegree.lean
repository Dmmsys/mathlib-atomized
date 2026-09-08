/-
Copyright (c) 2026 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill, Andrew Yang, Edison Xie
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
## Low degree continuous cohomology

In this file we show that the zeroth continuous cohomology is isomorphic to the
invariants of the representation.
-/

@[expose] public section

namespace ContinuousCohomology

open CategoryTheory Functor TopRep ContRepresentation

variable {k G : Type*} [Ring k] [Group G] [TopologicalSpace k]
  [TopologicalSpace G] [IsTopologicalGroup G]

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

variable (X : TopRep k G)

/-
**ContinuousCohomology.cocycles** 是 Mathlib 中的一个缩写定义，位于命名空间 `ContinuousCohomolog
y`。
形式化陈述：cocycles (A : TopRep k G) (n : Nat) : TopModuleCat k
参数：A : TopRep k G；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cocycles₀IsoAux (σ : (homogeneousCochains X).X 0)
    (hσ : σ ∈ ((homogeneousCochains X).d 0 1).hom.ker) : σ.1 1 ∈ X.ρ.invariants := by
  simp only [Nat.reduceAdd, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Subtype.ext_iff, homogeneousCochains.d_apply _] at hσ
  simp only [mem_invariants]
  intro g
  rw [d_succ, hom_sub, hom_ofHom, ContIntertwiningMap.sub_apply, d_zero,
    ZeroMemClass.coe_zero, sub_eq_zero] at hσ
  replace hσ := DFunLike.ext_iff.1 (DFunLike.ext_iff.1 hσ 1) g⁻¹
  simp only [Nat.reduceAdd, coind₁ι_toFun, ContinuousMap.const_apply, ConcreteCategory.hom_ofHom,
    coind₁Map_toFun, ContinuousMap.comp_apply, ContinuousMap.coe_mk] at hσ
  simpa [hσ] using DFunLike.ext_iff.1 (σ.2 g) 1
/-
**ContinuousCohomology.mem_const_resol** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousCoho
mology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mem_const_resol₀ (x : X) (hx : x ∈ X.ρ.invariants) :
    ContinuousMap.const G x ∈ ((resolution' X).X 0).ρ.invariants :=
  ContRepresentation.mem_invariants _|>.1 fun _ ↦ ContinuousMap.ext fun _ ↦ hx _
/-
**ContinuousCohomology.cocycles** 是 Mathlib 中的一个缩写定义，位于命名空间 `ContinuousCohomolog
y`。
形式化陈述：cocycles (A : TopRep k G) (n : Nat) : TopModuleCat k
参数：A : TopRep k G；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cocycles₀IsoAux' (x : X) (h : ContinuousMap.const G x ∈ ((resolution' X).X 0).ρ.invariants) :
    ⟨ContinuousMap.const G x, h⟩ ∈ ((homogeneousCochains X).d 0 1).hom.ker := by
  rw [LinearMap.mem_ker, Subtype.ext_iff, ContinuousLinearMap.coe_coe,
    homogeneousCochains.d_apply]
  simp [d_succ, hom_sub, ContIntertwiningMap.sub_apply, d_zero]

/-- The isomorphism between the zeroth cocycles and the kernel of the zeroth differential. -/
/-
**ContinuousCohomology.cocycles** 是 Mathlib 中的一个缩写定义，位于命名空间 `ContinuousCohomolog
y`。
形式化陈述：cocycles (A : TopRep k G) (n : Nat) : TopModuleCat k
参数：A : TopRep k G；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between the zeroth cocycles and the kernel of the zeroth differe
ntial.
-/
noncomputable abbrev cocycles₀Iso : cocycles X 0 ≅
    TopModuleCat.of k ((homogeneousCochains X).d 0 1).hom.ker :=
  Limits.KernelFork.mapIsoOfIsLimit ((homogeneousCochains X).cyclesIsKernel 0 1 (by simp))
    (TopModuleCat.isLimitKer _) (Iso.refl _)

/-- The isomorphism between the kernel of the zeroth differential and
the invariants of a representation. -/
/-
**ContinuousCohomology.d** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between the kernel of the zeroth differential and
the invariants of a representation.
-/
def d₀kerIso : ((homogeneousCochains X).d 0 1).hom.ker ≃L[k] X.ρ.invariants where
  toFun := fun ⟨σ, hσ⟩ ↦ ⟨σ.val 1, cocycles₀IsoAux X σ hσ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := fun ⟨x, hx⟩ ↦ ⟨⟨ContinuousMap.const G x, mem_const_resol₀ X x hx⟩,
    cocycles₀IsoAux' X x (mem_const_resol₀ X x hx)⟩
  left_inv := fun ⟨⟨(x : C(G, X)), hx'⟩, hx⟩ ↦ by
    ext g
    rw [LinearMap.mem_ker, Subtype.ext_iff, ContinuousLinearMap.coe_coe,
      homogeneousCochains.d_apply] at hx
    simp only [Nat.reduceAdd, d_succ, d_zero, ConcreteCategory.hom_ofHom, hom_sub,
      ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun, ZeroMemClass.coe_zero,
      sub_eq_zero, ContinuousMap.const_apply] at hx ⊢
    simpa using DFunLike.ext_iff.1 (DFunLike.ext_iff.1 hx g) 1
  right_inv _ := rfl
  continuous_toFun := continuous_induced_rng.2 <| (continuous_eval_const 1).comp <|
    (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := continuous_induced_rng.2 <| continuous_induced_rng.2 <|
    ContinuousMap.continuous_const'.comp continuous_subtype_val

/-- The isomorphism between the zeroth continuous cohomology group and
the invariants of a representation. -/
/-
**ContinuousCohomology.zeroIso** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousCohomology`。
形式化陈述：zeroIso (A : TopRep k G) : continuousCohomology 0 A ≅ TopModuleCat.of k A.
ρ.invariants
参数：A : TopRep k G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between the zeroth continuous cohomology group and
the invariants of a representation.
-/
noncomputable def zeroIso (A : TopRep k G) :
    continuousCohomology 0 A ≅ TopModuleCat.of k A.ρ.invariants :=
  (homogeneousCochains A).isoHomologyπ₀.symm ≪≫ cocycles₀Iso A ≪≫
    TopModuleCat.ofIso (d₀kerIso A)

end ContinuousCohomology

