/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.PartialHomeomorph.Defs

/-!
# Partial homeomorphisms: basic theory


## Main definitions

* `PartialHomeomorph.refl`: the identity partial homeomorphism
* `IsEmbedding.toPartialHomeomorph`: an embedding of `X` into `Y`, with `X` nonempty,
  defines a partial homeomorphism whose source is all of `X`.
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace PartialHomeomorph

/-- The identity on the whole space as a partial homeomorphism. -/
@[simps! -fullyApplied apply, simps! -isSimp source target]
/-
**PartialHomeomorph.refl** 是 Mathlib 中的一个定义，位于命名空间 `PartialHomeomorph`。
形式化陈述：(X : Type u_7) → [inst : TopologicalSpace X] → PartialHomeomorph X X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity on the whole space as a partial homeomorphism.
-/
protected def refl (X : Type*) [TopologicalSpace X] : PartialHomeomorph X X :=
  (Homeomorph.refl X).toPartialHomeomorph

@[simp]
/-
**PartialHomeomorph.refl_partialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomor
ph`。
形式化陈述：refl_partialEquiv : (PartialHomeomorph.refl X).toPartialEquiv = PartialEqu
iv.refl X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_partialEquiv : (PartialHomeomorph.refl X).toPartialEquiv = PartialEquiv.refl X :=
  rfl

@[simp]
/-
**PartialHomeomorph.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：refl_symm : (PartialHomeomorph.refl X).symm = PartialHomeomorph.refl X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (PartialHomeomorph.refl X).symm = PartialHomeomorph.refl X :=
  rfl

variable (e : PartialHomeomorph X Y)
/-
**PartialHomeomorph.source_preimage_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialHom
eomorph`。
形式化陈述：source_preimage_target : e.source subseteq e ⁻¹' e.target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (e : PartialHomeomorph X Y),   Set.M
apsTo (↑e) e.s…
-/
theorem source_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.mapsTo
/-
**PartialHomeomorph.image_eq_target_inter_inv_preimage** 是 Mathlib 中的一个定理，位于命名空间
 `PartialHomeomorph`。
形式化陈述：image_eq_target_inter_inv_preimage {s : Set X} (h : s subseteq e.source) :
 e '' s = e.target inter e.symm ⁻¹' s
参数：h : s subseteq e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_eq_target_inter_inv_preimage`：image_eq_target_inter_i
nv_preimage {s : Set α} (h : s subseteq e.source) : e '' s = e.target inter e.sy
mm ⁻¹' s
-/
theorem image_eq_target_inter_inv_preimage {s : Set X} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_eq_target_inter_inv_preimage h
/-
**PartialHomeomorph.image_source_inter_eq'** 是 Mathlib 中的一个定理，位于命名空间 `PartialHom
eomorph`。
形式化陈述：image_source_inter_eq' (s : Set X) : e '' (e.source inter s) = e.target in
ter e.symm ⁻¹' s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_source_inter_eq'`：image_source_inter_eq' (s : Set α) 
: e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
-/
theorem image_source_inter_eq' (s : Set X) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_source_inter_eq' s
/-
**PartialHomeomorph.image_source_inter_eq** 是 Mathlib 中的一个定理，位于命名空间 `PartialHome
omorph`。
形式化陈述：image_source_inter_eq (s : Set X) : e '' (e.source inter s) = e.target int
er e.symm ⁻¹' (e.source inter s)
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_source_inter_eq`：image_source_inter_eq (s : Set α) : 
e '' (e.source inter s) = e.target inter e.symm ⁻¹' (e.source inter s)
-/
theorem image_source_inter_eq (s : Set X) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) :=
  e.toPartialEquiv.image_source_inter_eq s
/-
**PartialHomeomorph.symm_image_eq_source_inter_preimage** 是 Mathlib 中的一个定理，位于命名空
间 `PartialHomeomorph`。
形式化陈述：symm_image_eq_source_inter_preimage {s : Set Y} (h : s subseteq e.target) 
: e.symm '' s = e.source inter e ⁻¹' s
参数：h : s subseteq e.target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.image_eq_target_inter_inv_preimage`：image_eq_target_in
ter_inv_preimage {s : Set X} (h : s subseteq e.source) : e '' s = e.target inter
 e.symm ⁻¹' s
-/
theorem symm_image_eq_source_inter_preimage {s : Set Y} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h
/-
**PartialHomeomorph.symm_image_target_inter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Partia
lHomeomorph`。
形式化陈述：symm_image_target_inter_eq (s : Set Y) : e.symm '' (e.target inter s) = e.
source inter e ⁻¹' (e.target inter s)
参数：s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.image_source_inter_eq`：image_source_inter_eq (s : Set 
X) : e '' (e.source inter s) = e.target inter e.symm ⁻¹' (e.source inter s)
-/
theorem symm_image_target_inter_eq (s : Set Y) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _
/-
**PartialHomeomorph.source_inter_preimage_inv_preimage** 是 Mathlib 中的一个定理，位于命名空间
 `PartialHomeomorph`。
形式化陈述：source_inter_preimage_inv_preimage (s : Set X) : e.source inter e ⁻¹' (e.s
ymm ⁻¹' s) = e.source inter s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.source_inter_preimage_inv_preimage`：source_inter_preimage_i
nv_preimage (s : Set α) : e.source inter e ⁻¹' e.symm ⁻¹' s = e.source inter s
-/
theorem source_inter_preimage_inv_preimage (s : Set X) :
    e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
  e.toPartialEquiv.source_inter_preimage_inv_preimage s
/-
**PartialHomeomorph.target_inter_inv_preimage_preimage** 是 Mathlib 中的一个定理，位于命名空间
 `PartialHomeomorph`。
形式化陈述：target_inter_inv_preimage_preimage (s : Set Y) : e.target inter e.symm ⁻¹'
 (e ⁻¹' s) = e.target inter s
参数：s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.source_inter_preimage_inv_preimage`：source_inter_preim
age_inv_preimage (s : Set X) : e.source inter e ⁻¹' (e.symm ⁻¹' s) = e.source in
ter s
-/
theorem target_inter_inv_preimage_preimage (s : Set Y) :
    e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _
/-
**PartialHomeomorph.source_inter_preimage_target_inter** 是 Mathlib 中的一个定理，位于命名空间
 `PartialHomeomorph`。
形式化陈述：source_inter_preimage_target_inter (s : Set Y) : e.source inter e ⁻¹' (e.t
arget inter s) = e.source inter e ⁻¹' s
参数：s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.source_inter_preimage_target_inter`：source_inter_preimage_t
arget_inter (s : Set β) : e.source inter e ⁻¹' (e.target inter s) = e.source int
er e ⁻¹' s
-/
theorem source_inter_preimage_target_inter (s : Set Y) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.toPartialEquiv.source_inter_preimage_target_inter s
/-
**PartialHomeomorph.image_source_eq_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialHom
eomorph`。
形式化陈述：image_source_eq_target : e '' e.source = e.target
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
-/
theorem image_source_eq_target : e '' e.source = e.target :=
  e.toPartialEquiv.image_source_eq_target
/-
**PartialHomeomorph.symm_image_target_eq_source** 是 Mathlib 中的一个定理，位于命名空间 `Parti
alHomeomorph`。
形式化陈述：symm_image_target_eq_source : e.symm '' e.target = e.source
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.image_source_eq_target`：image_source_eq_target : e '' 
e.source = e.target
-/
theorem symm_image_target_eq_source : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target

/-- A `PartialEquiv` which is continuous on its source and has open forward map (on its source) is a
`PartialHomeomorph`. -/
@[simps toPartialEquiv]
/-
**PartialHomeomorph.ofContinuousOpenRestrict** 是 Mathlib 中的一个定义，位于命名空间 `PartialH
omeomorph`。
形式化陈述：ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.sou
rce) (ho : IsOpenMap (e.source.domRestrict e)) : PartialHomeomorph X Y where toP
artialEquiv
参数：e : PartialEquiv X Y；hc : ContinuousOn e e.source；ho : IsOpenMap (e.source.do
mRestrict e)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PartialEquiv` which is continuous on its source and has open forward map (on 
its source) is a
`PartialHomeomorph`.
-/
def ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.domRestrict e)) : PartialHomeomorph X Y where
  toPartialEquiv := e
  continuousOn_toFun := hc
  continuousOn_invFun := e.image_source_eq_target ▸ ho.continuousOn_image_of_leftInvOn e.leftInvOn

@[simp]
/-
**PartialHomeomorph.coe_ofContinuousOpenRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Part
ialHomeomorph`。
形式化陈述：coe_ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e
.source) (ho : IsOpenMap (e.source.domRestrict e)) : ⇑(ofContinuousOpenRestrict 
e hc ho) = e
参数：e : PartialEquiv X Y；hc : ContinuousOn e e.source；ho : IsOpenMap (e.source.do
mRestrict e)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.domRestrict e)) : ⇑(ofContinuousOpenRestrict e hc ho) = e :=
  rfl

@[simp]
/-
**PartialHomeomorph.coe_ofContinuousOpenRestrict_symm** 是 Mathlib 中的一个定理，位于命名空间 
`PartialHomeomorph`。
形式化陈述：coe_ofContinuousOpenRestrict_symm (e : PartialEquiv X Y) (hc : ContinuousO
n e e.source) (ho : IsOpenMap (e.source.domRestrict e)) : ⇑(ofContinuousOpenRest
rict e hc ho).symm = e.symm
参数：e : PartialEquiv X Y；hc : ContinuousOn e e.source；ho : IsOpenMap (e.source.do
mRestrict e)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofContinuousOpenRestrict_symm (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.domRestrict e)) :
    ⇑(ofContinuousOpenRestrict e hc ho).symm = e.symm :=
  rfl

/-- A `PartialEquiv` which is continuous on its source and has open forward map (on its source) and
open source is a `PartialHomeomorph`. -/
@[simps! toPartialEquiv]
/-
**PartialHomeomorph.ofContinuousOpen** 是 Mathlib 中的一个定义，位于命名空间 `PartialHomeomorp
h`。
形式化陈述：ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source) (ho
 : IsOpenMap e) (hs : IsOpen e.source) : PartialHomeomorph X Y
参数：e : PartialEquiv X Y；hc : ContinuousOn e e.source；ho : IsOpenMap e；hs : IsOpe
n e.source。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PartialEquiv` which is continuous on its source and has open forward map (on 
its source) and
open source is a `PartialHomeomorph`.
-/
def ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
    (hs : IsOpen e.source) : PartialHomeomorph X Y :=
  ofContinuousOpenRestrict e hc (ho.domRestrict hs)

@[simp]
/-
**PartialHomeomorph.coe_ofContinuousOpen** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeo
morph`。
形式化陈述：coe_ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
 (ho : IsOpenMap e) (hs : IsOpen e.source) : ⇑(ofContinuousOpen e hc ho hs) = e
参数：e : PartialEquiv X Y；hc : ContinuousOn e e.source；ho : IsOpenMap e；hs : IsOpe
n e.source。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap e) (hs : IsOpen e.source) :
    ⇑(ofContinuousOpen e hc ho hs) = e :=
  rfl

@[simp]
/-
**PartialHomeomorph.coe_ofContinuousOpen_symm** 是 Mathlib 中的一个定理，位于命名空间 `Partial
Homeomorph`。
形式化陈述：coe_ofContinuousOpen_symm (e : PartialEquiv X Y) (hc : ContinuousOn e e.so
urce) (ho : IsOpenMap e) (hs : IsOpen e.source) : ⇑(ofContinuousOpen e hc ho hs)
.symm = e.symm
参数：e : PartialEquiv X Y；hc : ContinuousOn e e.source；ho : IsOpenMap e；hs : IsOpe
n e.source。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofContinuousOpen_symm (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap e) (hs : IsOpen e.source) :
    ⇑(ofContinuousOpen e hc ho hs).symm = e.symm :=
  rfl

/-- The homeomorphism obtained by restricting a `PartialHomeomorph` to a subset of the source.
-/
@[simps]
/-
**PartialHomeomorph.homeomorphOfImageSubsetSource** 是 Mathlib 中的一个定义，位于命名空间 `Par
tialHomeomorph`。
形式化陈述：homeomorphOfImageSubsetSource {s : Set X} {t : Set Y} (hs : s subseteq e.s
ource) (ht : e '' s = t) : s ≃ₜ t
参数：hs : s subseteq e.source；ht : e '' s = t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homeomorphism obtained by restricting a `PartialHomeomorph` to a subset of t
he source.
-/
def homeomorphOfImageSubsetSource {s : Set X} {t : Set Y} (hs : s ⊆ e.source) (ht : e '' s = t) :
    s ≃ₜ t :=
  have h₁ : MapsTo e s t := mapsTo_iff_image_subset.2 ht.subset
  have h₂ : t ⊆ e.target := ht ▸ e.image_source_eq_target ▸ image_mono hs
  have h₃ : MapsTo e.symm t s := ht ▸ forall_mem_image.2 fun _x hx =>
      (e.left_inv (hs hx)).symm ▸ hx
  { toFun := MapsTo.restrict e s t h₁
    invFun := MapsTo.restrict e.symm t s h₃
    left_inv := fun a => Subtype.ext (e.left_inv (hs a.2))
    right_inv := fun b => Subtype.ext <| e.right_inv (h₂ b.2)
    continuous_toFun := (e.continuousOn.mono hs).mapsToRestrict h₁
    continuous_invFun := (e.continuousOn_symm.mono h₂).mapsToRestrict h₃ }

/-- A partial homeomorphism defines a homeomorphism between its source and target. -/
@[simps!]
/-
**PartialHomeomorph.toHomeomorphSourceTarget** 是 Mathlib 中的一个定义，位于命名空间 `PartialH
omeomorph`。
形式化陈述：toHomeomorphSourceTarget : e.source ≃ₜ e.target
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.image_source_eq_target`：image_source_eq_target : e '' 
e.source = e.target

--- 原说明 ---
A partial homeomorphism defines a homeomorphism between its source and target.
-/
def toHomeomorphSourceTarget : e.source ≃ₜ e.target :=
  e.homeomorphOfImageSubsetSource subset_rfl e.image_source_eq_target
/-
**PartialHomeomorph.secondCountableTopology_source** 是 Mathlib 中的一个定理，位于命名空间 `Pa
rtialHomeomorph`。
形式化陈述：secondCountableTopology_source [SecondCountableTopology Y] : SecondCountab
leTopology e.source
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.secondCountableTopology`：∀ {X : Type u_1} {Y : Type u_2} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [SecondCountableTopology Y
]   (h : X ≃ₜ Y), Second…
· 使用定理 `TopologicalSpace.Subtype.secondCountableTopology`：∀ {α : Type u} [t : To
pologicalSpace α] (s : Set α) [SecondCountableTopology α], SecondCountableTopolo
gy ↑s
-/
theorem secondCountableTopology_source [SecondCountableTopology Y] :
    SecondCountableTopology e.source :=
  e.toHomeomorphSourceTarget.secondCountableTopology

/-- If a partial homeomorphism has source and target equal to univ, then it induces a
homeomorphism between the whole spaces, expressed in this definition. -/
@[simps -fullyApplied apply symm_apply]
-- TODO: add a `PartialEquiv` version
/-
**PartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv** 是 Mathlib 中的一个定义，位于
命名空间 `PartialHomeomorph`。
形式化陈述：toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.source = (univ : Set X)) (h'
 : e.target = univ) : X ≃ₜ Y where toFun
参数：h : e.source = (univ : Set X)；h' : e.target = univ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.source = (univ : Set X)) (h' : e.target = univ) :
    X ≃ₜ Y where
  toFun := e
  invFun := e.symm
  left_inv x :=
    e.left_inv <| by
      rw [h]
      exact mem_univ _
  right_inv x :=
    e.right_inv <| by
      rw [h']
      exact mem_univ _
  continuous_toFun := by
    simpa only [continuousOn_univ, h] using e.continuousOn
  continuous_invFun := by
    simpa only [continuousOn_univ, h'] using e.continuousOn_symm
/-
**PartialHomeomorph.isEmbedding_restrict** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeo
morph`。
形式化陈述：isEmbedding_restrict : IsEmbedding (e.source.domRestrict e.toFun)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.isEmbedding_iff`：∀ {X : Type u_1} {Y : Type u_2} [tX : Topologi
calSpace X] [tY : TopologicalSpace Y] (f : X → Y),   Topology.IsEmbedding f ↔ To
pology.IsInduc…
· 使用引理 `Topology.IsInducing.of_codRestrict`：Topology.IsInducing.of_codRestrict {
f : X -> Y} {t : Set Y} (ht : forall x, f x in t) (h : IsInducing (t.codRestrict
 f ht)) : IsInducing f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PartialEquiv.toEquiv_eq_codRestrict_restrict`：toEquiv_eq_codRestrict_res
trict : e.toEquiv = codRestrict (e.source.domRestrict e) e.target (by simp)
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
· 使用定理 `Set.domRestrict_eq`：domRestrict_eq (f : α -> β) (s : Set α) : s.domRestr
ict f = f ∘ Subtype.val
· 使用定理 `PartialHomeomorph.toFun_eq_coe`：toFun_eq_coe (e : PartialHomeomorph X Y)
 : e.toFun = e
· 使用定理 `Set.InjOn.injective_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : α → β} {g : β → γ} (s : Set β),   Set.InjOn g s → Set.range f ⊆ s → (Functi
on.Injective …
· 使用定理 `PartialHomeomorph.injOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (e : PartialHomeomorph X Y),   Set.In
jOn (↑e) e.so…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem isEmbedding_restrict : IsEmbedding (e.source.domRestrict e.toFun) := by
  rw [isEmbedding_iff]
  constructor
  · apply Topology.IsInducing.of_codRestrict (t := e.target) (by simp)
    rw [← PartialEquiv.toEquiv_eq_codRestrict_restrict]
    exact e.toHomeomorphSourceTarget.isInducing
  · rw [domRestrict_eq, toFun_eq_coe e, e.injOn.injective_iff e.source (by simp)]
    exact Subtype.val_injective

/-- A partial homeomorphism whose source is all of `X` defines an embedding of `X` into
`Y`. The converse is also true; see `IsEmbedding.toPartialHomeomorph`. -/
/-
**PartialHomeomorph.isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `PartialHomeomorph`。
形式化陈述：isEmbedding (h : e.source = Set.univ) : IsEmbedding e
参数：h : e.source = Set.univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `PartialHomeomorph.isEmbedding_restrict`：isEmbedding_restrict : IsEmbeddi
ng (e.source.domRestrict e.toFun)
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h

--- 原说明 ---
A partial homeomorphism whose source is all of `X` defines an embedding of `X` i
nto
`Y`. The converse is also true; see `IsEmbedding.toPartialHomeomorph`.
-/
theorem isEmbedding (h : e.source = Set.univ) : IsEmbedding e :=
  e.isEmbedding_restrict.comp
    ((Homeomorph.setCongr h).trans <| Homeomorph.Set.univ X).symm.isEmbedding

/-- If a `PartialEquiv` is a homeomorphism when restricted to source and target, then it is a
`PartialHomeomorph`. -/
/-
**PartialHomeomorph.ofIsHomeomorphToEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PartialHome
omorph`。
形式化陈述：ofIsHomeomorphToEquiv (f : PartialEquiv X Y) (h : IsHomeomorph (f.toEquiv)
) : PartialHomeomorph X Y where toPartialEquiv
参数：f : PartialEquiv X Y；h : IsHomeomorph (f.toEquiv)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `PartialEquiv` is a homeomorphism when restricted to source and target, the
n it is a
`PartialHomeomorph`.
-/
def ofIsHomeomorphToEquiv (f : PartialEquiv X Y) (h : IsHomeomorph (f.toEquiv)) :
    PartialHomeomorph X Y where
  toPartialEquiv := f
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict,
      ← continuous_codRestrict_iff (s := f.target) (by simp)]
    exact h.continuous
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict,
      ← continuous_codRestrict_iff (s := f.source) (by simp)]
    exact ((Equiv.isHomeomorph_iff _).1 h).2

end PartialHomeomorph

/-!
## Embeddings
-/

namespace Topology.IsEmbedding

variable (f : X → Y) (h : IsEmbedding f)

/-- An embedding of `X` into `Y`, with `X` nonempty, defines a partial homeomorphism
whose source is all of `X`. The converse is also true; see `PartialHomeomorph.isEmbedding`. -/
@[simps! -fullyApplied apply source target]
/-
**Topology.IsEmbedding.toPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Topology.I
sEmbedding`。
形式化陈述：toPartialHomeomorph [Nonempty X] : PartialHomeomorph X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An embedding of `X` into `Y`, with `X` nonempty, defines a partial homeomorphism
whose source is all of `X`. The converse is also true; see `PartialHomeomorph.is
Embedding`.
-/
noncomputable def toPartialHomeomorph [Nonempty X] : PartialHomeomorph X Y :=
  PartialHomeomorph.ofIsHomeomorphToEquiv (h.injective.injOn.toPartialEquiv f univ) (by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    refine ⟨?_, Equiv.surjective _⟩
    rw [PartialEquiv.toEquiv_eq_codRestrict_restrict]
    apply IsEmbedding.codRestrict
    simpa! [domRestrict_eq] using h.comp subtypeVal)

variable [Nonempty X]
/-
**Topology.IsEmbedding.toPartialHomeomorph_left_inv** 是 Mathlib 中的一个引理，位于命名空间 `T
opology.IsEmbedding`。
形式化陈述：toPartialHomeomorph_left_inv {x : X} : (h.toPartialHomeomorph f).symm (f x
) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Topology.IsEmbedding.toPartialHomeomorph_apply`：∀ {X : Type u_1} {Y : Ty
pe u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y)   
(h : Topology.IsEmbedding f) [inst_2…
· 使用定理 `PartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e.sym
m (e x) = x
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
lemma toPartialHomeomorph_left_inv {x : X} : (h.toPartialHomeomorph f).symm (f x) = x := by
  rw [← congr_fun (h.toPartialHomeomorph_apply f), PartialHomeomorph.left_inv]
  exact Set.mem_univ _
/-
**Topology.IsEmbedding.toPartialHomeomorph_right_inv** 是 Mathlib 中的一个引理，位于命名空间 `
Topology.IsEmbedding`。
形式化陈述：toPartialHomeomorph_right_inv {x : Y} (hx : x in Set.range f) : f ((h.toPa
rtialHomeomorph f).symm x) = x
参数：hx : x in Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Topology.IsEmbedding.toPartialHomeomorph_apply`：∀ {X : Type u_1} {Y : Ty
pe u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y)   
(h : Topology.IsEmbedding f) [inst_2…
· 使用定理 `PartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) : e (
e.symm x) = x
· 使用定理 `Topology.IsEmbedding.toPartialHomeomorph_target`：∀ {X : Type u_1} {Y : T
ype u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y)  
 (h : Topology.IsEmbedding f) [inst_2…
-/
lemma toPartialHomeomorph_right_inv {x : Y} (hx : x ∈ Set.range f) :
    f ((h.toPartialHomeomorph f).symm x) = x := by
  rw [← congr_fun (h.toPartialHomeomorph_apply f), PartialHomeomorph.right_inv]
  rwa [toPartialHomeomorph_target]

end Topology.IsEmbedding

/-! inclusion of a set in a topological space -/
namespace Set

/- `Nonempty s` is not a type class argument because `s`, being a subset, rarely comes with a type
class instance. Then we'd have to manually provide the instance every time we use the following
lemmas, tediously using `haveI := ...` or `@foobar _ _ _ ...`. -/
variable (s : Set X) (hs : Nonempty s)

/-- The inclusion of an subset `s` of a space `X` into `X` is a partial homeomorphism
from the subtype `s` to `X`. -/
/-
**Set.partialHomeomorphSubtypeCoe** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：partialHomeomorphSubtypeCoe : PartialHomeomorph s X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of an subset `s` of a space `X` into `X` is a partial homeomorphis
m
from the subtype `s` to `X`.
-/
noncomputable def partialHomeomorphSubtypeCoe : PartialHomeomorph s X :=
  IsEmbedding.subtypeVal.toPartialHomeomorph _

@[simp]
/-
**Set.partialHomeomorphSubtypeCoe_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：partialHomeomorphSubtypeCoe_coe : (s.partialHomeomorphSubtypeCoe hs : s ->
 X) = (↑)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem partialHomeomorphSubtypeCoe_coe :
    (s.partialHomeomorphSubtypeCoe hs : s → X) = (↑) :=
  rfl

@[simp]
/-
**Set.partialHomeomorphSubtypeCoe_source** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：partialHomeomorphSubtypeCoe_source : (s.partialHomeomorphSubtypeCoe hs).so
urce = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem partialHomeomorphSubtypeCoe_source :
    (s.partialHomeomorphSubtypeCoe hs).source = Set.univ :=
  rfl

@[simp]
/-
**Set.partialHomeomorphSubtypeCoe_target** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：partialHomeomorphSubtypeCoe_target : (s.partialHomeomorphSubtypeCoe hs).ta
rget = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsEmbedding.toPartialHomeomorph_target`：∀ {X : Type u_1} {Y : T
ype u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y)  
 (h : Topology.IsEmbedding f) [inst_2…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem partialHomeomorphSubtypeCoe_target :
    (s.partialHomeomorphSubtypeCoe hs).target = s := by
  simp [partialHomeomorphSubtypeCoe]

end Set

