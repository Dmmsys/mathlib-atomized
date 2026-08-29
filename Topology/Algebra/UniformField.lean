/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.UniformRing

/-!
# Completion of topological fields

The goal of this file is to prove the main part of Proposition 7 of Bourbaki GT III 6.8 :

The completion `hat K` of a Hausdorff topological field is a field if the image under
the mapping `x ↦ x⁻¹` of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at `0` is a Cauchy filter
(with respect to the additive uniform structure).

Bourbaki does not give any detail here, he refers to the general discussion of extending
functions defined on a dense subset with values in a complete Hausdorff space. In particular
the subtlety about clustering at zero is totally left to readers.

Note that the separated completion of a non-separated topological field is the zero ring, hence
the separation assumption is needed. Indeed the kernel of the completion map is the closure of
zero which is an ideal. Hence it's either zero (and the field is separated) or the full field,
which implies one is sent to zero and the completion ring is trivial.

The main definition is `CompletableTopField` which packages the assumptions as a Prop-valued
type class and the main results are the instances `UniformSpace.Completion.Field` and
`UniformSpace.Completion.IsTopologicalDivisionRing`.
-/

@[expose] public section

noncomputable section

open uniformity Topology

open Set UniformSpace UniformSpace.Completion Filter

variable (K : Type*) [Field K] [UniformSpace K]

local notation "hat" => Completion

/--
Definition of `CompletableTopField` / `CompletableTopField` 的定义

English:
class CompletableTopField
  parameters: : Prop extends T0Space K where
  extends: T0Space K
  axioms and operations (1):
    - nice : forall F : Filter K, Cauchy F -> 𝓝 0 ⊓ F = ⊥ -> Cauchy (map (fun x => x⁻¹) F)

中文:
类 CompletableTopField
  参数: : 命题 extends T0Space K where
  继承: T0Space K
  公理与运算 (1 个):
    - nice : 对任意 F : Filter K, Cauchy F -> 𝓝 0 ⊓ F = ⊥ -> Cauchy (map (fun x => x⁻¹) F)
-/
class CompletableTopField : Prop extends T0Space K where
  nice : forall F : Filter K, Cauchy F -> 𝓝 0 ⊓ F = ⊥ -> Cauchy (map (fun x => x⁻¹) F)

namespace UniformSpace

namespace Completion

instance (priority := 100) [T0Space K] : Nontrivial (hat K) :=
  (isUniformEmbedding_coe K).injective.nontrivial

variable {K}

/--
Definition of `hatInv` / `hatInv` 的定义

English:
definition hatInv
  signature: : hat K -> hat K
  body: isDenseInducing_coe.extend fun x : K => (↑x⁻¹ : hat K)

@[fun_prop]

中文:
定义 hatInv
  签名: : hat K -> hat K
  定义体: isDenseInducing_coe.extend fun x : K => (↑x⁻¹ : hat K)

@[fun_prop]

Depends on / 依赖: extend, isDenseInducing_coe, isDenseInducing_coe.extend
-/
def hatInv : hat K -> hat K :=
  isDenseInducing_coe.extend fun x : K => (↑x⁻¹ : hat K)

@[fun_prop]
/--
theorem `continuous_hatInv` / 定理 `continuous_hatInv`

English:
theorem continuous_hatInv
  given: [CompletableTopField K] {x : hat K} (h : x != 0)
  proof: by
  refine isDenseInducing_coe.continuousAt_extend ?_
  apply mem_of_superset (compl_singleton_mem_nhds h)
  intro y y_ne
  rw [mem_compl_singleton_iff] at y_ne
  apply CompleteSpace.complete
  have : (fun (x : K) => (↑x⁻¹ : hat K)) =
      ((fun (y : K) => (↑y : hat K)) ∘ (fun (x : K) => (x⁻¹ : K)

中文:
定理 continuous_hatInv
  条件: [CompletableTopField K] {x : hat K} (h : x != 0)
  证明: by
  refine isDenseInducing_coe.continuousAt_extend ?_
  apply mem_of_superset (compl_singleton_mem_nhds h)
  intro y y_ne
  rw [mem_compl_singleton_iff] at y_ne
  apply CompleteSpace.complete
  have : (fun (x : K) => (↑x⁻¹ : hat K)) =
      ((fun (y : K) => (↑y : hat K)) ∘ (fun (x : K) => (x⁻¹ : K)

Depends on / 依赖: Cauchy, Cauchy.map, CompletableTopField, CompletableTopField.nice, CompleteSpace, CompleteSpace.complete, Completion, Completion.uniformContinuous_coe, Filter, Filter.map_map, Function, Function.comp_def, cauchy_nh, comap_nhds_neBot, comp_def, compl_singleton_mem_nhds, complete, continuousAt_extend, isDenseInducing_coe, isDenseInducing_coe.comap_nhds_neBot
-/
theorem continuous_hatInv [CompletableTopField K] {x : hat K} (h : x != 0) :
    ContinuousAt hatInv x := by
  refine isDenseInducing_coe.continuousAt_extend ?_
  apply mem_of_superset (compl_singleton_mem_nhds h)
  intro y y_ne
  rw [mem_compl_singleton_iff] at y_ne
  apply CompleteSpace.complete
  have : (fun (x : K) => (↑x⁻¹ : hat K)) =
      ((fun (y : K) => (↑y : hat K)) ∘ (fun (x : K) => (x⁻¹ : K))) := by
    simp [Function.comp_def]
  rw [this]; rw [← Filter.map_map]
  apply Cauchy.map _ (Completion.uniformContinuous_coe K)
  apply CompletableTopField.nice
  · have := isDenseInducing_coe.comap_nhds_neBot y
    apply cauchy_nhds.comap
    rw [Completion.comap_coe_eq_uniformity]
  · have eq_bot : 𝓝 (0 : hat K) ⊓ 𝓝 y = ⊥ := by
      by_contra h
      exact y_ne (eq_of_nhds_neBot <| neBot_iff.mpr h).symm
    rw [isDenseInducing_coe.nhds_eq_comap (0 : K)]; rw [← Filter.comap_inf]
    norm_cast
    rw [eq_bot]
    exact comap_bot

open scoped Classical in
/--
Instance `instInvCompletion` / 实例 `instInvCompletion`

English:
instance instInvCompletion
  signature: : Inv (hat K)
  body: ⟨fun x => if x = 0 then 0 else hatInv x⟩

中文:
实例 instInvCompletion
  签名: : Inv (hat K)
  定义体: ⟨fun x => if x = 0 then 0 else hatInv x⟩

Depends on / 依赖: hatInv
-/
instance instInvCompletion : Inv (hat K) :=
  ⟨fun x => if x = 0 then 0 else hatInv x⟩

variable [IsTopologicalDivisionRing K]

/--
theorem `hatInv_extends` / 定理 `hatInv_extends`

English:
theorem hatInv_extends
  given: {x : K} (h : x != 0)
  statement: hatInv (x : hat K) = ↑(x⁻¹ : K)
  proof: isDenseInducing_coe.extend_eq_at ((continuous_coe K).continuousAt.comp (continuousAt_inv₀ h))

中文:
定理 hatInv_extends
  条件: {x : K} (h : x != 0)
  结论: hatInv (x : hat K) = ↑(x⁻¹ : K)
  证明: isDenseInducing_coe.extend_eq_at ((continuous_coe K).continuousAt.comp (continuousAt_inv₀ h))

Depends on / 依赖: continuousAt, continuousAt.comp, continuous_coe, extend_eq_at, isDenseInducing_coe, isDenseInducing_coe.extend_eq_at
-/
theorem hatInv_extends {x : K} (h : x != 0) : hatInv (x : hat K) = ↑(x⁻¹ : K) :=
  isDenseInducing_coe.extend_eq_at ((continuous_coe K).continuousAt.comp (continuousAt_inv₀ h))

variable [CompletableTopField K]

@[norm_cast]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (x : K)
  statement: (x : hat K)⁻¹ = ((x⁻¹ : K) : hat K)
  proof: by
  by_cases h : x = 0
  · rw [h, inv_zero]
    dsimp [Inv.inv]
    norm_cast
    simp
  · conv_lhs => dsimp [Inv.inv]
    rw [if_neg]
    · exact hatInv_extends h
    · exact fun H => h (isDenseEmbedding_coe.injective H)

中文:
定理 coe_inv
  条件: (x : K)
  结论: (x : hat K)⁻¹ = ((x⁻¹ : K) : hat K)
  证明: by
  by_cases h : x = 0
  · rw [h, inv_zero]
    dsimp [Inv.inv]
    norm_cast
    simp
  · conv_lhs => dsimp [Inv.inv]
    rw [if_neg]
    · exact hatInv_extends h
    · exact fun H => h (isDenseEmbedding_coe.injective H)

Depends on / 依赖: Inv.inv, conv_lhs, hatInv_extends, if_neg, injective, inv_zero, isDenseEmbedding_coe, isDenseEmbedding_coe.injective
-/
theorem coe_inv (x : K) : (x : hat K)⁻¹ = ((x⁻¹ : K) : hat K) := by
  by_cases h : x = 0
  · rw [h, inv_zero]
    dsimp [Inv.inv]
    norm_cast
    simp
  · conv_lhs => dsimp [Inv.inv]
    rw [if_neg]
    · exact hatInv_extends h
    · exact fun H => h (isDenseEmbedding_coe.injective H)

variable [IsUniformAddGroup K]

/--
theorem `mul_hatInv_cancel` / 定理 `mul_hatInv_cancel`

English:
theorem mul_hatInv_cancel
  given: {x : hat K} (x_ne : x != 0)
  statement: x * hatInv x = 1
  proof: by
  have : T1Space (hat K) := T2Space.t1Space
  let f := fun x : hat K => x * hatInv x
  let c := (fun (x : K) => (x : hat K))
  change f x = 1
  have cont : ContinuousAt f x := by fun_prop
  have clo : x in closure (c '' {0}ᶜ) := by
    have := isDenseInducing_coe.dense x
    rw [← image_univ]; rw

中文:
定理 mul_hatInv_cancel
  条件: {x : hat K} (x_ne : x != 0)
  结论: x * hatInv x = 1
  证明: by
  have : T1Space (hat K) := T2Space.t1Space
  let f := fun x : hat K => x * hatInv x
  let c := (fun (x : K) => (x : hat K))
  change f x = 1
  have cont : ContinuousAt f x := by fun_prop
  have clo : x in closure (c '' {0}ᶜ) := by
    have := isDenseInducing_coe.dense x
    rw [← image_univ]; rw

Depends on / 依赖: ContinuousAt, T1Space, T2Space, T2Space.t1Space, closure, compl_singleton_mem_nhds, fun_prop, hatInv, image_singleton, image_union, image_univ, isDenseInducing_coe, isDenseInducing_coe.dense, mem_closure_of_mem_closure_union, t1Space, union_compl_self, x_ne
-/
theorem mul_hatInv_cancel {x : hat K} (x_ne : x != 0) : x * hatInv x = 1 := by
  have : T1Space (hat K) := T2Space.t1Space
  let f := fun x : hat K => x * hatInv x
  let c := (fun (x : K) => (x : hat K))
  change f x = 1
  have cont : ContinuousAt f x := by fun_prop
  have clo : x in closure (c '' {0}ᶜ) := by
    have := isDenseInducing_coe.dense x
    rw [← image_univ]; rw [show (univ : Set K) = {0} union {0}ᶜ from (union_compl_self _).symm]; rw [image_union] at this
    apply mem_closure_of_mem_closure_union this
    rw [image_singleton]
    exact compl_singleton_mem_nhds x_ne
  have fxclo : f x in closure (f '' c '' {0}ᶜ) := mem_closure_image cont clo
  have : f '' c '' {0}ᶜ subseteq {1} := by
    rw [image_image]
    rintro _ ⟨z, z_ne, rfl⟩
    rw [mem_singleton_iff]
    rw [mem_compl_singleton_iff] at z_ne
    dsimp [f]
    rw [hatInv_extends z_ne]; rw [← coe_mul]
    rw [mul_inv_cancel₀ z_ne]; rw [coe_one]
  replace fxclo := closure_mono this fxclo
  rwa [closure_singleton, mem_singleton_iff] at fxclo

/--
Instance `instField` / 实例 `instField`

English:
instance instField
  signature: : Field (hat K) where
  body: fun x x_ne => by simp only [Inv.inv, if_neg x_ne, mul_hatInv_cancel x_ne]
  inv_zero := by simp only [Inv.inv, ite_true]
  -- TODO: use a better defeq
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

中文:
实例 instField
  签名: : Field (hat K) where
  定义体: fun x x_ne => by simp only [Inv.inv, if_neg x_ne, mul_hatInv_cancel x_ne]
  inv_zero := by simp only [Inv.inv, ite_true]
  -- TODO: use a better defeq
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

Depends on / 依赖: Inv.inv, if_neg, mul_hatInv_cancel, x_ne
-/
instance instField : Field (hat K) where
  mul_inv_cancel := fun x x_ne => by simp only [Inv.inv, if_neg x_ne, mul_hatInv_cancel x_ne]
  inv_zero := by simp only [Inv.inv, ite_true]
  -- TODO: use a better defeq
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalDivisionRing (hat K)
  body: { Completion.topologicalRing with
    continuousAt_inv₀ := by
      intro x x_ne
      have : { y | hatInv y = y⁻¹ } in 𝓝 x :=
        haveI : {(0 : hat K)}ᶜ subseteq { y : hat K | hatInv y = y⁻¹ } := by
          intro y y_ne
          rw [mem_compl_singleton_iff] at y_ne
          dsimp [Inv.inv]


中文:
实例 :
  签名: IsTopologicalDivisionRing (hat K)
  定义体: { Completion.topologicalRing with
    continuousAt_inv₀ := by
      intro x x_ne
      have : { y | hatInv y = y⁻¹ } in 𝓝 x :=
        haveI : {(0 : hat K)}ᶜ subseteq { y : hat K | hatInv y = y⁻¹ } := by
          intro y y_ne
          rw [mem_compl_singleton_iff] at y_ne
          dsimp [Inv.inv]


Depends on / 依赖: Completion, Completion.topologicalRing, ContinuousAt, ContinuousAt.congr, Inv.inv, compl_singleton_mem_nhds, continuous_hatInv, hatInv, if_neg, mem_compl_singleton_iff, mem_of_superset, subseteq, topologicalRing, x_ne, y_ne
-/
instance : IsTopologicalDivisionRing (hat K) :=
  { Completion.topologicalRing with
    continuousAt_inv₀ := by
      intro x x_ne
      have : { y | hatInv y = y⁻¹ } in 𝓝 x :=
        haveI : {(0 : hat K)}ᶜ subseteq { y : hat K | hatInv y = y⁻¹ } := by
          intro y y_ne
          rw [mem_compl_singleton_iff] at y_ne
          dsimp [Inv.inv]
          rw [if_neg y_ne]
        mem_of_superset (compl_singleton_mem_nhds x_ne) this
      exact ContinuousAt.congr (continuous_hatInv x_ne) this }

end Completion

end UniformSpace

variable (L : Type*) [Field L] [UniformSpace L] [CompletableTopField L]

/--
Instance `Subfield.completableTopField` / 实例 `Subfield.completableTopField`

English:
instance Subfield.completableTopField
  signature: (K : Subfield L)
  body: by
    let i : K ->+* L := K.subtype
    have hi : IsUniformInducing i := isUniformEmbedding_subtype_val.isUniformInducing
    rw [← hi.cauchy_map_iff] at F_cau ⊢
    rw [map_comm (show (i ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ i by ext; rfl)]
    apply CompletableTopField.nice _ F_cau
    rw [← Filter.

中文:
实例 Subfield.completableTopField
  签名: (K : Subfield L)
  定义体: by
    let i : K ->+* L := K.subtype
    have hi : IsUniformInducing i := isUniformEmbedding_subtype_val.isUniformInducing
    rw [← hi.cauchy_map_iff] at F_cau ⊢
    rw [map_comm (show (i ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ i by ext; rfl)]
    apply CompletableTopField.nice _ F_cau
    rw [← Filter.

Depends on / 依赖: CompletableTopField, CompletableTopField.nice, F_cau, Filter, Filter.map_bot, Filter.push_pull, IsUniformInducing, K.subtype, cauchy_map_iff, hi.cauchy_map_iff, hi.isInducing.nhds_eq_comap, inf_F, isInducing, isUniformEmbedding_subtype_val, isUniformEmbedding_subtype_val.isUniformInducing, isUniformInducing, map_bot, map_comm, map_zero, nhds_eq_comap
-/
instance Subfield.completableTopField (K : Subfield L) : CompletableTopField K where
  nice F F_cau inf_F := by
    let i : K ->+* L := K.subtype
    have hi : IsUniformInducing i := isUniformEmbedding_subtype_val.isUniformInducing
    rw [← hi.cauchy_map_iff] at F_cau ⊢
    rw [map_comm (show (i ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ i by ext; rfl)]
    apply CompletableTopField.nice _ F_cau
    rw [← Filter.push_pull']; rw [← map_zero i]; rw [← hi.isInducing.nhds_eq_comap]; rw [inf_F]; rw [Filter.map_bot]

instance (priority := 100) completableTopField_of_complete (L : Type*) [Field L] [UniformSpace L]
    [IsTopologicalDivisionRing L] [T0Space L] [CompleteSpace L] : CompletableTopField L where
  nice F cau_F hF := by
    have : NeBot F := cau_F.1
    rcases CompleteSpace.complete cau_F with ⟨x, hx⟩
    have hx' : x != 0 := by
      rintro rfl
      rw [inf_eq_right.mpr hx] at hF
      exact cau_F.1.ne hF
exact Filter.Tendsto.cauchy_map
      calc
        map (fun x => x⁻¹) F <= map (fun x => x⁻¹) (𝓝 x) := map_mono hx
        _ <= 𝓝 x⁻¹ := continuousAt_inv₀ hx'

variable {α β : Type*} [Field β] [b : UniformSpace β] [CompletableTopField β]
  [Field α]

/--
theorem `IsUniformInducing.completableTopField` / 定理 `IsUniformInducing.completableTopField`

English:
theorem IsUniformInducing.completableTopField
  proof: by
  refine CompletableTopField.mk (fun F F_cau inf_F => ?_)
  rw [← IsUniformInducing.cauchy_map_iff hf] at F_cau ⊢
  have h_comm : (f ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ f := by
    ext; simp only [Function.comp_apply, map_inv₀]
  rw [Filter.map_comm h_comm]
  apply CompletableTopField.nice _ F_cau

中文:
定理 IsUniformInducing.completableTopField
  证明: by
  refine CompletableTopField.mk (fun F F_cau inf_F => ?_)
  rw [← IsUniformInducing.cauchy_map_iff hf] at F_cau ⊢
  have h_comm : (f ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ f := by
    ext; simp only [Function.comp_apply, map_inv₀]
  rw [Filter.map_comm h_comm]
  apply CompletableTopField.nice _ F_cau

Depends on / 依赖: CompletableTopField, CompletableTopField.mk, CompletableTopField.nice, F_cau, Filter, Filter.map_bot, Filter.map_comm, Filter.push_pull, Function, Function.comp_apply, IsUniformInducing, IsUniformInducing.cauchy_map_iff, cauchy_map_iff, comp_apply, h_comm, hf.isInducing.nhds_eq_comap, inf_F, isInducing, map_bot, map_comm
-/
theorem IsUniformInducing.completableTopField
    [UniformSpace α] [T0Space α]
    {f : α ->+* β} (hf : IsUniformInducing f) :
    CompletableTopField α := by
  refine CompletableTopField.mk (fun F F_cau inf_F => ?_)
  rw [← IsUniformInducing.cauchy_map_iff hf] at F_cau ⊢
  have h_comm : (f ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ f := by
    ext; simp only [Function.comp_apply, map_inv₀]
  rw [Filter.map_comm h_comm]
  apply CompletableTopField.nice _ F_cau
  rw [← Filter.push_pull']; rw [← map_zero f]; rw [← hf.isInducing.nhds_eq_comap]; rw [inf_F]; rw [Filter.map_bot]
