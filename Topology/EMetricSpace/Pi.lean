/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Topology.UniformSpace.Pi

/-!
# Indexed product of extended metric spaces
-/

@[expose] public section

open Set Filter

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}

open scoped Uniformity Topology NNReal ENNReal Pointwise

variable [PseudoEMetricSpace α]

open EMetric

section Pi

open Finset

variable {X : β -> Type*} [Fintype β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: b, EDist (X b)] : EDist (forall b, X b) where
  body: Finset.sup univ fun b => edist (f b) (g b)

中文:
实例 [forall
  签名: b, EDist (X b)] : EDist (对任意 b, X b) where
  定义体: Finset.sup univ fun b => edist (f b) (g b)

Depends on / 依赖: Finset, Finset.sup
-/
instance [forall b, EDist (X b)] : EDist (forall b, X b) where
  edist f g := Finset.sup univ fun b => edist (f b) (g b)

/--
theorem `edist_pi_def` / 定理 `edist_pi_def`

English:
theorem edist_pi_def
  given: [forall b, EDist (X b)] (f g : forall b, X b)
  proof: rfl

中文:
定理 edist_pi_def
  条件: [对任意 b, EDist (X b)] (f g : 对任意 b, X b)
  证明: rfl
-/
theorem edist_pi_def [forall b, EDist (X b)] (f g : forall b, X b) :
    edist f g = Finset.sup univ fun b => edist (f b) (g b) :=
  rfl

/--
theorem `edist_le_pi_edist` / 定理 `edist_le_pi_edist`

English:
theorem edist_le_pi_edist
  given: [forall b, EDist (X b)] (f g : forall b, X b) (b : β)
  proof: le_sup (f := fun b => edist (f b) (g b)) (Finset.mem_univ b)

中文:
定理 edist_le_pi_edist
  条件: [对任意 b, EDist (X b)] (f g : 对任意 b, X b) (b : β)
  证明: le_sup (f := fun b => edist (f b) (g b)) (Finset.mem_univ b)

Depends on / 依赖: Finset, Finset.mem_univ, le_sup, mem_univ
-/
theorem edist_le_pi_edist [forall b, EDist (X b)] (f g : forall b, X b) (b : β) :
    edist (f b) (g b) <= edist f g :=
  le_sup (f := fun b => edist (f b) (g b)) (Finset.mem_univ b)

/--
theorem `edist_pi_le_iff` / 定理 `edist_pi_le_iff`

English:
theorem edist_pi_le_iff
  given: [forall b, EDist (X b)] {f g : forall b, X b} {d : Real>=0∞}
  proof: Finset.sup_le_iff.trans by simp only [Finset.mem_univ, forall_const]

中文:
定理 edist_pi_le_iff
  条件: [对任意 b, EDist (X b)] {f g : 对任意 b, X b} {d : 实数>=0∞}
  证明: Finset.sup_le_iff.trans by simp only [Finset.mem_univ, forall_const]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sup_le_iff.trans, forall_const, mem_univ, sup_le_iff
-/
theorem edist_pi_le_iff [forall b, EDist (X b)] {f g : forall b, X b} {d : Real>=0∞} :
    edist f g <= d ↔ forall b, edist (f b) (g b) <= d :=
Finset.sup_le_iff.trans by simp only [Finset.mem_univ, forall_const]

/--
theorem `edist_pi_const_le` / 定理 `edist_pi_const_le`

English:
theorem edist_pi_const_le
  given: (a b : α)
  statement: (edist (fun _ : β => a) fun _ => b) <= edist a b
  proof: edist_pi_le_iff.2 fun _ => le_rfl

@[simp]

中文:
定理 edist_pi_const_le
  条件: (a b : α)
  结论: (edist (fun _ : β => a) fun _ => b) <= edist a b
  证明: edist_pi_le_iff.2 fun _ => le_rfl

@[simp]

Depends on / 依赖: edist_pi_le_iff, le_rfl
-/
theorem edist_pi_const_le (a b : α) : (edist (fun _ : β => a) fun _ => b) <= edist a b :=
  edist_pi_le_iff.2 fun _ => le_rfl

@[simp]
/--
theorem `edist_pi_const` / 定理 `edist_pi_const`

English:
theorem edist_pi_const
  given: [Nonempty β] (a b : α)
  statement: (edist (fun _ : β => a) fun _ => b) = edist a b
  proof: Finset.sup_const univ_nonempty (edist a b)

中文:
定理 edist_pi_const
  条件: [Nonempty β] (a b : α)
  结论: (edist (fun _ : β => a) fun _ => b) = edist a b
  证明: Finset.sup_const univ_nonempty (edist a b)

Depends on / 依赖: Finset, Finset.sup_const, sup_const, univ_nonempty
-/
theorem edist_pi_const [Nonempty β] (a b : α) : (edist (fun _ : β => a) fun _ => b) = edist a b :=
  Finset.sup_const univ_nonempty (edist a b)

/--
Instance `pseudoEMetricSpacePi` / 实例 `pseudoEMetricSpacePi`

English:
instance pseudoEMetricSpacePi
  signature: [forall b, PseudoEMetricSpace (X b)]
  body: bot_unique Finset.sup_le by simp
  edist_comm f g := by simp [edist_pi_def, edist_comm]
  edist_triangle _ g _ := edist_pi_le_iff.2 fun b => le_trans (edist_triangle _ (g b) _)
    (add_le_add (edist_le_pi_edist _ _ _) (edist_le_pi_edist _ _ _))
  toUniformSpace := Pi.uniformSpace _
  uniformity_edi

中文:
实例 pseudoEMetricSpacePi
  签名: [对任意 b, PseudoEMetricSpace (X b)]
  定义体: bot_unique Finset.sup_le by simp
  edist_comm f g := by simp [edist_pi_def, edist_comm]
  edist_triangle _ g _ := edist_pi_le_iff.2 fun b => le_trans (edist_triangle _ (g b) _)
    (add_le_add (edist_le_pi_edist _ _ _) (edist_le_pi_edist _ _ _))
  toUniformSpace := Pi.uniformSpace _
  uniformity_edi

Depends on / 依赖: Finset, Finset.sup_le, bot_unique, sup_le
-/
instance pseudoEMetricSpacePi [forall b, PseudoEMetricSpace (X b)] : PseudoEMetricSpace (forall b, X b) where
edist_self f := bot_unique Finset.sup_le by simp
  edist_comm f g := by simp [edist_pi_def, edist_comm]
  edist_triangle _ g _ := edist_pi_le_iff.2 fun b => le_trans (edist_triangle _ (g b) _)
    (add_le_add (edist_le_pi_edist _ _ _) (edist_le_pi_edist _ _ _))
  toUniformSpace := Pi.uniformSpace _
  uniformity_edist := by
    simp only [Pi.uniformity, PseudoEMetricSpace.uniformity_edist, comap_iInf, gt_iff_lt,
      preimage_ofPred_eq, comap_principal, edist_pi_def]
    rw [iInf_comm]; congr; funext ε
    rw [iInf_comm]; congr; funext εpos
    simp [ofPred_forall, εpos]

end Pi

variable {γ : Type w} [EMetricSpace γ]

section Pi

open Finset

variable {X : β -> Type*} [Fintype β]

/--
Instance `emetricSpacePi` / 实例 `emetricSpacePi`

English:
instance emetricSpacePi
  signature: [forall b, EMetricSpace (X b)]
  body: .ofT0PseudoEMetricSpace _

中文:
实例 emetricSpacePi
  签名: [对任意 b, EMetricSpace (X b)]
  定义体: .ofT0PseudoEMetricSpace _

Depends on / 依赖: ofT0PseudoEMetricSpace
-/
instance emetricSpacePi [forall b, EMetricSpace (X b)] : EMetricSpace (forall b, X b) :=
  .ofT0PseudoEMetricSpace _

end Pi
