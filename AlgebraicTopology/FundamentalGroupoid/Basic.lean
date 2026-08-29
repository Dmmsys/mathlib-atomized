/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Data.Set.Subsingleton

/-!
# Fundamental groupoid of a space

Given a topological space `X`, we can define the fundamental groupoid of `X` to be the category with
objects being points of `X`, and morphisms `x ⟶ y` being paths from `x` to `y`, quotiented by
homotopy equivalence. With this, the fundamental group of `X` based at `x` is just the automorphism
group of `x`.
-/

@[expose] public section

open CategoryTheory

universe u

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ : X}

noncomputable section

open unitInterval

namespace Path

namespace Homotopy

section

/--
Definition of `reflTransSymmAux` / `reflTransSymmAux` 的定义

English:
definition reflTransSymmAux
  signature: (x : I × I)
  body: if (x.2 : Real) <= 1 / 2 then x.1 * 2 * x.2 else x.1 * (2 - 2 * x.2)

@[continuity, fun_prop]

中文:
定义 reflTransSymmAux
  签名: (x : I × I)
  定义体: if (x.2 : Real) <= 1 / 2 then x.1 * 2 * x.2 else x.1 * (2 - 2 * x.2)

@[continuity, fun_prop]
-/
def reflTransSymmAux (x : I × I) : Real :=
  if (x.2 : Real) <= 1 / 2 then x.1 * 2 * x.2 else x.1 * (2 - 2 * x.2)

@[continuity, fun_prop]
/--
theorem `continuous_reflTransSymmAux` / 定理 `continuous_reflTransSymmAux`

English:
theorem continuous_reflTransSymmAux
  statement: Continuous reflTransSymmAux
  proof: continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by grind)

中文:
定理 continuous_reflTransSymmAux
  结论: Continuous reflTransSymmAux
  证明: continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by grind)

Depends on / 依赖: continuous_if_le, fun_prop
-/
theorem continuous_reflTransSymmAux : Continuous reflTransSymmAux :=
  continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by grind)

/--
theorem `reflTransSymmAux_mem_I` / 定理 `reflTransSymmAux_mem_I`

English:
theorem reflTransSymmAux_mem_I
  given: (x : I × I)
  statement: reflTransSymmAux x in I
  proof: by
  dsimp only [reflTransSymmAux]
  split_ifs
  · constructor
    · apply mul_nonneg <;> grind
    · rw [mul_assoc]
      apply mul_le_one₀ <;> grind
  · constructor
    · apply mul_nonneg <;> grind
    · apply mul_le_one₀ <;> grind

中文:
定理 reflTransSymmAux_mem_I
  条件: (x : I × I)
  结论: reflTransSymmAux x in I
  证明: by
  dsimp only [reflTransSymmAux]
  split_ifs
  · constructor
    · apply mul_nonneg <;> grind
    · rw [mul_assoc]
      apply mul_le_one₀ <;> grind
  · constructor
    · apply mul_nonneg <;> grind
    · apply mul_le_one₀ <;> grind

Depends on / 依赖: mul_assoc, mul_nonneg, reflTransSymmAux, split_ifs
-/
theorem reflTransSymmAux_mem_I (x : I × I) : reflTransSymmAux x in I := by
  dsimp only [reflTransSymmAux]
  split_ifs
  · constructor
    · apply mul_nonneg <;> grind
    · rw [mul_assoc]
      apply mul_le_one₀ <;> grind
  · constructor
    · apply mul_nonneg <;> grind
    · apply mul_le_one₀ <;> grind

/--
Definition of `reflTransSymm` / `reflTransSymm` 的定义

English:
definition reflTransSymm
  signature: (p : Path x₀ x₁)
  body: p ⟨reflTransSymmAux x, reflTransSymmAux_mem_I x⟩
  continuous_toFun := by fun_prop
  map_zero_left := by simp [reflTransSymmAux]
  map_one_left x := by
    simp only [reflTransSymmAux, Path.trans]
    cases le_or_gt (x : Real) 2⁻¹ with
    | inl hx => simp [hx, ← extend_apply]
    | inr hx =>
      

中文:
定义 reflTransSymm
  签名: (p : Path x₀ x₁)
  定义体: p ⟨reflTransSymmAux x, reflTransSymmAux_mem_I x⟩
  continuous_toFun := by fun_prop
  map_zero_left := by simp [reflTransSymmAux]
  map_one_left x := by
    simp only [reflTransSymmAux, Path.trans]
    cases le_or_gt (x : Real) 2⁻¹ with
    | inl hx => simp [hx, ← extend_apply]
    | inr hx =>
      

Depends on / 依赖: reflTransSymmAux, reflTransSymmAux_mem_I
-/
def reflTransSymm (p : Path x₀ x₁) : Homotopy (Path.refl x₀) (p.trans p.symm) where
  toFun x := p ⟨reflTransSymmAux x, reflTransSymmAux_mem_I x⟩
  continuous_toFun := by fun_prop
  map_zero_left := by simp [reflTransSymmAux]
  map_one_left x := by
    simp only [reflTransSymmAux, Path.trans]
    cases le_or_gt (x : Real) 2⁻¹ with
    | inl hx => simp [hx, ← extend_apply]
    | inr hx =>
      have : p.extend (2 - 2 * ↑x) = p.extend (1 - (2 * ↑x - 1)) := by ring_nf
      simpa [hx.not_ge, ← extend_apply]
  prop' t := by norm_num [reflTransSymmAux]

/--
Definition of `reflSymmTrans` / `reflSymmTrans` 的定义

English:
definition reflSymmTrans
  signature: (p : Path x₀ x₁)
  body: (reflTransSymm p.symm).cast rfl congr_arg _ (Path.symm_symm _)

中文:
定义 reflSymmTrans
  签名: (p : Path x₀ x₁)
  定义体: (reflTransSymm p.symm).cast rfl congr_arg _ (Path.symm_symm _)

Depends on / 依赖: Path.symm_symm, congr_arg, p.symm, reflTransSymm, symm_symm
-/
def reflSymmTrans (p : Path x₀ x₁) : Homotopy (Path.refl x₁) (p.symm.trans p) :=
(reflTransSymm p.symm).cast rfl congr_arg _ (Path.symm_symm _)

end

section TransRefl

/--
Definition of `transReflReparamAux` / `transReflReparamAux` 的定义

English:
definition transReflReparamAux
  signature: (t : I)
  body: if (t : Real) <= 1 / 2 then 2 * t else 1

@[continuity, fun_prop]

中文:
定义 transReflReparamAux
  签名: (t : I)
  定义体: if (t : Real) <= 1 / 2 then 2 * t else 1

@[continuity, fun_prop]
-/
def transReflReparamAux (t : I) : Real :=
  if (t : Real) <= 1 / 2 then 2 * t else 1

@[continuity, fun_prop]
/--
theorem `continuous_transReflReparamAux` / 定理 `continuous_transReflReparamAux`

English:
theorem continuous_transReflReparamAux
  statement: Continuous transReflReparamAux
  proof: continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by grind)

中文:
定理 continuous_transReflReparamAux
  结论: Continuous transReflReparamAux
  证明: continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by grind)

Depends on / 依赖: continuous_if_le, fun_prop
-/
theorem continuous_transReflReparamAux : Continuous transReflReparamAux :=
  continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by grind)

/--
theorem `transReflReparamAux_mem_I` / 定理 `transReflReparamAux_mem_I`

English:
theorem transReflReparamAux_mem_I
  given: (t : I)
  statement: transReflReparamAux t in I
  proof: by
  unfold transReflReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]

中文:
定理 transReflReparamAux_mem_I
  条件: (t : I)
  结论: transReflReparamAux t in I
  证明: by
  unfold transReflReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]

Depends on / 依赖: le_one, nonneg, split_ifs, transReflReparamAux, unitInterval, unitInterval.le_one, unitInterval.nonneg
-/
theorem transReflReparamAux_mem_I (t : I) : transReflReparamAux t in I := by
  unfold transReflReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]

/--
theorem `transReflReparamAux_zero` / 定理 `transReflReparamAux_zero`

English:
theorem transReflReparamAux_zero
  statement: transReflReparamAux 0 = 0
  proof: by
  norm_num [transReflReparamAux]

中文:
定理 transReflReparamAux_zero
  结论: transReflReparamAux 0 = 0
  证明: by
  norm_num [transReflReparamAux]

Depends on / 依赖: transReflReparamAux
-/
theorem transReflReparamAux_zero : transReflReparamAux 0 = 0 := by
  norm_num [transReflReparamAux]

/--
theorem `transReflReparamAux_one` / 定理 `transReflReparamAux_one`

English:
theorem transReflReparamAux_one
  statement: transReflReparamAux 1 = 1
  proof: by
  norm_num [transReflReparamAux]

中文:
定理 transReflReparamAux_one
  结论: transReflReparamAux 1 = 1
  证明: by
  norm_num [transReflReparamAux]

Depends on / 依赖: transReflReparamAux
-/
theorem transReflReparamAux_one : transReflReparamAux 1 = 1 := by
  norm_num [transReflReparamAux]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `trans_refl_reparam` / 定理 `trans_refl_reparam`

English:
theorem trans_refl_reparam
  given: (p : Path x₀ x₁)
  proof: by
  ext
  unfold transReflReparamAux
  simp only [coe_reparam]
  grind

中文:
定理 trans_refl_reparam
  条件: (p : Path x₀ x₁)
  证明: by
  ext
  unfold transReflReparamAux
  simp only [coe_reparam]
  grind

Depends on / 依赖: coe_reparam, transReflReparamAux
-/
theorem trans_refl_reparam (p : Path x₀ x₁) :
    p.trans (Path.refl x₁) =
      p.reparam (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩) (by fun_prop)
        (Subtype.ext transReflReparamAux_zero) (Subtype.ext transReflReparamAux_one) := by
  ext
  unfold transReflReparamAux
  simp only [coe_reparam]
  grind

/--
Definition of `transRefl` / `transRefl` 的定义

English:
definition transRefl
  signature: (p : Path x₀ x₁)
  body: ((Homotopy.reparam p (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩)
          (by fun_prop) (Subtype.ext transReflReparamAux_zero)
          (Subtype.ext transReflReparamAux_one)).cast
      rfl (trans_refl_reparam p).symm).symm

中文:
定义 transRefl
  签名: (p : Path x₀ x₁)
  定义体: ((Homotopy.reparam p (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩)
          (by fun_prop) (Subtype.ext transReflReparamAux_zero)
          (Subtype.ext transReflReparamAux_one)).cast
      rfl (trans_refl_reparam p).symm).symm

Depends on / 依赖: Homotopy, Homotopy.reparam, Subtype, Subtype.ext, fun_prop, reparam, transReflReparamAux, transReflReparamAux_mem_I, transReflReparamAux_one, transReflReparamAux_zero, trans_refl_reparam
-/
def transRefl (p : Path x₀ x₁) : Homotopy (p.trans (Path.refl x₁)) p :=
  ((Homotopy.reparam p (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩)
          (by fun_prop) (Subtype.ext transReflReparamAux_zero)
          (Subtype.ext transReflReparamAux_one)).cast
      rfl (trans_refl_reparam p).symm).symm

/--
Definition of `reflTrans` / `reflTrans` 的定义

English:
definition reflTrans
  signature: (p : Path x₀ x₁)
  body: (transRefl p.symm).symm₂.cast (by simp) (by simp)

中文:
定义 reflTrans
  签名: (p : Path x₀ x₁)
  定义体: (transRefl p.symm).symm₂.cast (by simp) (by simp)

Depends on / 依赖: p.symm, transRefl
-/
def reflTrans (p : Path x₀ x₁) : Homotopy ((Path.refl x₀).trans p) p :=
  (transRefl p.symm).symm₂.cast (by simp) (by simp)

end TransRefl

section Assoc

/--
Definition of `transAssocReparamAux` / `transAssocReparamAux` 的定义

English:
definition transAssocReparamAux
  signature: (t : I)
  body: if (t : Real) <= 1 / 4 then 2 * t else if (t : Real) <= 1 / 2 then t + 1 / 4 else 1 / 2 * (t + 1)

@[continuity, fun_prop]

中文:
定义 transAssocReparamAux
  签名: (t : I)
  定义体: if (t : Real) <= 1 / 4 then 2 * t else if (t : Real) <= 1 / 2 then t + 1 / 4 else 1 / 2 * (t + 1)

@[continuity, fun_prop]
-/
def transAssocReparamAux (t : I) : Real :=
  if (t : Real) <= 1 / 4 then 2 * t else if (t : Real) <= 1 / 2 then t + 1 / 4 else 1 / 2 * (t + 1)

@[continuity, fun_prop]
/--
theorem `continuous_transAssocReparamAux` / 定理 `continuous_transAssocReparamAux`

English:
theorem continuous_transAssocReparamAux
  statement: Continuous transAssocReparamAux
  proof: continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop)
    (continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (by grind)).continuousOn (by grind)

中文:
定理 continuous_transAssocReparamAux
  结论: Continuous transAssocReparamAux
  证明: continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop)
    (continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (by grind)).continuousOn (by grind)

Depends on / 依赖: continuousOn, continuous_if_le, fun_prop
-/
theorem continuous_transAssocReparamAux : Continuous transAssocReparamAux :=
  continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop)
    (continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (by grind)).continuousOn (by grind)

/--
theorem `transAssocReparamAux_mem_I` / 定理 `transAssocReparamAux_mem_I`

English:
theorem transAssocReparamAux_mem_I
  given: (t : I)
  statement: transAssocReparamAux t in I
  proof: by
  unfold transAssocReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]

中文:
定理 transAssocReparamAux_mem_I
  条件: (t : I)
  结论: transAssocReparamAux t in I
  证明: by
  unfold transAssocReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]

Depends on / 依赖: le_one, nonneg, split_ifs, transAssocReparamAux, unitInterval, unitInterval.le_one, unitInterval.nonneg
-/
theorem transAssocReparamAux_mem_I (t : I) : transAssocReparamAux t in I := by
  unfold transAssocReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]

/--
theorem `transAssocReparamAux_zero` / 定理 `transAssocReparamAux_zero`

English:
theorem transAssocReparamAux_zero
  statement: transAssocReparamAux 0 = 0
  proof: by
  norm_num [transAssocReparamAux]

中文:
定理 transAssocReparamAux_zero
  结论: transAssocReparamAux 0 = 0
  证明: by
  norm_num [transAssocReparamAux]

Depends on / 依赖: transAssocReparamAux
-/
theorem transAssocReparamAux_zero : transAssocReparamAux 0 = 0 := by
  norm_num [transAssocReparamAux]

/--
theorem `transAssocReparamAux_one` / 定理 `transAssocReparamAux_one`

English:
theorem transAssocReparamAux_one
  statement: transAssocReparamAux 1 = 1
  proof: by
  norm_num [transAssocReparamAux]

中文:
定理 transAssocReparamAux_one
  结论: transAssocReparamAux 1 = 1
  证明: by
  norm_num [transAssocReparamAux]

Depends on / 依赖: transAssocReparamAux
-/
theorem transAssocReparamAux_one : transAssocReparamAux 1 = 1 := by
  norm_num [transAssocReparamAux]

/--
theorem `trans_assoc_reparam` / 定理 `trans_assoc_reparam`

English:
theorem trans_assoc_reparam
  given: {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃)
  proof: by
  ext x
  simp only [transAssocReparamAux, Path.trans_apply, Function.comp_apply, Path.coe_reparam]
  split_ifs
  iterate 12 grind
  · linarith
  · linarith
  · grind

中文:
定理 trans_assoc_reparam
  条件: {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃)
  证明: by
  ext x
  simp only [transAssocReparamAux, Path.trans_apply, Function.comp_apply, Path.coe_reparam]
  split_ifs
  iterate 12 grind
  · linarith
  · linarith
  · grind

Depends on / 依赖: Function, Function.comp_apply, Path.coe_reparam, Path.trans_apply, coe_reparam, comp_apply, iterate, split_ifs, transAssocReparamAux, trans_apply
-/
theorem trans_assoc_reparam {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    (p.trans q).trans r =
      (p.trans (q.trans r)).reparam
        (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by fun_prop)
        (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one) := by
  ext x
  simp only [transAssocReparamAux, Path.trans_apply, Function.comp_apply, Path.coe_reparam]
  split_ifs
  iterate 12 grind
  · linarith
  · linarith
  · grind

/--
Definition of `transAssoc` / `transAssoc` 的定义

English:
definition transAssoc
  signature: {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃)
  body: ((Homotopy.reparam (p.trans (q.trans r))
          (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by fun_prop)
          (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one)).cast
      rfl (trans_assoc_reparam p q r).symm).symm

中文:
定义 transAssoc
  签名: {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃)
  定义体: ((Homotopy.reparam (p.trans (q.trans r))
          (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by fun_prop)
          (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one)).cast
      rfl (trans_assoc_reparam p q r).symm).symm

Depends on / 依赖: Homotopy, Homotopy.reparam, Subtype, Subtype.ext, fun_prop, p.trans, q.trans, reparam, transAssocReparamAux, transAssocReparamAux_mem_I, transAssocReparamAux_one, transAssocReparamAux_zero, trans_assoc_reparam
-/
def transAssoc {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    Homotopy ((p.trans q).trans r) (p.trans (q.trans r)) :=
  ((Homotopy.reparam (p.trans (q.trans r))
          (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by fun_prop)
          (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one)).cast
      rfl (trans_assoc_reparam p q r).symm).symm

end Assoc

end Homotopy

namespace Homotopic

/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  given: (p : Path x₀ x₁)
  proof: ⟨Homotopy.reflTrans p⟩

中文:
定理 refl_trans
  条件: (p : Path x₀ x₁)
  证明: ⟨Homotopy.reflTrans p⟩

Depends on / 依赖: Homotopy, Homotopy.reflTrans, reflTrans
-/
theorem refl_trans (p : Path x₀ x₁) :
    ((Path.refl x₀).trans p).Homotopic p :=
  ⟨Homotopy.reflTrans p⟩

/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  given: (p : Path x₀ x₁)
  proof: ⟨Homotopy.transRefl p⟩

中文:
定理 trans_refl
  条件: (p : Path x₀ x₁)
  证明: ⟨Homotopy.transRefl p⟩

Depends on / 依赖: Homotopy, Homotopy.transRefl, transRefl
-/
theorem trans_refl (p : Path x₀ x₁) :
    (p.trans (Path.refl x₁)).Homotopic p :=
  ⟨Homotopy.transRefl p⟩

/--
theorem `trans_symm` / 定理 `trans_symm`

English:
theorem trans_symm
  given: (p : Path x₀ x₁)
  proof: ⟨(Homotopy.reflTransSymm p).symm⟩

中文:
定理 trans_symm
  条件: (p : Path x₀ x₁)
  证明: ⟨(Homotopy.reflTransSymm p).symm⟩

Depends on / 依赖: Homotopy, Homotopy.reflTransSymm, reflTransSymm
-/
theorem trans_symm (p : Path x₀ x₁) :
    (p.trans p.symm).Homotopic (Path.refl x₀) :=
  ⟨(Homotopy.reflTransSymm p).symm⟩

/--
theorem `symm_trans` / 定理 `symm_trans`

English:
theorem symm_trans
  given: (p : Path x₀ x₁)
  proof: ⟨(Homotopy.reflSymmTrans p).symm⟩

中文:
定理 symm_trans
  条件: (p : Path x₀ x₁)
  证明: ⟨(Homotopy.reflSymmTrans p).symm⟩

Depends on / 依赖: Homotopy, Homotopy.reflSymmTrans, reflSymmTrans
-/
theorem symm_trans (p : Path x₀ x₁) :
    (p.symm.trans p).Homotopic (Path.refl x₁) :=
  ⟨(Homotopy.reflSymmTrans p).symm⟩

/--
theorem `trans_assoc` / 定理 `trans_assoc`

English:
theorem trans_assoc
  given: {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃)
  proof: ⟨Homotopy.transAssoc p q r⟩

中文:
定理 trans_assoc
  条件: {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃)
  证明: ⟨Homotopy.transAssoc p q r⟩

Depends on / 依赖: Homotopy, Homotopy.transAssoc, transAssoc
-/
theorem trans_assoc {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    ((p.trans q).trans r).Homotopic (p.trans (q.trans r)) :=
  ⟨Homotopy.transAssoc p q r⟩

namespace Quotient

@[simp, grind =]
/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  given: (γ : Homotopic.Quotient x₀ x₁)
  proof: by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_refl, eq] using Homotopic.refl_trans γ

@[simp, grind =]

中文:
定理 refl_trans
  条件: (γ : Homotopic.Quotient x₀ x₁)
  证明: by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_refl, eq] using Homotopic.refl_trans γ

@[simp, grind =]

Depends on / 依赖: Homotopic, Homotopic.refl_trans, Quotient, Quotient.ind, mk_refl, mk_trans, refl_trans
-/
theorem refl_trans (γ : Homotopic.Quotient x₀ x₁) :
    trans (refl x₀) γ = γ := by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_refl, eq] using Homotopic.refl_trans γ

@[simp, grind =]
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  given: (γ : Homotopic.Quotient x₀ x₁)
  proof: by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_refl, eq] using Homotopic.trans_refl γ

@[simp, grind =]

中文:
定理 trans_refl
  条件: (γ : Homotopic.Quotient x₀ x₁)
  证明: by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_refl, eq] using Homotopic.trans_refl γ

@[simp, grind =]

Depends on / 依赖: Homotopic, Homotopic.trans_refl, Quotient, Quotient.ind, mk_refl, mk_trans, trans_refl
-/
theorem trans_refl (γ : Homotopic.Quotient x₀ x₁) :
    trans γ (refl x₁) = γ := by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_refl, eq] using Homotopic.trans_refl γ

@[simp, grind =]
/--
theorem `trans_symm` / 定理 `trans_symm`

English:
theorem trans_symm
  given: (γ : Homotopic.Quotient x₀ x₁)
  proof: by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_symm, ← mk_refl, eq] using Homotopic.trans_symm γ

@[simp, grind =]

中文:
定理 trans_symm
  条件: (γ : Homotopic.Quotient x₀ x₁)
  证明: by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_symm, ← mk_refl, eq] using Homotopic.trans_symm γ

@[simp, grind =]

Depends on / 依赖: Homotopic, Homotopic.trans_symm, Quotient, Quotient.ind, mk_refl, mk_symm, mk_trans, trans_symm
-/
theorem trans_symm (γ : Homotopic.Quotient x₀ x₁) :
    trans γ (symm γ) = refl x₀ := by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_symm, ← mk_refl, eq] using Homotopic.trans_symm γ

@[simp, grind =]
/--
theorem `symm_trans` / 定理 `symm_trans`

English:
theorem symm_trans
  given: (γ : Homotopic.Quotient x₀ x₁)
  proof: by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_symm, ← mk_refl, eq] using Homotopic.symm_trans γ

@[simp, grind _=_]

中文:
定理 symm_trans
  条件: (γ : Homotopic.Quotient x₀ x₁)
  证明: by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_symm, ← mk_refl, eq] using Homotopic.symm_trans γ

@[simp, grind _=_]

Depends on / 依赖: Homotopic, Homotopic.symm_trans, Quotient, Quotient.ind, mk_refl, mk_symm, mk_trans, symm_trans
-/
theorem symm_trans (γ : Homotopic.Quotient x₀ x₁) :
    trans (symm γ) γ = refl x₁ := by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_symm, ← mk_refl, eq] using Homotopic.symm_trans γ

@[simp, grind _=_]
/--
theorem `trans_assoc` / 定理 `trans_assoc`

English:
theorem trans_assoc
  statement: {x₀ x₁ x₂ x₃ : X}
  proof: by
  induction γ₀ using Quotient.ind with | mk γ₀ =>
  induction γ₁ using Quotient.ind with | mk γ₁ =>
  induction γ₂ using Quotient.ind with | mk γ₂ =>
  simpa [← mk_trans, eq] using Homotopic.trans_assoc γ₀ γ₁ γ₂

中文:
定理 trans_assoc
  结论: {x₀ x₁ x₂ x₃ : X}
  证明: by
  induction γ₀ using Quotient.ind with | mk γ₀ =>
  induction γ₁ using Quotient.ind with | mk γ₁ =>
  induction γ₂ using Quotient.ind with | mk γ₂ =>
  simpa [← mk_trans, eq] using Homotopic.trans_assoc γ₀ γ₁ γ₂

Depends on / 依赖: Homotopic, Homotopic.trans_assoc, Quotient, Quotient.ind, mk_trans, trans_assoc
-/
theorem trans_assoc {x₀ x₁ x₂ x₃ : X}
    (γ₀ : Homotopic.Quotient x₀ x₁)
    (γ₁ : Homotopic.Quotient x₁ x₂)
    (γ₂ : Homotopic.Quotient x₂ x₃) :
    trans (trans γ₀ γ₁) γ₂ = trans γ₀ (trans γ₁ γ₂) := by
  induction γ₀ using Quotient.ind with | mk γ₀ =>
  induction γ₁ using Quotient.ind with | mk γ₁ =>
  induction γ₂ using Quotient.ind with | mk γ₂ =>
  simpa [← mk_trans, eq] using Homotopic.trans_assoc γ₀ γ₁ γ₂

end Quotient

end Homotopic

end Path

/-- The fundamental groupoid of a space `X` is defined to be a wrapper around `X`, and we
subsequently put a `CategoryTheory.Groupoid` structure on it. -/
@[ext]
/--
Definition of `FundamentalGroupoid` / `FundamentalGroupoid` 的定义

English:
structure FundamentalGroupoid
  parameters: (X : Type*)
  axioms and operations (1):
    - as : X

中文:
结构 FundamentalGroupoid
  参数: (X : 类型)
  公理与运算 (1 个):
    - as : X
-/
structure FundamentalGroupoid (X : Type*) where
  /-- View a term of `FundamentalGroupoid X` as a term of `X`. -/
  as : X

namespace FundamentalGroupoid

/-- The equivalence between `X` and the underlying type of its fundamental groupoid.
  This is useful for transferring constructions (instances, etc.)
  from `X` to `πₓ X`. -/
@[simps]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: (X : Type*)
  body: x.as
  invFun x := .mk x

@[simp]

中文:
定义 equiv
  签名: (X : 类型)
  定义体: x.as
  invFun x := .mk x

@[simp]

Depends on / 依赖: x.as
-/
def equiv (X : Type*) : FundamentalGroupoid X ≃ X where
  toFun x := x.as
  invFun x := .mk x

@[simp]
/--
lemma `isEmpty_iff` / 引理 `isEmpty_iff`

English:
lemma isEmpty_iff
  given: (X : Type*)
  proof: .isEmpty_congr equiv _

中文:
引理 isEmpty_iff
  条件: (X : 类型)
  证明: .isEmpty_congr equiv _

Depends on / 依赖: isEmpty_congr
-/
lemma isEmpty_iff (X : Type*) :
    IsEmpty (FundamentalGroupoid X) ↔ IsEmpty X :=
.isEmpty_congr equiv _

instance (X : Type*) [IsEmpty X] :
    IsEmpty (FundamentalGroupoid X) :=
.isEmpty equiv _

@[simp]
/--
lemma `nonempty_iff` / 引理 `nonempty_iff`

English:
lemma nonempty_iff
  given: (X : Type*)
  proof: .nonempty_congr equiv _

中文:
引理 nonempty_iff
  条件: (X : 类型)
  证明: .nonempty_congr equiv _

Depends on / 依赖: nonempty_congr
-/
lemma nonempty_iff (X : Type*) :
    Nonempty (FundamentalGroupoid X) ↔ Nonempty X :=
.nonempty_congr equiv _

instance (X : Type*) [Nonempty X] :
    Nonempty (FundamentalGroupoid X) :=
.nonempty equiv _

@[simp]
/--
lemma `subsingleton_iff` / 引理 `subsingleton_iff`

English:
lemma subsingleton_iff
  given: (X : Type*)
  proof: .subsingleton_congr equiv _

中文:
引理 subsingleton_iff
  条件: (X : 类型)
  证明: .subsingleton_congr equiv _

Depends on / 依赖: subsingleton_congr
-/
lemma subsingleton_iff (X : Type*) :
    Subsingleton (FundamentalGroupoid X) ↔ Subsingleton X :=
.subsingleton_congr equiv _

instance (X : Type*) [Subsingleton X] :
    Subsingleton (FundamentalGroupoid X) :=
.subsingleton equiv _

-- TODO: It seems that `Equiv.nontrivial_congr` doesn't exist.
-- Once it is added, please add the corresponding lemma and instance.

instance {X : Type*} [Inhabited X] : Inhabited (FundamentalGroupoid X) :=
  ⟨⟨default⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Groupoid (FundamentalGroupoid X)
  body: Path.Homotopic.Quotient x.as y.as
  id x := ⟦Path.refl x.as⟧
  comp := Path.Homotopic.Quotient.trans
  id_comp := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨Path.Homotopy.reflTrans f⟩
  comp_id := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨Path.Homotopy.transRefl f⟩
  assoc := by rintro _ _ _ _ ⟨f⟩ ⟨g⟩ 

中文:
实例 :
  签名: Groupoid (FundamentalGroupoid X)
  定义体: Path.Homotopic.Quotient x.as y.as
  id x := ⟦Path.refl x.as⟧
  comp := Path.Homotopic.Quotient.trans
  id_comp := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨Path.Homotopy.reflTrans f⟩
  comp_id := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨Path.Homotopy.transRefl f⟩
  assoc := by rintro _ _ _ _ ⟨f⟩ ⟨g⟩ 

Depends on / 依赖: Homotopic, Path.Homotopic.Quotient, Quotient, x.as, y.as
-/
instance : Groupoid (FundamentalGroupoid X) where
  Hom x y := Path.Homotopic.Quotient x.as y.as
  id x := ⟦Path.refl x.as⟧
  comp := Path.Homotopic.Quotient.trans
  id_comp := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨Path.Homotopy.reflTrans f⟩
  comp_id := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨Path.Homotopy.transRefl f⟩
  assoc := by rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩; exact Quotient.sound ⟨Path.Homotopy.transAssoc f g h⟩
  inv := Quotient.lift (fun f => ⟦f.symm⟧) (by rintro a b ⟨h⟩; exact Quotient.sound ⟨h.symm₂⟩)
  inv_comp := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨(Path.Homotopy.reflSymmTrans f).symm⟩
  comp_inv := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨(Path.Homotopy.reflTransSymm f).symm⟩

/--
theorem `comp_eq` / 定理 `comp_eq`

English:
theorem comp_eq
  given: (x y z : FundamentalGroupoid X) (p : x ⟶ y) (q : y ⟶ z)
  statement: p ≫ q = p.trans q
  proof: rfl

中文:
定理 comp_eq
  条件: (x y z : FundamentalGroupoid X) (p : x ⟶ y) (q : y ⟶ z)
  结论: p ≫ q = p.trans q
  证明: rfl
-/
theorem comp_eq (x y z : FundamentalGroupoid X) (p : x ⟶ y) (q : y ⟶ z) : p ≫ q = p.trans q := rfl

/--
theorem `id_eq_path_refl` / 定理 `id_eq_path_refl`

English:
theorem id_eq_path_refl
  given: (x : FundamentalGroupoid X)
  statement: 𝟙 x = ⟦Path.refl x.as⟧
  proof: rfl

中文:
定理 id_eq_path_refl
  条件: (x : FundamentalGroupoid X)
  结论: 𝟙 x = ⟦Path.refl x.as⟧
  证明: rfl
-/
theorem id_eq_path_refl (x : FundamentalGroupoid X) : 𝟙 x = ⟦Path.refl x.as⟧ := rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : C(X, Y))
  body: ⟨f x.as⟩
  map p := p.map f
  map_id _ := rfl
  map_comp := by rintro _ _ _ ⟨p⟩ ⟨q⟩; exact congr_arg Quotient.mk'' (p.map_trans q f.continuous)

@[simp]

中文:
定义 map
  签名: (f : C(X, Y))
  定义体: ⟨f x.as⟩
  map p := p.map f
  map_id _ := rfl
  map_comp := by rintro _ _ _ ⟨p⟩ ⟨q⟩; exact congr_arg Quotient.mk'' (p.map_trans q f.continuous)

@[simp]
-/
@[simps] def map (f : C(X, Y)) : FundamentalGroupoid X ⥤ FundamentalGroupoid Y where
  obj x := ⟨f x.as⟩
  map p := p.map f
  map_id _ := rfl
  map_comp := by rintro _ _ _ ⟨p⟩ ⟨q⟩; exact congr_arg Quotient.mk'' (p.map_trans q f.continuous)

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (.id X) = 𝟭 _
  proof: by
  simp only [map]; congr; ext x y ⟨p⟩; rfl

@[simp]

中文:
定理 map_id
  结论: map (.id X) = 𝟭 _
  证明: by
  simp only [map]; congr; ext x y ⟨p⟩; rfl

@[simp]
-/
protected theorem map_id : map (.id X) = 𝟭 _ := by
  simp only [map]; congr; ext x y ⟨p⟩; rfl

@[simp]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: {Z : Type*} [TopologicalSpace Z] (g : C(Y, Z)) (f : C(X, Y))
  proof: by
  simp only [map]; congr; ext x y ⟨p⟩; rfl

中文:
定理 map_comp
  条件: {Z : 类型} [TopologicalSpace Z] (g : C(Y, Z)) (f : C(X, Y))
  证明: by
  simp only [map]; congr; ext x y ⟨p⟩; rfl
-/
protected theorem map_comp {Z : Type*} [TopologicalSpace Z] (g : C(Y, Z)) (f : C(X, Y)) :
    map (g.comp f) = map f ⋙ map g := by
  simp only [map]; congr; ext x y ⟨p⟩; rfl

/--
Definition of `fundamentalGroupoidFunctor` / `fundamentalGroupoidFunctor` 的定义

English:
definition fundamentalGroupoidFunctor
  signature: : TopCat ⥤ Grpd where
  body: { α := FundamentalGroupoid X }
  map f := map f.hom
  map_id _ := FundamentalGroupoid.map_id
  map_comp _ _ := FundamentalGroupoid.map_comp _ _

@[inherit_doc] scoped notation "π" => FundamentalGroupoid.fundamentalGroupoidFunctor

中文:
定义 fundamentalGroupoidFunctor
  签名: : TopCat ⥤ Grpd where
  定义体: { α := FundamentalGroupoid X }
  map f := map f.hom
  map_id _ := FundamentalGroupoid.map_id
  map_comp _ _ := FundamentalGroupoid.map_comp _ _

@[inherit_doc] scoped notation "π" => FundamentalGroupoid.fundamentalGroupoidFunctor

Depends on / 依赖: FundamentalGroupoid
-/
def fundamentalGroupoidFunctor : TopCat ⥤ Grpd where
  obj X := { α := FundamentalGroupoid X }
  map f := map f.hom
  map_id _ := FundamentalGroupoid.map_id
  map_comp _ _ := FundamentalGroupoid.map_comp _ _

@[inherit_doc] scoped notation "π" => FundamentalGroupoid.fundamentalGroupoidFunctor

/-- The fundamental groupoid of a topological space. -/
scoped notation "πₓ" => FundamentalGroupoid.fundamentalGroupoidFunctor.obj

/-- The functor between fundamental groupoids induced by a continuous map. -/
scoped notation "πₘ" => FundamentalGroupoid.fundamentalGroupoidFunctor.map

/--
theorem `map_eq` / 定理 `map_eq`

English:
theorem map_eq
  given: {X Y : TopCat.{u}} {x₀ x₁ : X} (f : C(X, Y)) (p : Path.Homotopic.Quotient x₀ x₁)
  proof: rfl

中文:
定理 map_eq
  条件: {X Y : TopCat.{u}} {x₀ x₁ : X} (f : C(X, Y)) (p : Path.Homotopic.Quotient x₀ x₁)
  证明: rfl
-/
theorem map_eq {X Y : TopCat.{u}} {x₀ x₁ : X} (f : C(X, Y)) (p : Path.Homotopic.Quotient x₀ x₁) :
    (πₘ (TopCat.ofHom f)).map p = p.map f := rfl

/--
Definition of `toTop` / `toTop` 的定义

English:
abbreviation toTop
  signature: {X : TopCat.{u}} (x : πₓ X)
  body: x.as

中文:
缩写 toTop
  签名: {X : TopCat.{u}} (x : πₓ X)
  定义体: x.as

Depends on / 依赖: x.as
-/
abbrev toTop {X : TopCat.{u}} (x : πₓ X) : X := x.as

/--
Definition of `fromTop` / `fromTop` 的定义

English:
abbreviation fromTop
  signature: {X : TopCat.{u}} (x : X)
  body: ⟨x⟩

中文:
缩写 fromTop
  签名: {X : TopCat.{u}} (x : X)
  定义体: ⟨x⟩
-/
abbrev fromTop {X : TopCat.{u}} (x : X) : πₓ X := ⟨x⟩

/--
Definition of `toPath` / `toPath` 的定义

English:
abbreviation toPath
  signature: {X : TopCat.{u}} {x₀ x₁ : πₓ X} (p : x₀ ⟶ x₁)
  body: p

中文:
缩写 toPath
  签名: {X : TopCat.{u}} {x₀ x₁ : πₓ X} (p : x₀ ⟶ x₁)
  定义体: p
-/
abbrev toPath {X : TopCat.{u}} {x₀ x₁ : πₓ X} (p : x₀ ⟶ x₁) :
    Path.Homotopic.Quotient x₀.as x₁.as :=
  p

/--
Definition of `fromPath` / `fromPath` 的定义

English:
abbreviation fromPath
  signature: {x₀ x₁ : X} (p : Path.Homotopic.Quotient x₀ x₁)
  body: p

中文:
缩写 fromPath
  签名: {x₀ x₁ : X} (p : Path.Homotopic.Quotient x₀ x₁)
  定义体: p
-/
abbrev fromPath {x₀ x₁ : X} (p : Path.Homotopic.Quotient x₀ x₁) :
    FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x₁ := p

/--
theorem `fromPath_eq_iff_homotopic` / 定理 `fromPath_eq_iff_homotopic`

English:
theorem fromPath_eq_iff_homotopic
  given: {x₀ x₁ : X} (f : Path x₀ x₁) (g : Path x₀ x₁)
  proof: ⟨fun ih => Quotient.exact ih, fun h => Quotient.sound h⟩

中文:
定理 fromPath_eq_iff_homotopic
  条件: {x₀ x₁ : X} (f : Path x₀ x₁) (g : Path x₀ x₁)
  证明: ⟨fun ih => Quotient.exact ih, fun h => Quotient.sound h⟩

Depends on / 依赖: Quotient, Quotient.exact, Quotient.sound
-/
theorem fromPath_eq_iff_homotopic {x₀ x₁ : X} (f : Path x₀ x₁) (g : Path x₀ x₁) :
    fromPath (Path.Homotopic.Quotient.mk f) = fromPath (Path.Homotopic.Quotient.mk g) ↔
      f.Homotopic g :=
  ⟨fun ih => Quotient.exact ih, fun h => Quotient.sound h⟩

/--
lemma `eqToHom_eq` / 引理 `eqToHom_eq`

English:
lemma eqToHom_eq
  given: {x₀ x₁ : X} (h : x₀ = x₁)
  proof: by subst h; rfl

@[reassoc]

中文:
引理 eqToHom_eq
  条件: {x₀ x₁ : X} (h : x₀ = x₁)
  证明: by subst h; rfl

@[reassoc]
-/
lemma eqToHom_eq {x₀ x₁ : X} (h : x₀ = x₁) :
    eqToHom congr(mk $h) = (Path.Homotopic.Quotient.refl x₁).cast h rfl := by subst h; rfl

@[reassoc]
/--
lemma `conj_eqToHom` / 引理 `conj_eqToHom`

English:
lemma conj_eqToHom
  given: {x y x' y' : X} {p : Path.Homotopic.Quotient x y} (hx : x' = x) (hy : y' = y)
  proof: by
  subst hx hy; simp

中文:
引理 conj_eqToHom
  条件: {x y x' y' : X} {p : Path.Homotopic.Quotient x y} (hx : x' = x) (hy : y' = y)
  证明: by
  subst hx hy; simp
-/
lemma conj_eqToHom {x y x' y' : X} {p : Path.Homotopic.Quotient x y} (hx : x' = x) (hy : y' = y) :
    eqToHom congr(mk $hx) ≫ p ≫ eqToHom congr(mk $hy.symm) = p.cast hx hy := by
  subst hx hy; simp

end FundamentalGroupoid
