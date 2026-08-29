/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism

/-!
# Pointed simplices

Given a simplicial set `X`, `n : ℕ` and `x : X _⦋0⦌`, we introduce the
type `X.PtSimplex n x` of morphisms `Δ[n] ⟶ X` which send `∂Δ[n]` to `x`.
We introduce structures `PtSimplex.RelStruct` and `PtSimplex.MulStruct`
which will be used in the definition of homotopy groups of Kan complexes.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial
namespace SSet

variable (X : SSet.{u})

/--
Definition of `PtSimplex` / `PtSimplex` 的定义

English:
abbreviation PtSimplex
  signature: (n : Nat) (x : X _⦋0⦌)
  body: RelativeMorphism (boundary n) (Subcomplex.ofSimplex x)
    (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

中文:
缩写 PtSimplex
  签名: (n : 自然数) (x : X _⦋0⦌)
  定义体: RelativeMorphism (boundary n) (Subcomplex.ofSimplex x)
    (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

Depends on / 依赖: RelativeMorphism, Subcomplex, Subcomplex.mem_ofSimplex_obj, Subcomplex.ofSimplex, boundary, mem_ofSimplex_obj, ofSimplex
-/
abbrev PtSimplex (n : Nat) (x : X _⦋0⦌) : Type u :=
  RelativeMorphism (boundary n) (Subcomplex.ofSimplex x)
    (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

namespace PtSimplex

variable {X} {n : Nat} {x : X _⦋0⦌}

@[reassoc]
/--
lemma `comp_map_eq_const` / 引理 `comp_map_eq_const`

English:
lemma comp_map_eq_const
  proof: by
  refine (Subcomplex.lift φ ?_) ≫= s.comm
  rw [stdSimplex.le_boundary_iff]
  intro h
  have : IsIso (Subcomplex.range φ).ι := by rw [h]; infer_instance
  exact stdSimplex.not_hasDimensionLT n
    ((hasDimensionLT_iff_of_iso (asIso (Subcomplex.range φ).ι) n).mp inferInstance)

@[reassoc (attr := simp)]

中文:
引理 comp_map_eq_const
  证明: by
  refine (Subcomplex.lift φ ?_) ≫= s.comm
  rw [stdSimplex.le_boundary_iff]
  intro h
  have : IsIso (Subcomplex.range φ).ι := by rw [h]; infer_instance
  exact stdSimplex.not_hasDimensionLT n
    ((hasDimensionLT_iff_of_iso (asIso (Subcomplex.range φ).ι) n).mp inferInstance)

@[reassoc (attr := simp)]

Depends on / 依赖: Subcomplex, Subcomplex.lift, Subcomplex.range, hasDimensionLT_iff_of_iso, infer_instance, le_boundary_iff, not_hasDimensionLT, s.comm, stdSimplex, stdSimplex.le_boundary_iff, stdSimplex.not_hasDimensionLT
-/
lemma comp_map_eq_const
    (s : X.PtSimplex n x) {Y : SSet.{u}} (φ : Y ⟶ Δ[n]) [Y.HasDimensionLT n] :
    φ ≫ s.map = const x := by
  refine (Subcomplex.lift φ ?_) ≫= s.comm
  rw [stdSimplex.le_boundary_iff]
  intro h
  have : IsIso (Subcomplex.range φ).ι := by rw [h]; infer_instance
  exact stdSimplex.not_hasDimensionLT n
    ((hasDimensionLT_iff_of_iso (asIso (Subcomplex.range φ).ι) n).mp inferInstance)

@[reassoc (attr := simp)]
/--
lemma `δ_map` / 引理 `δ_map`

English:
lemma δ_map
  given: (f : X.PtSimplex (n + 1) x) (i : Fin (n + 2))
  proof: comp_map_eq_const _ _

中文:
引理 δ_map
  条件: (f : X.PtSimplex (n + 1) x) (i : 有限集 (n + 2))
  证明: comp_map_eq_const _ _

Depends on / 依赖: comp_map_eq_const
-/
lemma δ_map (f : X.PtSimplex (n + 1) x) (i : Fin (n + 2)) :
    stdSimplex.δ i ≫ f.map = const x :=
  comp_map_eq_const _ _

/-- The bijection between `n`-simplices of `X.op` and of `X`
that are constant on the boundary. -/
@[simps]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: : X.op.PtSimplex n (opObjEquiv.symm x) ≃ X.PtSimplex n x where
  body: { map := yonedaEquiv.symm (opObjEquiv (yonedaEquiv f.map))
      comm := by
        obtain _ | n := n
        · ext
        · refine boundary.hom_ext (fun i => ?_)
          simp [stdSimplex.δ_comp_yonedaEquiv_symm,
            δ_opObjEquiv, ← stdSimplex.yonedaEquiv_δ_comp,
            opObjEquiv_yonedaEquiv_const] }
  invFun g :=
    { map := yonedaEquiv.symm (opObjEquiv.symm (yonedaEquiv g.map))
      comm := by
        obtain _ | n := n
        · ext
        · refine boundary.hom_ext (fun i => ?_)
          simp [stdSimplex.δ_comp_yonedaEquiv_symm, op_δ,
            ← stdSimplex.yonedaEquiv_δ_comp,
            opObjEquiv_symm_yonedaEquiv_const] }
  left_inv _ := by simp
  right_inv _ := by simp

中文:
定义 opEquiv
  签名: : X.op.PtSimplex n (opObjEquiv.symm x) ≃ X.PtSimplex n x where
  定义体: { map := yonedaEquiv.symm (opObjEquiv (yonedaEquiv f.map))
      comm := by
        obtain _ | n := n
        · ext
        · refine boundary.hom_ext (fun i => ?_)
          simp [stdSimplex.δ_comp_yonedaEquiv_symm,
            δ_opObjEquiv, ← stdSimplex.yonedaEquiv_δ_comp,
            opObjEquiv_yonedaEquiv_const] }
  invFun g :=
    { map := yonedaEquiv.symm (opObjEquiv.symm (yonedaEquiv g.map))
      comm := by
        obtain _ | n := n
        · ext
        · refine boundary.hom_ext (fun i => ?_)
          simp [stdSimplex.δ_comp_yonedaEquiv_symm, op_δ,
            ← stdSimplex.yonedaEquiv_δ_comp,
            opObjEquiv_symm_yonedaEquiv_const] }
  left_inv _ := by simp
  right_inv _ := by simp

Depends on / 依赖: boundary, boundary.hom_ext, f.map, g.map, hom_ext, invFun, opObjEquiv, opObjEquiv.symm, opObjEquiv_sy, opObjEquiv_yonedaEquiv_const, stdSimplex, stdSimplex.yonedaEquiv_, yonedaEquiv, yonedaEquiv.symm
-/
def opEquiv : X.op.PtSimplex n (opObjEquiv.symm x) ≃ X.PtSimplex n x where
  toFun f :=
    { map := yonedaEquiv.symm (opObjEquiv (yonedaEquiv f.map))
      comm := by
        obtain _ | n := n
        · ext
        · refine boundary.hom_ext (fun i => ?_)
          simp [stdSimplex.δ_comp_yonedaEquiv_symm,
            δ_opObjEquiv, ← stdSimplex.yonedaEquiv_δ_comp,
            opObjEquiv_yonedaEquiv_const] }
  invFun g :=
    { map := yonedaEquiv.symm (opObjEquiv.symm (yonedaEquiv g.map))
      comm := by
        obtain _ | n := n
        · ext
        · refine boundary.hom_ext (fun i => ?_)
          simp [stdSimplex.δ_comp_yonedaEquiv_symm, op_δ,
            ← stdSimplex.yonedaEquiv_δ_comp,
            opObjEquiv_symm_yonedaEquiv_const] }
  left_inv _ := by simp
  right_inv _ := by simp

/--
Definition of `op` / `op` 的定义

English:
abbreviation op
  signature: (f : X.PtSimplex n x)
  body: opEquiv.symm f

中文:
缩写 op
  签名: (f : X.PtSimplex n x)
  定义体: opEquiv.symm f

Depends on / 依赖: opEquiv, opEquiv.symm
-/
abbrev op (f : X.PtSimplex n x) : X.op.PtSimplex n (opObjEquiv.symm x) :=
  opEquiv.symm f

/--
Definition of `unop` / `unop` 的定义

English:
abbreviation unop
  signature: (f : X.op.PtSimplex n (opObjEquiv.symm x))
  body: opEquiv f

中文:
缩写 unop
  签名: (f : X.op.PtSimplex n (opObjEquiv.symm x))
  定义体: opEquiv f

Depends on / 依赖: opEquiv
-/
abbrev unop (f : X.op.PtSimplex n (opObjEquiv.symm x)) : X.PtSimplex n x :=
  opEquiv f

/--
Definition of `RelStruct` / `RelStruct` 的定义

English:
structure RelStruct
  parameters: (f g : X.PtSimplex n x) (i : Fin (n + 1))
  axioms and operations (5):
    - map : Δ[n + 1] ⟶ X
    - δ_castSucc_map : stdSimplex.δ i.castSucc ≫ map = f.map  [default: by cat_disch]
    - δ_succ_map : stdSimplex.δ i.succ ≫ map = g.map  [default: by cat_disch]
    - δ_map_of_lt((j : Fin (n + 2)) (hj : j < i.castSucc)) : stdSimplex.δ j ≫ map = const x  [default: by cat_disch]
    - δ_map_of_gt((j : Fin (n + 2)) (hj : i.succ < j)) : stdSimplex.δ j ≫ map = const x  [default: by cat_disch]

中文:
结构 RelStruct
  参数: (f g : X.PtSimplex n x) (i : 有限集 (n + 1))
  公理与运算 (5 个):
    - map : Δ[n + 1] ⟶ X
    - δ_castSucc_map : stdSimplex.δ i.castSucc ≫ map = f.map  [默认: by cat_disch]
    - δ_succ_map : stdSimplex.δ i.succ ≫ map = g.map  [默认: by cat_disch]
    - δ_map_of_lt((j : 有限集 (n + 2)) (hj : j < i.castSucc)) : stdSimplex.δ j ≫ map = const x  [默认: by cat_disch]
    - δ_map_of_gt((j : 有限集 (n + 2)) (hj : i.succ < j)) : stdSimplex.δ j ≫ map = const x  [默认: by cat_disch]

Depends on / 依赖: castSucc, cat_disch, g.map, i.castSucc, i.succ, stdSimplex
-/
structure RelStruct (f g : X.PtSimplex n x) (i : Fin (n + 1)) where
  /-- A `n + 1`-simplex -/
  map : Δ[n + 1] ⟶ X
  δ_castSucc_map : stdSimplex.δ i.castSucc ≫ map = f.map := by cat_disch
  δ_succ_map : stdSimplex.δ i.succ ≫ map = g.map := by cat_disch
  δ_map_of_lt (j : Fin (n + 2)) (hj : j < i.castSucc) :
    stdSimplex.δ j ≫ map = const x := by cat_disch
  δ_map_of_gt (j : Fin (n + 2)) (hj : i.succ < j) :
    stdSimplex.δ j ≫ map = const x := by cat_disch

namespace RelStruct

attribute [reassoc (attr := simp)] δ_castSucc_map δ_succ_map
  δ_map_of_lt δ_map_of_gt

/-- `RelStruct` is reflexive. -/
@[simps]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (f : X.PtSimplex n x) (i : Fin (n + 1))
  body: stdSimplex.σ i ≫ f.map
  δ_castSucc_map := by rw [CosimplicialObject.δ_comp_σ_self_assoc]
  δ_succ_map := by rw [CosimplicialObject.δ_comp_σ_succ_assoc]
  δ_map_of_lt j hj := by
    obtain ⟨i, rfl⟩ := i.eq_succ_of_ne_zero (by aesop)
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (by grind)
    obtain _ | n := n
    · fin_cases i
    · rw [stdSimplex.δ_comp_σ_of_le_assoc (by grind), δ_map, comp_const]
  δ_map_of_gt j hj := by
    obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (by grind)
    obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (by aesop)
    obtain _ | n := n
    · fin_cases i
    · rw [stdSimplex.δ_comp_σ_of_gt_assoc (by grind), δ_map, comp_const]

中文:
定义 refl
  签名: (f : X.PtSimplex n x) (i : 有限集 (n + 1))
  定义体: stdSimplex.σ i ≫ f.map
  δ_castSucc_map := by rw [CosimplicialObject.δ_comp_σ_self_assoc]
  δ_succ_map := by rw [CosimplicialObject.δ_comp_σ_succ_assoc]
  δ_map_of_lt j hj := by
    obtain ⟨i, rfl⟩ := i.eq_succ_of_ne_zero (by aesop)
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (by grind)
    obtain _ | n := n
    · fin_cases i
    · rw [stdSimplex.δ_comp_σ_of_le_assoc (by grind), δ_map, comp_const]
  δ_map_of_gt j hj := by
    obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (by grind)
    obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (by aesop)
    obtain _ | n := n
    · fin_cases i
    · rw [stdSimplex.δ_comp_σ_of_gt_assoc (by grind), δ_map, comp_const]

Depends on / 依赖: f.map, stdSimplex
-/
def refl (f : X.PtSimplex n x) (i : Fin (n + 1)) : RelStruct f f i where
  map := stdSimplex.σ i ≫ f.map
  δ_castSucc_map := by rw [CosimplicialObject.δ_comp_σ_self_assoc]
  δ_succ_map := by rw [CosimplicialObject.δ_comp_σ_succ_assoc]
  δ_map_of_lt j hj := by
    obtain ⟨i, rfl⟩ := i.eq_succ_of_ne_zero (by aesop)
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (by grind)
    obtain _ | n := n
    · fin_cases i
    · rw [stdSimplex.δ_comp_σ_of_le_assoc (by grind), δ_map, comp_const]
  δ_map_of_gt j hj := by
    obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (by grind)
    obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (by aesop)
    obtain _ | n := n
    · fin_cases i
    · rw [stdSimplex.δ_comp_σ_of_gt_assoc (by grind), δ_map, comp_const]

/-- The `RelStruct f' g' i` deduced from `r : RelStruct f g i` when
`f = f'` and `g = g'`. -/
@[simps]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: {f g : X.PtSimplex n x} {i : Fin (n + 1)} (r : RelStruct f g i)
  body: r.map
  δ_castSucc_map := by rw [δ_castSucc_map, hf]
  δ_succ_map := by rw [δ_succ_map, hg]
  δ_map_of_lt j hj := by rw [δ_map_of_lt _ j hj]
  δ_map_of_gt j hj := by rw [δ_map_of_gt _ j hj]

中文:
定义 copy
  签名: {f g : X.PtSimplex n x} {i : 有限集 (n + 1)} (r : RelStruct f g i)
  定义体: r.map
  δ_castSucc_map := by rw [δ_castSucc_map, hf]
  δ_succ_map := by rw [δ_succ_map, hg]
  δ_map_of_lt j hj := by rw [δ_map_of_lt _ j hj]
  δ_map_of_gt j hj := by rw [δ_map_of_gt _ j hj]

Depends on / 依赖: r.map
-/
def copy {f g : X.PtSimplex n x} {i : Fin (n + 1)} (r : RelStruct f g i)
    {f' g' : X.PtSimplex n x} (hf : f = f') (hg : g = g') :
    RelStruct f' g' i where
  map := r.map
  δ_castSucc_map := by rw [δ_castSucc_map, hf]
  δ_succ_map := by rw [δ_succ_map, hg]
  δ_map_of_lt j hj := by rw [δ_map_of_lt _ j hj]
  δ_map_of_gt j hj := by rw [δ_map_of_gt _ j hj]

/-- The `RelStruct f g i` deduced from an equality `f = g`. -/
@[simps! map]
/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: {f g : X.PtSimplex n x} (h : f = g) (i : Fin (n + 1))
  body: (refl f i).copy rfl h

中文:
定义 ofEq
  签名: {f g : X.PtSimplex n x} (h : f = g) (i : 有限集 (n + 1))
  定义体: (refl f i).copy rfl h
-/
def ofEq {f g : X.PtSimplex n x} (h : f = g) (i : Fin (n + 1)) :
    RelStruct f g i :=
  (refl f i).copy rfl h

end RelStruct

/--
Definition of `MulStruct` / `MulStruct` 的定义

English:
structure MulStruct
  parameters: (f g fg : X.PtSimplex n x) (i : Fin n)
  axioms and operations (6):
    - map : Δ[n + 1] ⟶ X
    - δ_castSucc_castSucc_map : stdSimplex.δ (i.castSucc.castSucc) ≫ map = g.map  [default: by cat_disch]
    - δ_succ_castSucc_map : stdSimplex.δ (i.castSucc.succ) ≫ map = fg.map  [default: by cat_disch]
    - δ_succ_succ_map : stdSimplex.δ (i.succ.succ) ≫ map = f.map  [default: by cat_disch]
    - δ_map_of_lt((j : Fin (n + 2)) (hj : j < i.castSucc.castSucc)) : stdSimplex.δ j ≫ map = const x  [default: by cat_disch]
    - δ_map_of_gt((j : Fin (n + 2)) (hj : i.succ.succ < j)) : stdSimplex.δ j ≫ map = const x  [default: by cat_disch]

中文:
结构 MulStruct
  参数: (f g fg : X.PtSimplex n x) (i : 有限集 n)
  公理与运算 (6 个):
    - map : Δ[n + 1] ⟶ X
    - δ_castSucc_castSucc_map : stdSimplex.δ (i.castSucc.castSucc) ≫ map = g.map  [默认: by cat_disch]
    - δ_succ_castSucc_map : stdSimplex.δ (i.castSucc.succ) ≫ map = fg.map  [默认: by cat_disch]
    - δ_succ_succ_map : stdSimplex.δ (i.succ.succ) ≫ map = f.map  [默认: by cat_disch]
    - δ_map_of_lt((j : 有限集 (n + 2)) (hj : j < i.castSucc.castSucc)) : stdSimplex.δ j ≫ map = const x  [默认: by cat_disch]
    - δ_map_of_gt((j : 有限集 (n + 2)) (hj : i.succ.succ < j)) : stdSimplex.δ j ≫ map = const x  [默认: by cat_disch]

Depends on / 依赖: castSucc, cat_disch, f.map, fg.map, i.castSucc.castSucc, i.castSucc.succ, i.succ.succ, stdSimplex
-/
structure MulStruct (f g fg : X.PtSimplex n x) (i : Fin n) where
  /-- A `n + 1`-simplex -/
  map : Δ[n + 1] ⟶ X
  δ_castSucc_castSucc_map : stdSimplex.δ (i.castSucc.castSucc) ≫ map = g.map := by cat_disch
  δ_succ_castSucc_map : stdSimplex.δ (i.castSucc.succ) ≫ map = fg.map := by cat_disch
  δ_succ_succ_map : stdSimplex.δ (i.succ.succ) ≫ map = f.map := by cat_disch
  δ_map_of_lt (j : Fin (n + 2)) (hj : j < i.castSucc.castSucc) :
    stdSimplex.δ j ≫ map = const x := by cat_disch
  δ_map_of_gt (j : Fin (n + 2)) (hj : i.succ.succ < j) :
    stdSimplex.δ j ≫ map = const x := by cat_disch

namespace MulStruct

attribute [reassoc (attr := simp)] δ_castSucc_castSucc_map δ_succ_castSucc_map δ_succ_succ_map
  δ_map_of_lt δ_map_of_gt

/-- The `MulStruct` for `X.op` that is deduced from a `MulStruct` for the simplicial
set `X`. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: {f g fg : X.PtSimplex n x} {i : Fin n} (h : MulStruct f g fg i) {j : Fin n}
  body: yonedaEquiv.symm (opObjEquiv.symm (yonedaEquiv h.map))
  δ_castSucc_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]; rw [op_δ]; rw [Equiv.apply_symm_apply]; rw [← stdSimplex.yonedaEquiv_δ_comp]; rw [opEquiv_symm_apply_map]; rw [← h.δ_succ_succ_map]; rw [Fin.rev_castSucc]; rw [Fin.rev_castSucc]; rw [← hij]; rw [Fin.rev_rev]
  δ_succ_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]; rw [op_δ]; rw [Equiv.apply_symm_apply]; rw [← stdSimplex.yonedaEquiv_δ_comp]; rw [opEquiv_symm_apply_map]; rw [← h.δ_succ_castSucc_map]; rw [Fin.rev_succ]; rw [Fin.rev_castSucc]; rw [Fin.castSucc_succ]; rw [← hij]; rw [Fin.rev_rev]
  δ_succ_succ_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]; rw [op_δ]; rw [Equiv.apply_symm_apply]; rw [← stdSimplex.yonedaEquiv_δ_comp]; rw [opEquiv_symm_apply_map]; rw [← h.δ_castSucc_castSucc_map]; rw [Fin.rev_succ]; rw [Fin.rev_succ]; rw [← hij]; rw [Fin.rev_rev]
  δ_map_of_lt k hk := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, ← stdSimplex.yonedaEquiv_δ_comp,
      opObjEquiv_symm_yonedaEquiv_const, h.δ_map_of_gt k.rev (by grind)]
  δ_map_of_gt k hk := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, ← stdSimplex.yonedaEquiv_δ_comp,
      opObjEquiv_symm_yonedaEquiv_const, h.δ_map_of_lt k.rev (by grind)]

中文:
定义 op
  签名: {f g fg : X.PtSimplex n x} {i : 有限集 n} (h : MulStruct f g fg i) {j : 有限集 n}
  定义体: yonedaEquiv.symm (opObjEquiv.symm (yonedaEquiv h.map))
  δ_castSucc_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]; rw [op_δ]; rw [Equiv.apply_symm_apply]; rw [← stdSimplex.yonedaEquiv_δ_comp]; rw [opEquiv_symm_apply_map]; rw [← h.δ_succ_succ_map]; rw [Fin.rev_castSucc]; rw [Fin.rev_castSucc]; rw [← hij]; rw [Fin.rev_rev]
  δ_succ_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]; rw [op_δ]; rw [Equiv.apply_symm_apply]; rw [← stdSimplex.yonedaEquiv_δ_comp]; rw [opEquiv_symm_apply_map]; rw [← h.δ_succ_castSucc_map]; rw [Fin.rev_succ]; rw [Fin.rev_castSucc]; rw [Fin.castSucc_succ]; rw [← hij]; rw [Fin.rev_rev]
  δ_succ_succ_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]; rw [op_δ]; rw [Equiv.apply_symm_apply]; rw [← stdSimplex.yonedaEquiv_δ_comp]; rw [opEquiv_symm_apply_map]; rw [← h.δ_castSucc_castSucc_map]; rw [Fin.rev_succ]; rw [Fin.rev_succ]; rw [← hij]; rw [Fin.rev_rev]
  δ_map_of_lt k hk := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, ← stdSimplex.yonedaEquiv_δ_comp,
      opObjEquiv_symm_yonedaEquiv_const, h.δ_map_of_gt k.rev (by grind)]
  δ_map_of_gt k hk := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, ← stdSimplex.yonedaEquiv_δ_comp,
      opObjEquiv_symm_yonedaEquiv_const, h.δ_map_of_lt k.rev (by grind)]

Depends on / 依赖: Equiv.apply_symm_apply, Fin.rev_castSucc, Fin.rev_rev, MulStruct, apply_symm_apply, f.op, fg.op, g.op, h.map, opEquiv_symm_apply_map, opObjEquiv, opObjEquiv.symm, rev_castSucc, rev_rev, stdSimplex, stdSimplex.yonedaEquiv_, yonedaEquiv, yonedaEquiv.symm
-/
def op {f g fg : X.PtSimplex n x} {i : Fin n} (h : MulStruct f g fg i) {j : Fin n}
    (hij : i.rev = j := by grind) :
    MulStruct g.op f.op fg.op j where
  map := yonedaEquiv.symm (opObjEquiv.symm (yonedaEquiv h.map))
  δ_castSucc_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]; rw [op_δ]; rw [Equiv.apply_symm_apply]; rw [← stdSimplex.yonedaEquiv_δ_comp]; rw [opEquiv_symm_apply_map]; rw [← h.δ_succ_succ_map]; rw [Fin.rev_castSucc]; rw [Fin.rev_castSucc]; rw [← hij]; rw [Fin.rev_rev]
  δ_succ_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]; rw [op_δ]; rw [Equiv.apply_symm_apply]; rw [← stdSimplex.yonedaEquiv_δ_comp]; rw [opEquiv_symm_apply_map]; rw [← h.δ_succ_castSucc_map]; rw [Fin.rev_succ]; rw [Fin.rev_castSucc]; rw [Fin.castSucc_succ]; rw [← hij]; rw [Fin.rev_rev]
  δ_succ_succ_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]; rw [op_δ]; rw [Equiv.apply_symm_apply]; rw [← stdSimplex.yonedaEquiv_δ_comp]; rw [opEquiv_symm_apply_map]; rw [← h.δ_castSucc_castSucc_map]; rw [Fin.rev_succ]; rw [Fin.rev_succ]; rw [← hij]; rw [Fin.rev_rev]
  δ_map_of_lt k hk := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, ← stdSimplex.yonedaEquiv_δ_comp,
      opObjEquiv_symm_yonedaEquiv_const, h.δ_map_of_gt k.rev (by grind)]
  δ_map_of_gt k hk := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, ← stdSimplex.yonedaEquiv_δ_comp,
      opObjEquiv_symm_yonedaEquiv_const, h.δ_map_of_lt k.rev (by grind)]

/-- The `Mulstruct` for a simplicial set `X` that is deduced from a `Mulstruct` for `X.op`. -/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {f g fg : X.PtSimplex n x} {i : Fin n} (h : MulStruct g.op f.op fg.op i) {j : Fin n}
  body: yonedaEquiv.symm (opObjEquiv (yonedaEquiv h.map))
  δ_castSucc_castSucc_map := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, ← hij, Fin.rev_castSucc]
  δ_succ_castSucc_map := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, ← hij, Fin.rev_castSucc, Fin.rev_succ]
  δ_succ_succ_map := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, ← hij, Fin.rev_succ]
  δ_map_of_lt k hk := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]; rw [δ_opObjEquiv]; rw [← stdSimplex.yonedaEquiv_δ_comp]; rw [h.δ_map_of_gt _ (by grind)]
    simp [opObjEquiv_yonedaEquiv_const]
  δ_map_of_gt k hk := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]; rw [δ_opObjEquiv]; rw [← stdSimplex.yonedaEquiv_δ_comp]; rw [h.δ_map_of_lt _ (by grind)]
    simp [opObjEquiv_yonedaEquiv_const]

中文:
定义 unop
  签名: {f g fg : X.PtSimplex n x} {i : 有限集 n} (h : MulStruct g.op f.op fg.op i) {j : 有限集 n}
  定义体: yonedaEquiv.symm (opObjEquiv (yonedaEquiv h.map))
  δ_castSucc_castSucc_map := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, ← hij, Fin.rev_castSucc]
  δ_succ_castSucc_map := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, ← hij, Fin.rev_castSucc, Fin.rev_succ]
  δ_succ_succ_map := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, ← hij, Fin.rev_succ]
  δ_map_of_lt k hk := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]; rw [δ_opObjEquiv]; rw [← stdSimplex.yonedaEquiv_δ_comp]; rw [h.δ_map_of_gt _ (by grind)]
    simp [opObjEquiv_yonedaEquiv_const]
  δ_map_of_gt k hk := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]; rw [δ_opObjEquiv]; rw [← stdSimplex.yonedaEquiv_δ_comp]; rw [h.δ_map_of_lt _ (by grind)]
    simp [opObjEquiv_yonedaEquiv_const]

Depends on / 依赖: Fin.rev_castSucc, Fin.rev_succ, MulStruct, h.map, opObjEquiv, rev_castSucc, rev_succ, stdSimplex, stdSimplex.yonedaEquiv_, yonedaEquiv, yonedaEquiv.symm
-/
def unop {f g fg : X.PtSimplex n x} {i : Fin n} (h : MulStruct g.op f.op fg.op i) {j : Fin n}
    (hij : i.rev = j := by grind) :
    MulStruct f g fg j where
  map := yonedaEquiv.symm (opObjEquiv (yonedaEquiv h.map))
  δ_castSucc_castSucc_map := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, ← hij, Fin.rev_castSucc]
  δ_succ_castSucc_map := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, ← hij, Fin.rev_castSucc, Fin.rev_succ]
  δ_succ_succ_map := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, ← hij, Fin.rev_succ]
  δ_map_of_lt k hk := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]; rw [δ_opObjEquiv]; rw [← stdSimplex.yonedaEquiv_δ_comp]; rw [h.δ_map_of_gt _ (by grind)]
    simp [opObjEquiv_yonedaEquiv_const]
  δ_map_of_gt k hk := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]; rw [δ_opObjEquiv]; rw [← stdSimplex.yonedaEquiv_δ_comp]; rw [h.δ_map_of_lt _ (by grind)]
    simp [opObjEquiv_yonedaEquiv_const]

end MulStruct

/-- If `f` and `g` are in `X.PtSimplex n x`, then `RelStruct f g i.castSucc`
identifies to `MulStruct .const f g i`. -/
@[simps apply_map symm_apply_map]
/--
Definition of `relStructCastSuccEquivMulStruct` / `relStructCastSuccEquivMulStruct` 的定义

English:
definition relStructCastSuccEquivMulStruct
  signature: {f g : X.PtSimplex n x} {i : Fin n}
  body: { map := h.map
      δ_map_of_gt j hj := h.δ_map_of_gt j (lt_trans (by simp) hj) }
  invFun h :=
    { map := h.map
      δ_map_of_gt j hj := by
        rw [Fin.succ_castSucc]; rw [Fin.castSucc_lt_iff_succ_le] at hj
        obtain rfl | hj := hj.eq_or_lt
        exacts [h.δ_succ_succ_map, h.δ_map_of_gt j hj] }

中文:
定义 relStructCastSuccEquivMulStruct
  签名: {f g : X.PtSimplex n x} {i : 有限集 n}
  定义体: { map := h.map
      δ_map_of_gt j hj := h.δ_map_of_gt j (lt_trans (by simp) hj) }
  invFun h :=
    { map := h.map
      δ_map_of_gt j hj := by
        rw [Fin.succ_castSucc]; rw [Fin.castSucc_lt_iff_succ_le] at hj
        obtain rfl | hj := hj.eq_or_lt
        exacts [h.δ_succ_succ_map, h.δ_map_of_gt j hj] }

Depends on / 依赖: Fin.castSucc_lt_iff_succ_le, Fin.succ_castSucc, castSucc_lt_iff_succ_le, eq_or_lt, exacts, h.map, hj.eq_or_lt, invFun, lt_trans, succ_castSucc
-/
def relStructCastSuccEquivMulStruct {f g : X.PtSimplex n x} {i : Fin n} :
    RelStruct f g i.castSucc ≃ MulStruct .const f g i where
  toFun h :=
    { map := h.map
      δ_map_of_gt j hj := h.δ_map_of_gt j (lt_trans (by simp) hj) }
  invFun h :=
    { map := h.map
      δ_map_of_gt j hj := by
        rw [Fin.succ_castSucc]; rw [Fin.castSucc_lt_iff_succ_le] at hj
        obtain rfl | hj := hj.eq_or_lt
        exacts [h.δ_succ_succ_map, h.δ_map_of_gt j hj] }

/-- If `f` and `g` are in `X.PtSimplex n x`, then `RelStruct f g i.succ`
identifies to `MulStruct g .const f i`. -/
@[simps apply_map symm_apply_map]
/--
Definition of `relStructSuccEquivMulStruct` / `relStructSuccEquivMulStruct` 的定义

English:
definition relStructSuccEquivMulStruct
  signature: {f g : X.PtSimplex n x} {i : Fin n}
  body: { map := h.map
      δ_map_of_lt j hj := h.δ_map_of_lt j (lt_trans hj (by simp))
      δ_succ_castSucc_map := by rw [← Fin.castSucc_succ, h.δ_castSucc_map] }
  invFun h :=
    { map := h.map
      δ_map_of_lt j hj := by
        rw [← Fin.succ_castSucc] at hj
        obtain rfl | hj := (Fin.le_castSucc_iff.mpr hj).eq_or_lt
        exacts [h.δ_castSucc_castSucc_map, h.δ_map_of_lt j hj] }

中文:
定义 relStructSuccEquivMulStruct
  签名: {f g : X.PtSimplex n x} {i : 有限集 n}
  定义体: { map := h.map
      δ_map_of_lt j hj := h.δ_map_of_lt j (lt_trans hj (by simp))
      δ_succ_castSucc_map := by rw [← Fin.castSucc_succ, h.δ_castSucc_map] }
  invFun h :=
    { map := h.map
      δ_map_of_lt j hj := by
        rw [← Fin.succ_castSucc] at hj
        obtain rfl | hj := (Fin.le_castSucc_iff.mpr hj).eq_or_lt
        exacts [h.δ_castSucc_castSucc_map, h.δ_map_of_lt j hj] }

Depends on / 依赖: Fin.castSucc_succ, Fin.le_castSucc_iff.mpr, Fin.succ_castSucc, castSucc_succ, eq_or_lt, exacts, h.map, invFun, le_castSucc_iff, lt_trans, succ_castSucc
-/
def relStructSuccEquivMulStruct {f g : X.PtSimplex n x} {i : Fin n} :
    RelStruct f g i.succ ≃ MulStruct g .const f i where
  toFun h :=
    { map := h.map
      δ_map_of_lt j hj := h.δ_map_of_lt j (lt_trans hj (by simp))
      δ_succ_castSucc_map := by rw [← Fin.castSucc_succ, h.δ_castSucc_map] }
  invFun h :=
    { map := h.map
      δ_map_of_lt j hj := by
        rw [← Fin.succ_castSucc] at hj
        obtain rfl | hj := (Fin.le_castSucc_iff.mpr hj).eq_or_lt
        exacts [h.δ_castSucc_castSucc_map, h.δ_map_of_lt j hj] }

namespace MulStruct

/-- Given `f : X.PtSimplex n x` and `i : Fin n` (note that this implies `n ≠ 0`),
this is the term in `MulStruct .const f f i` corresponding to
`stdSimplex.σ i.castSucc ≫ f.map`. -/
@[simps! map]
/--
Definition of `oneMul` / `oneMul` 的定义

English:
definition oneMul
  signature: (f : X.PtSimplex n x) (i : Fin n)
  body: relStructCastSuccEquivMulStruct (.refl f i.castSucc)

中文:
定义 oneMul
  签名: (f : X.PtSimplex n x) (i : 有限集 n)
  定义体: relStructCastSuccEquivMulStruct (.refl f i.castSucc)

Depends on / 依赖: castSucc, i.castSucc, relStructCastSuccEquivMulStruct
-/
def oneMul (f : X.PtSimplex n x) (i : Fin n) :
    MulStruct .const f f i :=
  relStructCastSuccEquivMulStruct (.refl f i.castSucc)

/-- Given `f : X.PtSimplex n x` and `i : Fin n` (note that this implies `n ≠ 0`),
this is the term in `MulStruct f .const f i` corresponding to
`stdSimplex.σ i.succ ≫ f.map`. -/
@[simps! map]
/--
Definition of `mulOne` / `mulOne` 的定义

English:
definition mulOne
  signature: (f : X.PtSimplex n x) (i : Fin n)
  body: relStructSuccEquivMulStruct (.refl f i.succ)

中文:
定义 mulOne
  签名: (f : X.PtSimplex n x) (i : 有限集 n)
  定义体: relStructSuccEquivMulStruct (.refl f i.succ)

Depends on / 依赖: i.succ, relStructSuccEquivMulStruct
-/
def mulOne (f : X.PtSimplex n x) (i : Fin n) :
    MulStruct f .const f i :=
  relStructSuccEquivMulStruct (.refl f i.succ)

end MulStruct

end PtSimplex

end SSet
