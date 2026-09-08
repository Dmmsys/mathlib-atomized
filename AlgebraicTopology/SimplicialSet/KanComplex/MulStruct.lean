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

/-- Given a simplicial set `X`, `n : ℕ` and `x : X _⦋0⦌`, this is the type
of morphisms `Δ[n] ⟶ X` which are constant with value `x` on the boundary. -/
/-
**SSet.PtSimplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
形式化陈述：PtSimplex (n : Nat) (x : X _⦋0⦌) : Type u
参数：n : Nat；x : X _⦋0⦌。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a simplicial set `X`, `n : ℕ` and `x : X _⦋0⦌`, this is the type
of morphisms `Δ[n] ⟶ X` which are constant with value `x` on the boundary.
-/
abbrev PtSimplex (n : ℕ) (x : X _⦋0⦌) : Type u :=
  RelativeMorphism (boundary n) (Subcomplex.ofSimplex x)
    (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

namespace PtSimplex

variable {X} {n : ℕ} {x : X _⦋0⦌}

@[reassoc]
/-
**SSet.PtSimplex.comp_map_eq_const** 是 Mathlib 中的一个引理，位于命名空间 `SSet.PtSimplex`。
形式化陈述：comp_map_eq_const (s : X.PtSimplex n x) {Y : SSet.{u}} (φ : Y ⟶ Δ[n]) [Y.H
asDimensionLT n] : φ ≫ s.map = const x
参数：s : X.PtSimplex n x；φ : Y ⟶ Δ[n]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.stdSimplex.le_boundary_iff`：le_boundary_iff : A <= boundary.{u} n ↔
 A != ⊤
· 使用定理 `CategoryTheory.Subfunctor.instIsIsoFunctorTypeιTop`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor C (Type w)},   
CategoryTheory.IsIso ⊤.ι
· 使用引理 `SSet.stdSimplex.not_hasDimensionLT`：not_hasDimensionLT (n : Nat) (_ : Ha
sDimensionLT.{u} Δ[n] n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SSet.hasDimensionLT_iff_of_iso`：hasDimensionLT_iff_of_iso {X Y : SSet.{u
}} (e : X ≅ Y) (d : Nat) : X.HasDimensionLT d ↔ Y.HasDimensionLT d
· 使用定理 `SSet.instHasDimensionLTToSSetRange`：∀ {X Y : _root_.SSet} (f : X ⟶ Y) (d
 : ℕ) [X.HasDimensionLT d], (SSet.Subcomplex.range f).toSSet.HasDimensionLT d
· 使用定理 `SSet.RelativeMorphism.comm`：∀ {X Y : _root_.SSet} {A : X.Subcomplex} {B 
: Y.Subcomplex} {φ : A.toSSet ⟶ B.toSSet}   (self : SSet.RelativeMorphism A B φ)
,   CategoryTheo…
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
/-
**SSet.PtSimplex.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.PtSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_map (f : X.PtSimplex (n + 1) x) (i : Fin (n + 2)) :
    stdSimplex.δ i ≫ f.map = const x :=
  comp_map_eq_const _ _

/-- The bijection between `n`-simplices of `X.op` and of `X`
that are constant on the boundary. -/
@[simps]
/-
**SSet.PtSimplex.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.PtSimplex`。
形式化陈述：opEquiv : X.op.PtSimplex n (opObjEquiv.symm x) ≃ X.PtSimplex n x where toF
un f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The bijection between `n`-simplices of `X.op` and of `X`
that are constant on the boundary.
-/
def opEquiv : X.op.PtSimplex n (opObjEquiv.symm x) ≃ X.PtSimplex n x where
  toFun f :=
    { map := yonedaEquiv.symm (opObjEquiv (yonedaEquiv f.map))
      comm := by
        obtain _ | n := n
        · ext
        · refine boundary.hom_ext (fun i ↦ ?_)
          simp [stdSimplex.δ_comp_yonedaEquiv_symm,
            δ_opObjEquiv, ← stdSimplex.yonedaEquiv_δ_comp,
            opObjEquiv_yonedaEquiv_const] }
  invFun g :=
    { map := yonedaEquiv.symm (opObjEquiv.symm (yonedaEquiv g.map))
      comm := by
        obtain _ | n := n
        · ext
        · refine boundary.hom_ext (fun i ↦ ?_)
          simp [stdSimplex.δ_comp_yonedaEquiv_symm, op_δ,
            ← stdSimplex.yonedaEquiv_δ_comp,
            opObjEquiv_symm_yonedaEquiv_const] }
  left_inv _ := by simp
  right_inv _ := by simp

/-- Given a `n`-simplex of `X` that is constant on the boundary, this
is the corresponding `n`-simplex of `X.op`. -/
/-
**SSet.PtSimplex.op** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.PtSimplex`。
形式化陈述：op (f : X.PtSimplex n x) : X.op.PtSimplex n (opObjEquiv.symm x)
参数：f : X.PtSimplex n x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a `n`-simplex of `X` that is constant on the boundary, this
is the corresponding `n`-simplex of `X.op`.
-/
abbrev op (f : X.PtSimplex n x) : X.op.PtSimplex n (opObjEquiv.symm x) :=
  opEquiv.symm f

/-- Given a `n`-simplex of `X.op` that is constant on the boundary, this
is the corresponding `n`-simplex of `X`. -/
/-
**SSet.PtSimplex.unop** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.PtSimplex`。
形式化陈述：unop (f : X.op.PtSimplex n (opObjEquiv.symm x)) : X.PtSimplex n x
参数：f : X.op.PtSimplex n (opObjEquiv.symm x)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a `n`-simplex of `X.op` that is constant on the boundary, this
is the corresponding `n`-simplex of `X`.
-/
abbrev unop (f : X.op.PtSimplex n (opObjEquiv.symm x)) : X.PtSimplex n x :=
  opEquiv f

/-- For each `i : Fin (n + 1)`, this is a variant of the homotopy relation on
`n`-simplices that are constant on the boundary. Simplices `f` and `g` are related
if they appear respectively as the `i.castSucc` and `i.succ` faces of a
`n + 1`-simplex such that all the other faces are constant. -/
/-
**SSet.PtSimplex.RelStruct** 是 Mathlib 中的一个结构，位于命名空间 `SSet.PtSimplex`。
形式化陈述：RelStruct (f g : X.PtSimplex n x) (i : Fin (n + 1)) where /-- A `n + 1`-si
mplex -/ map : Δ[n + 1] ⟶ X δ_castSucc_map : stdSimplex.δ i.castSucc ≫ map = f.m
ap
参数：f g : X.PtSimplex n x；i : Fin (n + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For each `i : Fin (n + 1)`, this is a variant of the homotopy relation on
`n`-simplices that are constant on the boundary. Simplices `f` and `g` are relat
ed
if they appear respectively as the `i.castSucc` and `i.succ` faces of a
`n + 1`-simplex such that all the other faces are constant.
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
/-
**SSet.PtSimplex.RelStruct.refl** 是 Mathlib 中的一个定义，位于命名空间 `SSet.PtSimplex.RelStr
uct`。
形式化陈述：refl (f : X.PtSimplex n x) (i : Fin (n + 1)) : RelStruct f f i where map
参数：f : X.PtSimplex n x；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RelStruct` is reflexive.
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
/-
**SSet.PtSimplex.RelStruct.copy** 是 Mathlib 中的一个定义，位于命名空间 `SSet.PtSimplex.RelStr
uct`。
形式化陈述：copy {f g : X.PtSimplex n x} {i : Fin (n + 1)} (r : RelStruct f g i) {f' g
' : X.PtSimplex n x} (hf : f = f') (hg : g = g') : RelStruct f' g' i where map
参数：n + 1；r : RelStruct f g i；hf : f = f'；hg : g = g'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `RelStruct f' g' i` deduced from `r : RelStruct f g i` when
`f = f'` and `g = g'`.
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
/-
**SSet.PtSimplex.RelStruct.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `SSet.PtSimplex.RelStr
uct`。
形式化陈述：ofEq {f g : X.PtSimplex n x} (h : f = g) (i : Fin (n + 1)) : RelStruct f g
 i
参数：h : f = g；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `RelStruct f g i` deduced from an equality `f = g`.
-/
def ofEq {f g : X.PtSimplex n x} (h : f = g) (i : Fin (n + 1)) :
    RelStruct f g i :=
  (refl f i).copy rfl h

end RelStruct

/-- For each `i : Fin n`, this structure is a candidate for the relation saying
that `fg` is the product of `f` and `g` in the homotopy group (of a Kan complex).
It is so if `g`, `fg` and `f` are respectively the `i.castSucc.castSucc`,
`i.castSucc.succ` and `i.succ.succ` faces of a `n + 1`-simplex such that
all the other faces are constant. (The multiplication on homotopy groups will be
defined using `i := Fin.last _`, but in general, this structure is useful in
order to obtain properties of `RelStruct`.) -/
/-
**SSet.PtSimplex.MulStruct** 是 Mathlib 中的一个结构，位于命名空间 `SSet.PtSimplex`。
形式化陈述：MulStruct (f g fg : X.PtSimplex n x) (i : Fin n) where /-- A `n + 1`-simpl
ex -/ map : Δ[n + 1] ⟶ X δ_castSucc_castSucc_map : stdSimplex.δ (i.castSucc.cast
Succ) ≫ map = g.map
参数：f g fg : X.PtSimplex n x；i : Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For each `i : Fin n`, this structure is a candidate for the relation saying
that `fg` is the product of `f` and `g` in the homotopy group (of a Kan complex)
.
It is so if `g`, `fg` and `f` are respectively the `i.castSucc.castSucc`,
`i.castSucc.succ` and `i.succ.succ` faces of a `n + 1`-simplex such that
all the other faces are constant. (The multiplication on homotopy groups will be
defined using `i := Fin.last _`, but in general, this structure is useful in
order to obtain properties of `RelStruct`.)
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
/-
**SSet.PtSimplex.MulStruct.op** 是 Mathlib 中的一个定义，位于命名空间 `SSet.PtSimplex.MulStruc
t`。
形式化陈述：op {f g fg : X.PtSimplex n x} {i : Fin n} (h : MulStruct f g fg i) {j : Fi
n n} (hij : i.rev = j
参数：h : MulStruct f g fg i。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The `MulStruct` for `X.op` that is deduced from a `MulStruct` for the simplicial
set `X`.
-/
def op {f g fg : X.PtSimplex n x} {i : Fin n} (h : MulStruct f g fg i) {j : Fin n}
    (hij : i.rev = j := by grind) :
    MulStruct g.op f.op fg.op j where
  map := yonedaEquiv.symm (opObjEquiv.symm (yonedaEquiv h.map))
  δ_castSucc_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, op_δ, Equiv.apply_symm_apply,
      ← stdSimplex.yonedaEquiv_δ_comp, opEquiv_symm_apply_map, ← h.δ_succ_succ_map,
      Fin.rev_castSucc, Fin.rev_castSucc, ← hij, Fin.rev_rev]
  δ_succ_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, op_δ, Equiv.apply_symm_apply,
      ← stdSimplex.yonedaEquiv_δ_comp, opEquiv_symm_apply_map, ← h.δ_succ_castSucc_map,
      Fin.rev_succ, Fin.rev_castSucc, Fin.castSucc_succ, ← hij, Fin.rev_rev]
  δ_succ_succ_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, op_δ, Equiv.apply_symm_apply,
      ← stdSimplex.yonedaEquiv_δ_comp, opEquiv_symm_apply_map, ← h.δ_castSucc_castSucc_map,
      Fin.rev_succ, Fin.rev_succ, ← hij, Fin.rev_rev]
  δ_map_of_lt k hk := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, ← stdSimplex.yonedaEquiv_δ_comp,
      opObjEquiv_symm_yonedaEquiv_const, h.δ_map_of_gt k.rev (by grind)]
  δ_map_of_gt k hk := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, ← stdSimplex.yonedaEquiv_δ_comp,
      opObjEquiv_symm_yonedaEquiv_const, h.δ_map_of_lt k.rev (by grind)]

/-- The `Mulstruct` for a simplicial set `X` that is deduced from a `Mulstruct` for `X.op`. -/
@[simps]
/-
**SSet.PtSimplex.MulStruct.unop** 是 Mathlib 中的一个定义，位于命名空间 `SSet.PtSimplex.MulStr
uct`。
形式化陈述：unop {f g fg : X.PtSimplex n x} {i : Fin n} (h : MulStruct g.op f.op fg.op
 i) {j : Fin n} (hij : i.rev = j
参数：h : MulStruct g.op f.op fg.op i。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The `Mulstruct` for a simplicial set `X` that is deduced from a `Mulstruct` for 
`X.op`.
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
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, h.δ_map_of_gt _ (by grind)]
    simp [opObjEquiv_yonedaEquiv_const]
  δ_map_of_gt k hk := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, h.δ_map_of_lt _ (by grind)]
    simp [opObjEquiv_yonedaEquiv_const]

end MulStruct

/-- If `f` and `g` are in `X.PtSimplex n x`, then `RelStruct f g i.castSucc`
identifies to `MulStruct .const f g i`. -/
@[simps apply_map symm_apply_map]
/-
**SSet.PtSimplex.relStructCastSuccEquivMulStruct** 是 Mathlib 中的一个定义，位于命名空间 `SSet
.PtSimplex`。
形式化陈述：relStructCastSuccEquivMulStruct {f g : X.PtSimplex n x} {i : Fin n} : RelS
truct f g i.castSucc ≃ MulStruct .const f g i where toFun h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `g` are in `X.PtSimplex n x`, then `RelStruct f g i.castSucc`
identifies to `MulStruct .const f g i`.
-/
def relStructCastSuccEquivMulStruct {f g : X.PtSimplex n x} {i : Fin n} :
    RelStruct f g i.castSucc ≃ MulStruct .const f g i where
  toFun h :=
    { map := h.map
      δ_map_of_gt j hj := h.δ_map_of_gt j (lt_trans (by simp) hj) }
  invFun h :=
    { map := h.map
      δ_map_of_gt j hj := by
        rw [Fin.succ_castSucc, Fin.castSucc_lt_iff_succ_le] at hj
        obtain rfl | hj := hj.eq_or_lt
        exacts [h.δ_succ_succ_map, h.δ_map_of_gt j hj] }

/-- If `f` and `g` are in `X.PtSimplex n x`, then `RelStruct f g i.succ`
identifies to `MulStruct g .const f i`. -/
@[simps apply_map symm_apply_map]
/-
**SSet.PtSimplex.relStructSuccEquivMulStruct** 是 Mathlib 中的一个定义，位于命名空间 `SSet.PtS
implex`。
形式化陈述：relStructSuccEquivMulStruct {f g : X.PtSimplex n x} {i : Fin n} : RelStruc
t f g i.succ ≃ MulStruct g .const f i where toFun h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `g` are in `X.PtSimplex n x`, then `RelStruct f g i.succ`
identifies to `MulStruct g .const f i`.
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
/-
**SSet.PtSimplex.MulStruct.oneMul** 是 Mathlib 中的一个定义，位于命名空间 `SSet.PtSimplex.MulS
truct`。
形式化陈述：oneMul (f : X.PtSimplex n x) (i : Fin n) : MulStruct .const f f i
参数：f : X.PtSimplex n x；i : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : X.PtSimplex n x` and `i : Fin n` (note that this implies `n ≠ 0`),
this is the term in `MulStruct .const f f i` corresponding to
`stdSimplex.σ i.castSucc ≫ f.map`.
-/
def oneMul (f : X.PtSimplex n x) (i : Fin n) :
    MulStruct .const f f i :=
  relStructCastSuccEquivMulStruct (.refl f i.castSucc)

/-- Given `f : X.PtSimplex n x` and `i : Fin n` (note that this implies `n ≠ 0`),
this is the term in `MulStruct f .const f i` corresponding to
`stdSimplex.σ i.succ ≫ f.map`. -/
@[simps! map]
/-
**SSet.PtSimplex.MulStruct.mulOne** 是 Mathlib 中的一个定义，位于命名空间 `SSet.PtSimplex.MulS
truct`。
形式化陈述：mulOne (f : X.PtSimplex n x) (i : Fin n) : MulStruct f .const f i
参数：f : X.PtSimplex n x；i : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : X.PtSimplex n x` and `i : Fin n` (note that this implies `n ≠ 0`),
this is the term in `MulStruct f .const f i` corresponding to
`stdSimplex.σ i.succ ≫ f.map`.
-/
def mulOne (f : X.PtSimplex n x) (i : Fin n) :
    MulStruct f .const f i :=
  relStructSuccEquivMulStruct (.refl f i.succ)

end MulStruct

end PtSimplex

end SSet

