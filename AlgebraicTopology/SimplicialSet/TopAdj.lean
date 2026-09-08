/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.Topology.Category.TopCat.Monoidal

/-!
# Properties of the geometric realization

In this file, we introduce some API in order to study the geometric
realization functor (and its right adjoint the singular simplicial set functor):
* `SimplexCategory.toTopHomeo`: the homeomorphism between the geometric
realization of `Δ[n]` and `stdSimplex ℝ (Fin (n + 1))`;
* `TopCat.toSSetObj₀Equiv : toSSet.obj X _⦋0⦌ ≃ X` for `X : TopCat`;
* `SSet.stdSimplex.toTopObjIsoI : |Δ[1]| ≅ TopCat.I`;
* `SSet.stdSimplex.toSSetObjI : Δ[1] ⟶ TopCat.toSSet.obj TopCat.I`:
the morphism corresponding to `toTopObjIsoI.hom` by adjunction.

-/

@[expose] public section

universe u

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : TopCat.toSSet.{u}.Monoidal := .ofChosenFiniteProducts _

open CategoryTheory MonoidalCategory Simplicial Opposite

namespace SimplexCategory

open SSet

/-- The homeomorphism between the topological realization of a standard simplex
in `SSet` and the corresponding topological standard simplex. -/
/-
**SimplexCategory.toTopHomeo** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：toTopHomeo (n : SimplexCategory) : |stdSimplex.{u}.obj n| ≃ₜ stdSimplex Re
al (Fin (n.len + 1))
参数：n : SimplexCategory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homeomorphism between the topological realization of a standard simplex
in `SSet` and the corresponding topological standard simplex.
-/
noncomputable def toTopHomeo (n : SimplexCategory) :
    |stdSimplex.{u}.obj n| ≃ₜ stdSimplex ℝ (Fin (n.len + 1)) :=
  (TopCat.homeoOfIso (toTopSimplex.{u}.app n)).trans Homeomorph.ulift
/-
**SimplexCategory.toTopHomeo_naturality** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCatego
ry`。
形式化陈述：toTopHomeo_naturality {n m : SimplexCategory} (f : n ⟶ m) : toTopHomeo m ∘
 SSet.toTop.{u}.map (SSet.stdSimplex.map f) = stdSimplex.map f ∘ n.toTopHomeo
参数：f : n ⟶ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ULift.up_injective`：up_injective : Injective (@up α)
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma toTopHomeo_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    toTopHomeo m ∘ SSet.toTop.{u}.map (SSet.stdSimplex.map f) =
    stdSimplex.map f ∘ n.toTopHomeo := by
  ext x : 1
  exact ULift.up_injective (ConcreteCategory.congr_hom ((forget TopCat).congr_map
    (toTopSimplex.hom.naturality f)) x)
/-
**SimplexCategory.toTopHomeo_naturality_apply** 是 Mathlib 中的一个引理，位于命名空间 `Simplex
Category`。
形式化陈述：toTopHomeo_naturality_apply {n m : SimplexCategory} (f : n ⟶ m) (x : |stdS
implex.obj n|) : m.toTopHomeo ((SSet.toTop.{u}.map (SSet.stdSimplex.map f) x)) =
 (_root_.stdSimplex.map f) (n.toTopHomeo x)
参数：f : n ⟶ m；x : |stdSimplex.obj n|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用引理 `SimplexCategory.toTopHomeo_naturality`：toTopHomeo_naturality {n m : Simp
lexCategory} (f : n ⟶ m) : toTopHomeo m ∘ SSet.toTop.{u}.map (SSet.stdSimplex.ma
p f) = stdSimplex.map f ∘ n…
-/
lemma toTopHomeo_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : |stdSimplex.obj n|) :
    m.toTopHomeo ((SSet.toTop.{u}.map (SSet.stdSimplex.map f) x)) =
      (_root_.stdSimplex.map f) (n.toTopHomeo x) :=
  congr_fun (toTopHomeo_naturality f) x
/-
**SimplexCategory.toTopHomeo_symm_naturality** 是 Mathlib 中的一个引理，位于命名空间 `SimplexC
ategory`。
形式化陈述：toTopHomeo_symm_naturality {n m : SimplexCategory} (f : n ⟶ m) : m.toTopHo
meo.symm ∘ stdSimplex.map f = (SSet.toTop.{u}.map (SSet.stdSimplex.map f)).hom ∘
 n.toTopHomeo.symm
参数：f : n ⟶ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma toTopHomeo_symm_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    m.toTopHomeo.symm ∘ stdSimplex.map f =
      (SSet.toTop.{u}.map (SSet.stdSimplex.map f)).hom ∘ n.toTopHomeo.symm := by
  ext x : 1
  exact ConcreteCategory.congr_hom ((forget _).congr_map
    (toTopSimplex.inv.naturality f)) _
/-
**SimplexCategory.toTopHomeo_symm_naturality_apply** 是 Mathlib 中的一个引理，位于命名空间 `Si
mplexCategory`。
形式化陈述：toTopHomeo_symm_naturality_apply {n m : SimplexCategory} (f : n ⟶ m) (x : 
stdSimplex Real (Fin (n.len + 1))) : m.toTopHomeo.symm (stdSimplex.map f x) = SS
et.toTop.{u}.map (SSet.stdSimplex.map f) (n.toTopHomeo.symm x)
参数：f : n ⟶ m；x : stdSimplex Real (Fin (n.len + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用引理 `SimplexCategory.toTopHomeo_symm_naturality`：toTopHomeo_symm_naturality {
n m : SimplexCategory} (f : n ⟶ m) : m.toTopHomeo.symm ∘ stdSimplex.map f = (SSe
t.toTop.{u}.map (SSet.stdSimplex…
-/
lemma toTopHomeo_symm_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : stdSimplex ℝ (Fin (n.len + 1))) :
    m.toTopHomeo.symm (stdSimplex.map f x) =
      SSet.toTop.{u}.map (SSet.stdSimplex.map f) (n.toTopHomeo.symm x) :=
  congr_fun (toTopHomeo_symm_naturality f) x

end SimplexCategory

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (stdSimplex ℝ (Fin (⦋0⦌.len + 1))) :=
  inferInstanceAs (Unique (stdSimplex ℝ (Fin 1)))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Unique |(Δ[0] : SSet.{u})| := ⦋0⦌.toTopHomeo.unique

namespace TopCat

/-- Given `X : TopCat`, this is the bijection between `0`-simplices
of the singular simplicial set of `X` and `X`. -/
@[simps! -isSimp apply symm_apply]
/-
**TopCat.toSSetObj** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X : TopCat`, this is the bijection between `0`-simplices
of the singular simplicial set of `X` and `X`.
-/
noncomputable def toSSetObj₀Equiv {X : TopCat.{u}} :
    toSSet.obj X _⦋0⦌ ≃ X :=
  (toSSetObjEquiv X _).trans
    { toFun f := f.1 (default : _)
      invFun x := ⟨fun _ ↦ x, by fun_prop⟩
      left_inv _ := by
        ext x
        obtain rfl := Subsingleton.elim x default
        rfl
      right_inv _ := rfl }

@[simp]
/-
**TopCat.toSSet_map_const** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：toSSet_map_const (X : TopCat.{u}) {Y : TopCat.{u}} (y : Y) : toSSet.map (T
opCat.const (X
参数：X : TopCat.{u}；y : Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSSet_map_const (X : TopCat.{u}) {Y : TopCat.{u}} (y : Y) :
    toSSet.map (TopCat.const (X := X) y) =
      SSet.const (toSSetObj₀Equiv.symm y) :=
  rfl
/-
**TopCat.toSSetObjEquiv_symm_naturality** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：toSSetObjEquiv_symm_naturality {X : TopCat.{u}} {n m : SimplexCategory} (f
 : n ⟶ m) (g : C((stdSimplex Real (Fin (m.len + 1))), X)) : (toSSet.obj X).map f
.op ((X.toSSetObjEquiv _).symm g) = (X.toSSetObjEquiv _).symm (g.comp ⟨stdSimple
x.map f, by continuity⟩)
参数：f : n ⟶ m；g : C((stdSimplex Real (Fin (m.len + 1))), X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma toSSetObjEquiv_symm_naturality {X : TopCat.{u}} {n m : SimplexCategory} (f : n ⟶ m)
    (g : C((stdSimplex ℝ (Fin (m.len + 1))), X)) :
    (toSSet.obj X).map f.op ((X.toSSetObjEquiv _).symm g) =
      (X.toSSetObjEquiv _).symm (g.comp ⟨stdSimplex.map f, by continuity⟩) :=
  rfl

@[simp]
/-
**TopCat.toSSetObjEquiv_naturality_apply** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：toSSetObjEquiv_naturality_apply {X : TopCat.{u}} {n m : SimplexCategory} (
f : n ⟶ m) (x : (toSSet.obj X).obj (op m)) (z : stdSimplex Real (Fin (n.len + 1)
)) : dsimp% X.toSSetObjEquiv _ ((toSSet.obj X).map f.op x) z = X.toSSetObjEquiv 
_ x (stdSimplex.map f z)
参数：f : n ⟶ m；x : (toSSet.obj X).obj (op m)；z : stdSimplex Real (Fin (n.len + 1))
。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSSetObjEquiv_naturality_apply {X : TopCat.{u}} {n m : SimplexCategory} (f : n ⟶ m)
    (x : (toSSet.obj X).obj (op m)) (z : stdSimplex ℝ (Fin (n.len + 1))) :
    dsimp% X.toSSetObjEquiv _ ((toSSet.obj X).map f.op x) z =
      X.toSSetObjEquiv _ x (stdSimplex.map f z) :=
  rfl

@[simp]
/-
**TopCat.toSSetObjEquiv_** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSSetObjEquiv_δ_apply {X : TopCat.{u}} {n : ℕ}
    (x : toSSet.obj X _⦋n + 1⦌) (i : Fin (n + 2)) (z : stdSimplex ℝ (Fin (n + 1))) :
    dsimp% X.toSSetObjEquiv _ ((toSSet.obj X).δ i x) z =
      X.toSSetObjEquiv _ x (stdSimplex.map i.succAbove z) :=
  rfl

@[simp]
/-
**TopCat.toSSetObjEquiv_** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSSetObjEquiv_σ_apply {X : TopCat.{u}} {n : ℕ}
    (x : toSSet.obj X _⦋n⦌) (i : Fin (n + 1)) (z : stdSimplex ℝ (Fin (n + 2))) :
    dsimp% X.toSSetObjEquiv _ ((toSSet.obj X).σ i x) z =
      X.toSSetObjEquiv _ x (stdSimplex.map i.predAbove z) :=
  rfl

end TopCat

/-
**sSetTopAdj_homEquiv_stdSimplex_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sSetTopAdj_homEquiv_stdSimplex_zero {X : TopCat.{u}} (f : |Δ[0]| ⟶ X) : sS
etTopAdj.homEquiv Δ[0] X f = SSet.const (TopCat.toSSetObj₀Equiv.symm (f default)
)
参数：f : |Δ[0]| ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `TopCat.toSSetObj₀Equiv_symm_apply`：∀ {X : TopCat} (a : ↑X),   TopCat.toS
SetObj₀Equiv.symm a =     (X.toSSetObjEquiv (Opposite.op { len := 0 })).symm { t
oFun := fun x => a, con…
-/
lemma sSetTopAdj_homEquiv_stdSimplex_zero {X : TopCat.{u}}
    (f : |Δ[0]| ⟶ X) :
    sSetTopAdj.homEquiv Δ[0] X f =
      SSet.const (TopCat.toSSetObj₀Equiv.symm (f default)) := by
  have : sSetTopAdj.unit.app Δ[0] =
      SSet.const (TopCat.toSSetObj₀Equiv.symm default) :=
    SSet.yonedaEquiv.injective (TopCat.toSSetObj₀Equiv.injective (by subsingleton))
  rw [Adjunction.homEquiv_unit, TopCat.toSSetObj₀Equiv_symm_apply, this]
  rfl

/-- The standard topological simplex of dimension `1` is homeomorphic to `TopCat.I`. -/
/-
**TopCat.stdSimplexHomeomorphI** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TopCat.stdSimplexHomeomorphI : _root_.stdSimplex Real (Fin 2) ≃ₜ TopCat.I.
{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard topological simplex of dimension `1` is homeomorphic to `TopCat.I`.
-/
def TopCat.stdSimplexHomeomorphI :
    _root_.stdSimplex ℝ (Fin 2) ≃ₜ TopCat.I.{u} :=
  stdSimplexHomeomorphUnitInterval.trans Homeomorph.ulift.symm

@[simp]
/-
**TopCat.stdSimplexHomeomorphI_vertex_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TopCat.stdSimplexHomeomorphI_vertex_zero : TopCat.stdSimplexHomeomorphI.{u
} (stdSimplex.vertex 0) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma TopCat.stdSimplexHomeomorphI_vertex_zero :
    TopCat.stdSimplexHomeomorphI.{u} (stdSimplex.vertex 0) = 0 := rfl

@[simp]
/-
**TopCat.stdSimplexHomeomorphI_vertex_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TopCat.stdSimplexHomeomorphI_vertex_one : TopCat.stdSimplexHomeomorphI.{u}
 (stdSimplex.vertex 1) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma TopCat.stdSimplexHomeomorphI_vertex_one :
    TopCat.stdSimplexHomeomorphI.{u} (stdSimplex.vertex 1) = 1 := rfl

@[simp]
/-
**TopCat.stdSimplexHomeomorphI_symm_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TopCat.stdSimplexHomeomorphI_symm_zero : TopCat.stdSimplexHomeomorphI.{u}.
symm 0 = stdSimplex.vertex 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.symm_apply_apply`：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.s
ymm (h x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma TopCat.stdSimplexHomeomorphI_symm_zero :
    TopCat.stdSimplexHomeomorphI.{u}.symm 0 = stdSimplex.vertex 0 := by
  simp [← TopCat.stdSimplexHomeomorphI_vertex_zero]

@[simp]
/-
**TopCat.stdSimplexHomeomorphI_symm_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TopCat.stdSimplexHomeomorphI_symm_one : TopCat.stdSimplexHomeomorphI.{u}.s
ymm 1 = stdSimplex.vertex 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.symm_apply_apply`：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.s
ymm (h x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma TopCat.stdSimplexHomeomorphI_symm_one :
    TopCat.stdSimplexHomeomorphI.{u}.symm 1 = stdSimplex.vertex 1 := by
  simp [← TopCat.stdSimplexHomeomorphI_vertex_one]

namespace SSet.stdSimplex

/-- The geometric realization of `Δ[1]` is isomorphic to `TopCat.I`. -/
/-
**SSet.stdSimplex.toTopObjIsoI** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：toTopObjIsoI : |(Δ[1] : SSet.{u})| ≅ TopCat.I.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The geometric realization of `Δ[1]` is isomorphic to `TopCat.I`.
-/
noncomputable def toTopObjIsoI :
    |(Δ[1] : SSet.{u})| ≅ TopCat.I.{u} :=
  TopCat.isoOfHomeo ((SimplexCategory.toTopHomeo _).trans TopCat.stdSimplexHomeomorphI)

/-- The canonical morphism `Δ[1] ⟶ TopCat.toSSet.obj TopCat.I`: by adjunction,
it corresponds to the isomorphism `toTopObjIsoI : |Δ[1]| ≅ TopCat.I`. -/
/-
**SSet.stdSimplex.toSSetObjI** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：toSSetObjI : Δ[1] ⟶ TopCat.toSSet.obj TopCat.I.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `Δ[1] ⟶ TopCat.toSSet.obj TopCat.I`: by adjunction,
it corresponds to the isomorphism `toTopObjIsoI : |Δ[1]| ≅ TopCat.I`.
-/
noncomputable def toSSetObjI : Δ[1] ⟶ TopCat.toSSet.obj TopCat.I.{u} :=
  sSetTopAdj.homEquiv _ _ toTopObjIsoI.hom

@[simp]
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_one_toSSetObjI :
    stdSimplex.δ 1 ≫ toSSetObjI.{u} = SSet.const (TopCat.toSSetObj₀Equiv.symm 0) := by
  dsimp only [toSSetObjI, toTopObjIsoI, TopCat.stdSimplexHomeomorphI]
  rw [← Adjunction.homEquiv_naturality_left, sSetTopAdj_homEquiv_stdSimplex_zero]
  congr 2
  have : stdSimplexHomeomorphUnitInterval (⦋1⦌.toTopHomeo
      (((toTop.{u}.map (stdSimplex.δ 1)).hom) default)) = 0 := by
    rw [← stdSimplexHomeomorphUnitInterval_zero]
    congr 1
    refine (SimplexCategory.toTopHomeo_naturality_apply _ _).trans ?_
    rw [Subsingleton.elim (⦋0⦌.toTopHomeo default) (stdSimplex.vertex 0), stdSimplex.map_vertex]
    rfl
  exact congr_arg ULift.up.{u} this

@[simp]
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_zero_toSSetObjI :
    dsimp% stdSimplex.δ 0 ≫ toSSetObjI.{u} = SSet.const (TopCat.toSSetObj₀Equiv.symm 1) := by
  dsimp only [toSSetObjI, toTopObjIsoI, TopCat.stdSimplexHomeomorphI]
  rw [← Adjunction.homEquiv_naturality_left, sSetTopAdj_homEquiv_stdSimplex_zero]
  congr 2
  have : stdSimplexHomeomorphUnitInterval (⦋1⦌.toTopHomeo
      (((toTop.{u}.map (stdSimplex.δ 0)).hom) default)) = 1 := by
    rw [← stdSimplexHomeomorphUnitInterval_one]
    congr 1
    refine (SimplexCategory.toTopHomeo_naturality_apply _ _).trans ?_
    rw [Subsingleton.elim (⦋0⦌.toTopHomeo default) (stdSimplex.vertex 0), stdSimplex.map_vertex]
    rfl
  exact congr_arg ULift.up.{u} this

@[simp]
/-
**SSet.stdSimplex.toSSetObj_app_const_zero** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSi
mplex`。
形式化陈述：toSSetObj_app_const_zero : toSSetObjI.app (op ⦋0⦌) (const _ 0 _) = TopCat.
toSSetObj₀Equiv.symm 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.yonedaEquiv_symm_zero`：∀ {X : _root_.SSet} (x : X.obj (Opposite.op 
{ len := 0 })), SSet.yonedaEquiv.symm x = SSet.const x
· 使用引理 `SSet.const_comp`：const_comp {X Y Z : SSet.{u}} (y : Y _⦋0⦌) (g : Y ⟶ Z) 
: const (X
· 使用引理 `SSet.stdSimplex.δ_one_eq_const`：δ_one_eq_const : stdSimplex.{u}.δ (1 : F
in 2) = SSet.const (obj₀Equiv.symm 0)
· 使用定理 `SSet.stdSimplex.obj₀Equiv_symm_apply`：∀ {n : ℕ} (i : Fin (n + 1)), SSet.
stdSimplex.obj₀Equiv.symm i = SSet.stdSimplex.const n i (Opposite.op { len := 0 
})
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SSet.stdSimplex.δ_one_toSSetObjI`：δ_one_toSSetObjI : stdSimplex.δ 1 ≫ to
SSetObjI.{u} = SSet.const (TopCat.toSSetObj₀Equiv.symm 0)
-/
lemma toSSetObj_app_const_zero :
    toSSetObjI.app (op ⦋0⦌) (const _ 0 _) = TopCat.toSSetObj₀Equiv.symm 0 := by
  apply yonedaEquiv.symm.injective
  trans stdSimplex.δ 1 ≫ toSSetObjI
  · simp [← yonedaEquiv_symm_comp, stdSimplex.δ_one_eq_const]
  · simp

@[simp]
/-
**SSet.stdSimplex.toSSetObj_app_const_one** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSim
plex`。
形式化陈述：toSSetObj_app_const_one : toSSetObjI.app (op ⦋0⦌) (const _ 1 _) = TopCat.t
oSSetObj₀Equiv.symm 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.yonedaEquiv_symm_zero`：∀ {X : _root_.SSet} (x : X.obj (Opposite.op 
{ len := 0 })), SSet.yonedaEquiv.symm x = SSet.const x
· 使用引理 `SSet.const_comp`：const_comp {X Y Z : SSet.{u}} (y : Y _⦋0⦌) (g : Y ⟶ Z) 
: const (X
· 使用引理 `SSet.stdSimplex.δ_zero_eq_const`：δ_zero_eq_const : stdSimplex.{u}.δ (0 :
 Fin 2) = SSet.const (obj₀Equiv.symm 1)
· 使用定理 `SSet.stdSimplex.obj₀Equiv_symm_apply`：∀ {n : ℕ} (i : Fin (n + 1)), SSet.
stdSimplex.obj₀Equiv.symm i = SSet.stdSimplex.const n i (Opposite.op { len := 0 
})
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SSet.stdSimplex.δ_zero_toSSetObjI`：δ_zero_toSSetObjI : dsimp% stdSimplex
.δ 0 ≫ toSSetObjI.{u} = SSet.const (TopCat.toSSetObj₀Equiv.symm 1)
-/
lemma toSSetObj_app_const_one :
    toSSetObjI.app (op ⦋0⦌) (const _ 1 _) = TopCat.toSSetObj₀Equiv.symm 1 := by
  apply yonedaEquiv.symm.injective
  trans stdSimplex.δ 0 ≫ toSSetObjI
  · simp [← yonedaEquiv_symm_comp, stdSimplex.δ_zero_eq_const]
  · simp

open Functor.Monoidal in
@[reassoc (attr := simp)]
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₀_whiskerLeft_toSSetObjI_μ (X : TopCat.{u}) :
    SSet.ι₀ ≫ TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
      Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I = TopCat.toSSet.map TopCat.ι₀ := by
  rw [← cancel_mono (μIso _ _ _).inv, Category.assoc, Category.assoc, μIso_inv,
    μ_δ, Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

open Functor.Monoidal in
@[reassoc (attr := simp)]
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₁_whiskerLeft_toSSetObjI_μ (X : TopCat.{u}) :
    SSet.ι₁ ≫ TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
      Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I = TopCat.toSSet.map TopCat.ι₁ := by
  rw [← cancel_mono (μIso _ _ _).inv, Category.assoc, Category.assoc, μIso_inv,
    μ_δ, Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

end SSet.stdSimplex

