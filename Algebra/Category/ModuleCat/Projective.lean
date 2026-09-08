/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# The category of `R`-modules has enough projectives.
-/

public section

universe v u w

open CategoryTheory Module ModuleCat

variable {R : Type u} [Ring R] (P : ModuleCat.{v} R)

/-
**ModuleCat.projective_of_categoryTheory_projective** 是 Mathlib 中的一个实例，位于命名空间 ``
。
形式化陈述：ModuleCat.projective_of_categoryTheory_projective [Module.Projective R P] 
: CategoryTheory.Projective P
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.projective_lifting_property`：projective_lifting_property [h : Pro
jective R P] (f : M ->ₗ[R] N) (g : P ->ₗ[R] N) (hf : Function.Surjective f) : ex
ists h : P ->ₗ[R] M, f ∘…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ModuleCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surj
ective f
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
-/
instance ModuleCat.projective_of_categoryTheory_projective [Module.Projective R P] :
    CategoryTheory.Projective P := by
  refine ⟨fun E X epi => ?_⟩
  obtain ⟨f, h⟩ := Module.projective_lifting_property X.hom E.hom
    ((ModuleCat.epi_iff_surjective _).mp epi)
  exact ⟨ofHom f, hom_ext h⟩
/-
**ModuleCat.projective_of_module_projective** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ModuleCat.projective_of_module_projective [Small.{v} R] [Projective P] : M
odule.Projective R P
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.of_lifting_property`：∀ {R : Type u} [inst : Ring R] {P
 : Type v} [inst_1 : AddCommGroup P] [inst_2 : _root_.Module R P] [Small.{v, u} 
R],   (∀ {M N : Type v} [in…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ModuleCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surj
ective f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ModuleCat.hom_ext_iff`：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R
} {f g : M ⟶ N}, f = g ↔ ModuleCat.Hom.hom f = ModuleCat.Hom.hom g
· 使用定理 `CategoryTheory.Projective.factorThru_comp`：factorThru_comp {P X E : C} [
Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] : factorThru f e ≫ e = f
-/
instance ModuleCat.projective_of_module_projective [Small.{v} R] [Projective P] :
    Module.Projective R P := by
  refine Module.Projective.of_lifting_property ?_
  intro _ _ _ _ _ _ f g s
  have : Epi (↟f) := (ModuleCat.epi_iff_surjective (↟f)).mpr s
  exact ⟨(Projective.factorThru (↟g) (↟f)).hom,
    ModuleCat.hom_ext_iff.mp <| Projective.factorThru_comp (↟g) (↟f)⟩

/-- The categorical notion of projective object agrees with the explicit module-theoretic notion. -/
/-
**IsProjective.iff_projective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsProjective.iff_projective [Small.{v} R] (P : Type v) [AddCommGroup P] [M
odule R P] : Module.Projective R P ↔ Projective (of R P)
参数：P : Type v。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical notion of projective object agrees with the explicit module-theo
retic notion.
-/
theorem IsProjective.iff_projective [Small.{v} R] (P : Type v) [AddCommGroup P] [Module R P] :
    Module.Projective R P ↔ Projective (of R P) :=
  ⟨fun _ => (of R P).projective_of_categoryTheory_projective,
    fun _ => (of R P).projective_of_module_projective⟩

namespace ModuleCat

variable {M : ModuleCat.{v} R}

-- We transport the corresponding result from `Module.Projective`.
/-- Modules that have a basis are projective. -/
/-
**ModuleCat.projective_of_free** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：projective_of_free {ι : Type w} (b : Basis ι R M) : Projective M
参数：b : Basis ι R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.of_basis`：∀ {R : Type u_1} [inst : Semiring R] {P : Ty
pe u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   {ι : Type u_8}
 (b : Module.Bas…

--- 原说明 ---
Modules that have a basis are projective.
-/
theorem projective_of_free {ι : Type w} (b : Basis ι R M) : Projective M :=
  have : Module.Projective R M := Module.Projective.of_basis b
  M.projective_of_categoryTheory_projective

/-- The category of modules has enough projectives, since every module is a quotient of a free
  module. -/
/-
**ModuleCat.enoughProjectives** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：enoughProjectives [Small.{v} R] : EnoughProjectives (ModuleCat.{v} R) wher
e presentation M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.projective_of_free`：projective_of_free {ι : Type w} (b : Basis
 ι R M) : Projective M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModuleCat.epi_iff_range_eq_top`：epi_iff_range_eq_top : Epi f ↔ LinearMap
.range f.hom = ⊤
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Module.Basis.constr_apply`：constr_apply (f : ι -> M') (x : M) : constr (
M'
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `Finsupp.mapRange.linearEquiv_apply`：∀ {α : Type u_1} {M : Type u_2} {N :
 Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring
 R₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Shrink.linearEquiv_apply`：∀ (R : Type u_1) (α : Type u_2) [inst : Small.
{v, u_2} α] [inst_1 : Semiring R] [inst_2 : AddCommMonoid α]   [inst_3 : _root_.
Module R α] (a…
· 使用引理 `equivShrink_symm_one`：equivShrink_symm_one [One α] : (equivShrink α).sym
m 1 = 1
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
The category of modules has enough projectives, since every module is a quotient
 of a free
  module.
-/
instance enoughProjectives [Small.{v} R] : EnoughProjectives (ModuleCat.{v} R) where
  presentation M :=
    let e : Basis M R (M →₀ Shrink.{v} R) := ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)⟩
    ⟨{p := ModuleCat.of R (M →₀ Shrink.{v} R)
      projective := projective_of_free e
      f := ofHom <| e.constr ℕ _root_.id
      epi := by
        rw [epi_iff_range_eq_top, LinearMap.range_eq_top]
        refine fun m ↦ ⟨Finsupp.single m 1, ?_⟩
        simp [e, Basis.constr_apply] }⟩

end ModuleCat

