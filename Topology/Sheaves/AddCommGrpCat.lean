/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib.Topology.Sheaves.Abelian

/-!
# Sheaves of abelian groups.

Results for sheaves of abelian groups on topological spaces.

-/

public section

universe u

open TopologicalSpace Opposite CategoryTheory TopCat
open scoped AlgebraicGeometry

variable {X : TopCat.{u}} {U : Opens X}

namespace TopCat

set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.Presheaf.sections_exact_of_exact** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Pres
heaf`。
形式化陈述：∀ {X : TopCat} {U : TopologicalSpace.Opens ↑X} {S : CategoryTheory.ShortCo
mplex (TopCat.Presheaf AddCommGrpCat X)},   S.Exact →     ∀ {s : ↑(S.X₂.obj (Opp
osite.op U))},       (CategoryTheory.ConcreteCategory.hom (S.g.app (Opposite.op 
U))) s = 0 →         ∃ t, (CategoryTheory.ConcreteCategory.hom (S.f.app (Opposit
e.op U))) t = s
参数：TopCat.Presheaf AddCommGrpCat X；S.X₂.obj (Opposite.op U)；CategoryTheory.Concr
eteCategory.hom (S.g.app (Opposite.op U))；CategoryTheory.ConcreteCategory.hom (S
.f.app (Opposite.op U))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_evaluation_obj`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用引理 `CategoryTheory.ShortComplex.ab_exact_iff`：ab_exact_iff : S.Exact ↔ foral
l (x₂ : S.X₂) (_ : S.g x₂ = 0), exists (x₁ : S.X₁), S.f x₁ = x₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.instAdditiveObjEvaluation`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
 {J : Type u_4}   [inst_2 : CategoryTh…
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `CategoryTheory.Functor.exact_tfae`：exact_tfae : List.TFAE [ forall (S : 
ShortComplex C), S.ShortExact -> (S.map F).ShortExact, forall (S : ShortComplex 
C), S.Exact -> (S.map F…
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteLimitsFunctorObjEvaluationOfHas
FiniteLimits`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {K 
: Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} K] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasCountableLimits`：∀ (C : Type
 u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasCo
untableLimits C],   CategoryTheory.Limits.HasFini…
· 使用定理 `CategoryTheory.Limits.hasCountableLimits_of_hasLimits`：∀ (C : Type u_1) 
[inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasLimits C
],   CategoryTheory.Limits.HasCountableLimi…
· 使用定理 `AddCommGrpCat.hasLimits`：CategoryTheory.Limits.HasLimits AddCommGrpCat
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteColimitsFunctorObjEvaluationOfH
asFiniteColimits`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C]
 {K : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} K] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasCountableColimits`：∀ (C : 
Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.H
asCountableColimits C],   CategoryTheory.Limits.HasFi…
· 使用定理 `CategoryTheory.Limits.hasCountableColimits_of_hasColimits`：∀ (C : Type u
_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasColi
mits C],   CategoryTheory.Limits.HasCountableCo…
· 使用定理 `AddCommGrpCat.hasColimitsOfSize`：∀ [UnivLE.{u, w}], CategoryTheory.Limit
s.HasColimitsOfSize.{v, u, w, w + 1} AddCommGrpCat
-/
theorem Presheaf.sections_exact_of_exact
    {S : ShortComplex (Presheaf AddCommGrpCat.{u} X)}
    (hS : S.Exact) {s : S.X₂.obj (Opposite.op U)} (h : S.g.app (Opposite.op U) s = 0) :
    ∃ (t : S.X₁.obj (Opposite.op U)), S.f.app (Opposite.op U) t = s := by
  dsimp [Presheaf] at S
  let F := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op U)
  exact (ShortComplex.ab_exact_iff (S.map F)).mp (((Functor.exact_tfae F).out 1 3 rfl rfl).mpr
    ⟨inferInstance, inferInstance⟩ S hS) _ h
/-
**TopCat.Sheaf.sections_exact_of_left_exact** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Sh
eaf`。
形式化陈述：∀ {X : TopCat} {U : TopologicalSpace.Opens ↑X} {S : CategoryTheory.ShortCo
mplex (TopCat.Sheaf AddCommGrpCat X)},   S.Exact →     CategoryTheory.Mono S.f →
       ∀ (s : ↑(S.X₂.obj.obj (Opposite.op U))),         (CategoryTheory.Concrete
Category.hom (S.g.hom.app (Opposite.op U))) s = 0 →           ∃ t, (CategoryTheo
ry.ConcreteCategory.hom (S.f.hom.app (Opposite.op U))) t = s
参数：TopCat.Sheaf AddCommGrpCat X；s : ↑(S.X₂.obj.obj (Opposite.op U))；CategoryTheo
ry.ConcreteCategory.hom (S.g.hom.app (Opposite.op U))；CategoryTheory.ConcreteCat
egory.hom (S.f.hom.app (Opposite.op U))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOf
SmallOppositeCover`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J 
: CategoryTheory.GrothendieckTopology C) (D : Type w)   [inst_1 : CategoryTheory
…
· 使用定理 `AddCommGrpCat.hasLimit`：∀ {J : Type v} [inst : CategoryTheory.Category.{
w, v} J] (F : CategoryTheory.Functor J AddCommGrpCat)   [Small.{u, max u v} ↑(F.
comp (Catego…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AddCommGrpCat.hasColimitsOfShape`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] [Small.{w, u} J],   CategoryTheory.Limits.HasColimitsOfShape 
J AddCommGrpCat
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits`：Categor
yTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `AddCommGrpCat.forget_reflects_isos`：(CategoryTheory.forget AddCommGrpCat
).ReflectsIsomorphisms
· 使用定理 `AddCommGrpCat.forget_preservesLimitsOfShape`：∀ {J : Type v} [inst : Cate
goryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.Preserve
sLimitsOfShape J (CategoryTheory.…
· 使用定理 `AddCommGrpCat.forget_preservesLimits`：CategoryTheory.Limits.PreservesLim
its (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasCountableLimits`：∀ (C : Type
 u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasCo
untableLimits C],   CategoryTheory.Limits.HasFini…
· 使用定理 `CategoryTheory.Limits.hasCountableLimits_of_hasLimits`：∀ (C : Type u_1) 
[inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasLimits C
],   CategoryTheory.Limits.HasCountableLimi…
· 使用定理 `AddCommGrpCat.hasLimits`：CategoryTheory.Limits.HasLimits AddCommGrpCat
· 使用定理 `TopCat.Presheaf.sections_exact_of_exact`：∀ {X : TopCat} {U : Topological
Space.Opens ↑X} {S : CategoryTheory.ShortComplex (TopCat.Presheaf AddCommGrpCat 
X)},   S.Exact →     ∀ {s : ↑…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `TopCat.Sheaf.instAdditivePresheafForget`：∀ {X : TopCat} {C : Type v₁} [i
nst : CategoryTheory.Category.{v₂, v₁} C]   [inst_1 : CategoryTheory.HasSheafify
 (Opens.grothendieckTopology …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `CategoryTheory.Functor.preservesFiniteLimits_tfae`：preservesFiniteLimits
_tfae : List.TFAE [ forall (S : ShortComplex C), S.ShortExact -> (S.map F).Exact
 ∧ Mono (F.map S.f), forall (S : ShortC…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesLimits_of_createsLimits_and_hasLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `TopCat.instHasLimitsPresheaf`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] [CategoryTheory.Limits.HasLimits C] (X : TopCat),   CategoryTheor
y.Limits.HasLimits…
-/
lemma Sheaf.sections_exact_of_left_exact {S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)}
    (hS : S.Exact) (hf : Mono S.f) (s : S.X₂.obj.obj (Opposite.op U))
    (h : S.g.hom.app (Opposite.op U) s = 0) :
    ∃ (t : S.X₁.obj.obj (Opposite.op U)), S.f.hom.app (Opposite.op U) t = s :=
  Presheaf.sections_exact_of_exact
    (((Functor.preservesFiniteLimits_tfae (Sheaf.forget ..)).out 1 3 rfl rfl).mpr
    inferInstance S ⟨hS, hf⟩).left h
/-
**TopCat.Presheaf.restrict_sum** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Presheaf`。
形式化陈述：∀ {X : TopCat} {U V : TopologicalSpace.Opens ↑X} {F : TopCat.Presheaf AddC
ommGrpCat X} (h : V ≤ U)   (s t : ↑(F.obj (Opposite.op U))),   TopCat.Presheaf.r
estrictOpen (s + t) V h = TopCat.Presheaf.restrictOpen s V h + TopCat.Presheaf.r
estrictOpen t V h
参数：h : V ≤ U；s t : ↑(F.obj (Opposite.op U))；s + t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Presheaf.restrict_sum {V : Opens X} {F : Presheaf AddCommGrpCat X} (h : V ≤ U)
    (s t : F.obj (op U)) : (s + t) |_ V = s |_ V + t |_ V := by
  delta Presheaf.restrictOpen Presheaf.restrict
  cat_disch

end TopCat

