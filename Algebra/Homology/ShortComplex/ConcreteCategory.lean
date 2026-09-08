/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Exactness of short complexes in concrete abelian categories

If an additive concrete category `C` has an additive forgetful functor to `Ab`
which preserves homology, then a short complex `S` in `C` is exact
if and only if it is so after applying the functor `forget₂ C Ab`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

section

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC] [HasForget₂ C Ab]

@[simp]
/-
**CategoryTheory.ShortComplex.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.ShortComplex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {FC : C → C → Typ
e u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) (CC X) (CC Y)]
 [inst_2 : CategoryTheory.ConcreteCategory C FC]   [inst_3 : CategoryTheory.HasF
orget₂ C Ab] [inst_4 : CategoryTheory.Limits.HasZeroMorphisms C]   [(CategoryThe
ory.forget₂ C Ab).PreservesZeroMorphisms] (S : CategoryTheory.ShortComplex C)   
(x : ↑((CategoryTheory.forget₂ C Ab).obj S.X₁)),   (CategoryTheory.ConcreteCateg
ory.hom ((CategoryTheory.forget₂ C Ab).map S.g))       ((CategoryTheory.Concrete
Category.hom ((CategoryTheory.forget₂ C Ab).map S.f)) x) =     0
参数：X Y : C；FC X Y；CC X；CC Y；CategoryTheory.forget₂ C Ab；S : CategoryTheory.Short
Complex C；x : ↑((CategoryTheory.forget₂ C Ab).obj S.X₁)；CategoryTheory.ConcreteC
ategory.hom ((CategoryTheory.forget₂ C Ab).map S.g)；(CategoryTheory.ConcreteCate
gory.hom ((CategoryTheory.forget₂ C Ab).map S.f)) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
-/
lemma ShortComplex.zero_apply
    [Limits.HasZeroMorphisms C] [(forget₂ C Ab).PreservesZeroMorphisms]
    (S : ShortComplex C) (x : (forget₂ C Ab).obj S.X₁) :
    ((forget₂ C Ab).map S.g) (((forget₂ C Ab).map S.f) x) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, S.zero, Functor.map_zero]
  rfl

section preadditive

variable [Preadditive C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  (S : ShortComplex C)

section
variable [HasZeroObject C]

/-
**CategoryTheory.Preadditive.mono_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Preadditive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {FC : C → C → Typ
e u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) (CC X) (CC Y)]
 [inst_2 : CategoryTheory.ConcreteCategory C FC]   [inst_3 : CategoryTheory.HasF
orget₂ C Ab] [inst_4 : CategoryTheory.Preadditive C]   [inst_5 : (CategoryTheory
.forget₂ C Ab).Additive] [(CategoryTheory.forget₂ C Ab).PreservesHomology]   [Ca
tegoryTheory.Limits.HasZeroObject C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Mon
o f ↔     Function.Injective ⇑(CategoryTheory.ConcreteCategory.hom ((CategoryThe
ory.forget₂ C Ab).map f))
参数：X Y : C；FC X Y；CC X；CC Y；CategoryTheory.forget₂ C Ab；CategoryTheory.forget₂ C
 Ab；f : X ⟶ Y；CategoryTheory.ConcreteCategory.hom ((CategoryTheory.forget₂ C Ab)
.map f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddCommGrpCat.mono_iff_injective`：∀ {A B : AddCommGrpCat} (f : A ⟶ B), C
ategoryTheory.Mono f ↔ Function.Injective ⇑(CategoryTheory.ConcreteCategory.hom 
f)
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesMonomorphisms`：∀ {C : Type u_1} {D :
 Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma Preadditive.mono_iff_injective {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective ((forget₂ C Ab).map f) := by
  rw [← AddCommGrpCat.mono_iff_injective]
  constructor
  · intro
    infer_instance
  · apply Functor.mono_of_mono_map
/-
**CategoryTheory.Preadditive.mono_iff_injective'** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Preadditive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {FC : C → C → Typ
e u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) (CC X) (CC Y)]
 [inst_2 : CategoryTheory.ConcreteCategory C FC]   [inst_3 : CategoryTheory.HasF
orget₂ C Ab] [inst_4 : CategoryTheory.Preadditive C]   [inst_5 : (CategoryTheory
.forget₂ C Ab).Additive] [(CategoryTheory.forget₂ C Ab).PreservesHomology]   [Ca
tegoryTheory.Limits.HasZeroObject C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Mon
o f ↔ Function.Injective ⇑(CategoryTheory.ConcreteCategory.hom f)
参数：X Y : C；FC X Y；CC X；CC Y；CategoryTheory.forget₂ C Ab；CategoryTheory.forget₂ C
 Ab；f : X ⟶ Y；CategoryTheory.ConcreteCategory.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.monomorphisms`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.mo
nomorphisms C).RespectsIso
· 使用定理 `CategoryTheory.HasForget₂.forget_comp`：∀ {C : Type u_1} {inst : Category
Theory.Category.{v_1, u_1} C} {FC : outParam (C → C → Type u_2)}   {CC : outPara
m (C → Type w)} {inst_1 : o…
-/
lemma Preadditive.mono_iff_injective' {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f := by
  simp only [mono_iff_injective, ← CategoryTheory.ofHom_mono_iff_injective]
  apply (MorphismProperty.monomorphisms (Type w)).arrow_mk_iso_iff
  have e : forget₂ C Ab ⋙ forget Ab ≅ forget C := eqToIso (HasForget₂.forget_comp)
  exact Arrow.isoOfNatIso e (Arrow.mk f)
/-
**CategoryTheory.Preadditive.epi_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Preadditive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {FC : C → C → Typ
e u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) (CC X) (CC Y)]
 [inst_2 : CategoryTheory.ConcreteCategory C FC]   [inst_3 : CategoryTheory.HasF
orget₂ C Ab] [inst_4 : CategoryTheory.Preadditive C]   [inst_5 : (CategoryTheory
.forget₂ C Ab).Additive] [(CategoryTheory.forget₂ C Ab).PreservesHomology]   [Ca
tegoryTheory.Limits.HasZeroObject C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Epi
 f ↔     Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom ((CategoryThe
ory.forget₂ C Ab).map f))
参数：X Y : C；FC X Y；CC X；CC Y；CategoryTheory.forget₂ C Ab；CategoryTheory.forget₂ C
 Ab；f : X ⟶ Y；CategoryTheory.ConcreteCategory.hom ((CategoryTheory.forget₂ C Ab)
.map f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddCommGrpCat.epi_iff_surjective`：∀ {A B : AddCommGrpCat} (f : A ⟶ B), C
ategoryTheory.Epi f ↔ Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom 
f)
· 使用定理 `CategoryTheory.Functor.instPreservesEpimorphisms`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma Preadditive.epi_iff_surjective {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective ((forget₂ C Ab).map f) := by
  rw [← AddCommGrpCat.epi_iff_surjective]
  constructor
  · intro
    infer_instance
  · apply Functor.epi_of_epi_map
/-
**CategoryTheory.Preadditive.epi_iff_surjective'** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Preadditive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {FC : C → C → Typ
e u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) (CC X) (CC Y)]
 [inst_2 : CategoryTheory.ConcreteCategory C FC]   [inst_3 : CategoryTheory.HasF
orget₂ C Ab] [inst_4 : CategoryTheory.Preadditive C]   [inst_5 : (CategoryTheory
.forget₂ C Ab).Additive] [(CategoryTheory.forget₂ C Ab).PreservesHomology]   [Ca
tegoryTheory.Limits.HasZeroObject C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Epi
 f ↔ Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom f)
参数：X Y : C；FC X Y；CC X；CC Y；CategoryTheory.forget₂ C Ab；CategoryTheory.forget₂ C
 Ab；f : X ⟶ Y；CategoryTheory.ConcreteCategory.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.epimorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.epi
morphisms C).RespectsIso
· 使用定理 `CategoryTheory.HasForget₂.forget_comp`：∀ {C : Type u_1} {inst : Category
Theory.Category.{v_1, u_1} C} {FC : outParam (C → C → Type u_2)}   {CC : outPara
m (C → Type w)} {inst_1 : o…
-/
lemma Preadditive.epi_iff_surjective' {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  simp only [epi_iff_surjective, ← CategoryTheory.ofHom_epi_iff_surjective]
  apply (MorphismProperty.epimorphisms (Type w)).arrow_mk_iso_iff
  have e : forget₂ C Ab ⋙ forget Ab ≅ forget C := eqToIso (HasForget₂.forget_comp)
  exact Arrow.isoOfNatIso e (Arrow.mk f)

end

namespace ShortComplex

/-
**CategoryTheory.ShortComplex.exact_iff_exact_map_forget** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact_iff_exact_map_forget₂ [S.HasHomology] :
    S.Exact ↔ (S.map (forget₂ C Ab)).Exact :=
  (S.exact_map_iff_of_faithful (forget₂ C Ab)).symm
/-
**CategoryTheory.ShortComplex.exact_iff_of_hasForget** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_of_hasForget [S.HasHomology] : S.Exact ↔ forall (x₂ : (forget₂ C
 Ab).obj S.X₂) (_ : ((forget₂ C Ab).map S.g) x₂ = 0), exists (x₁ : (forget₂ C Ab
).obj S.X₁), ((forget₂ C Ab).map S.f) x₁ = x₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_exact_map_forget₂`：exact_iff_exact
_map_forget₂ [S.HasHomology] : S.Exact ↔ (S.map (forget₂ C Ab)).Exact
· 使用引理 `CategoryTheory.ShortComplex.ab_exact_iff`：ab_exact_iff : S.Exact ↔ foral
l (x₂ : S.X₂) (_ : S.g x₂ = 0), exists (x₁ : S.X₁), S.f x₁ = x₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma exact_iff_of_hasForget [S.HasHomology] :
    S.Exact ↔ ∀ (x₂ : (forget₂ C Ab).obj S.X₂) (_ : ((forget₂ C Ab).map S.g) x₂ = 0),
      ∃ (x₁ : (forget₂ C Ab).obj S.X₁), ((forget₂ C Ab).map S.f) x₁ = x₂ := by
  rw [S.exact_iff_exact_map_forget₂, ab_exact_iff]
  rfl

variable {S}
/-
**CategoryTheory.ShortComplex.ShortExact.injective_f** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {FC : C → C → Typ
e u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) (CC X) (CC Y)]
 [inst_2 : CategoryTheory.ConcreteCategory C FC]   [inst_3 : CategoryTheory.HasF
orget₂ C Ab] [inst_4 : CategoryTheory.Preadditive C]   [inst_5 : (CategoryTheory
.forget₂ C Ab).Additive] [(CategoryTheory.forget₂ C Ab).PreservesHomology]   {S 
: CategoryTheory.ShortComplex C} [CategoryTheory.Limits.HasZeroObject C],   S.Sh
ortExact → Function.Injective ⇑(CategoryTheory.ConcreteCategory.hom ((CategoryTh
eory.forget₂ C Ab).map S.f))
参数：X Y : C；FC X Y；CC X；CC Y；CategoryTheory.forget₂ C Ab；CategoryTheory.forget₂ C
 Ab；CategoryTheory.ConcreteCategory.hom ((CategoryTheory.forget₂ C Ab).map S.f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Preadditive.mono_iff_injective`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [ins
t_1 : (X Y : C) → FunLike (FC X Y) …
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
-/
lemma ShortExact.injective_f [HasZeroObject C] (hS : S.ShortExact) :
    Function.Injective ((forget₂ C Ab).map S.f) := by
  rw [← Preadditive.mono_iff_injective]
  exact hS.mono_f
/-
**CategoryTheory.ShortComplex.ShortExact.surjective_g** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {FC : C → C → Typ
e u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) (CC X) (CC Y)]
 [inst_2 : CategoryTheory.ConcreteCategory C FC]   [inst_3 : CategoryTheory.HasF
orget₂ C Ab] [inst_4 : CategoryTheory.Preadditive C]   [inst_5 : (CategoryTheory
.forget₂ C Ab).Additive] [(CategoryTheory.forget₂ C Ab).PreservesHomology]   {S 
: CategoryTheory.ShortComplex C} [CategoryTheory.Limits.HasZeroObject C],   S.Sh
ortExact → Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom ((CategoryT
heory.forget₂ C Ab).map S.g))
参数：X Y : C；FC X Y；CC X；CC Y；CategoryTheory.forget₂ C Ab；CategoryTheory.forget₂ C
 Ab；CategoryTheory.ConcreteCategory.hom ((CategoryTheory.forget₂ C Ab).map S.g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Preadditive.epi_iff_surjective`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [ins
t_1 : (X Y : C) → FunLike (FC X Y) …
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
-/
lemma ShortExact.surjective_g [HasZeroObject C] (hS : S.ShortExact) :
    Function.Surjective ((forget₂ C Ab).map S.g) := by
  rw [← Preadditive.epi_iff_surjective]
  exact hS.epi_g

variable (S)

/-- Constructor for cycles of short complexes in a concrete category. -/
/-
**CategoryTheory.ShortComplex.cyclesMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：cyclesMk [S.HasHomology] (x₂ : (forget₂ C Ab).obj S.X₂) (hx₂ : ((forget₂ C
 Ab).map S.g) x₂ = 0) : (forget₂ C Ab).obj S.cycles
参数：x₂ : (forget₂ C Ab).obj S.X₂；hx₂ : ((forget₂ C Ab).map S.g) x₂ = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for cycles of short complexes in a concrete category.
-/
noncomputable def cyclesMk [S.HasHomology] (x₂ : (forget₂ C Ab).obj S.X₂)
    (hx₂ : ((forget₂ C Ab).map S.g) x₂ = 0) :
    (forget₂ C Ab).obj S.cycles :=
  (S.mapCyclesIso (forget₂ C Ab)).hom ((ShortComplex.abCyclesIso _).inv ⟨x₂, hx₂⟩)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.ShortComplex.i_cyclesMk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.ShortComplex`。
形式化陈述：i_cyclesMk [S.HasHomology] (x₂ : (forget₂ C Ab).obj S.X₂) (hx₂ : ((forget₂
 C Ab).map S.g) x₂ = 0) : (forget₂ C Ab).map S.iCycles (S.cyclesMk x₂ hx₂) = x₂
参数：x₂ : (forget₂ C Ab).obj S.X₂；hx₂ : ((forget₂ C Ab).map S.g) x₂ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用引理 `CategoryTheory.ShortComplex.abCyclesIso_inv_apply_iCycles`：abCyclesIso_i
nv_apply_iCycles (x : AddMonoidHom.ker S.g.hom) : S.iCycles (S.abCyclesIso.inv x
) = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.ShortComplex.mapCyclesIso_hom_iCycles`：mapCyclesIso_hom_i
Cycles [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] : (S.mapCyclesIso F).ho
m ≫ F.map S.iCycles = (S.map F).iCycles
-/
lemma i_cyclesMk [S.HasHomology] (x₂ : (forget₂ C Ab).obj S.X₂)
    (hx₂ : ((forget₂ C Ab).map S.g) x₂ = 0) :
    (forget₂ C Ab).map S.iCycles (S.cyclesMk x₂ hx₂) = x₂ := by
  dsimp [cyclesMk]
  -- `abCyclesIso_inv_apply_iCycles` is not in `simp`-normal form, so we first
  -- have to simplify it.
  have := abCyclesIso_inv_apply_iCycles (S.map (forget₂ C Ab)) ⟨x₂, hx₂⟩
  simp only [map_X₂, map_X₃, map_g] at this
  rw [← ConcreteCategory.comp_apply, S.mapCyclesIso_hom_iCycles (forget₂ C Ab), this]

end ShortComplex

end preadditive

end

section abelian

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC] [HasForget₂ C Ab]
  [Abelian C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]

namespace ShortComplex

namespace SnakeInput

variable (D : SnakeInput C)

set_option backward.isDefEq.respectTransparency false in
/-- This lemma allows the computation of the connecting homomorphism
`D.δ` when `D : SnakeInput C` and `C` is a concrete category. -/
/-
**CategoryTheory.ShortComplex.SnakeInput.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ShortComplex.SnakeInput`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma allows the computation of the connecting homomorphism
`D.δ` when `D : SnakeInput C` and `C` is a concrete category.
-/
lemma δ_apply (x₃ : ToType (D.L₀.X₃)) (x₂ : ToType (D.L₁.X₂)) (x₁ : ToType (D.L₂.X₁))
    (h₂ : D.L₁.g x₂ = D.v₀₁.τ₃ x₃) (h₁ : D.L₂.f x₁ = D.v₁₂.τ₂ x₂) :
    D.δ x₃ = D.v₂₃.τ₁ x₁ := by
  have := (forget₂ C Ab).preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteLimits (forget C) := by
    have : forget₂ C Ab ⋙ forget Ab = forget C := HasForget₂.forget_comp
    simpa only [← this] using comp_preservesFiniteLimits _ _
  have eq := CategoryTheory.congr_fun (D.snd_δ)
    (Limits.Concrete.pullbackMk D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂)
  have eq₁ := Concrete.pullbackMk_fst D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂
  have eq₂ := Concrete.pullbackMk_snd D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at eq
  rw [eq₂] at eq
  refine eq.trans (CategoryTheory.congr_arg (D.v₂₃.τ₁) ?_)
  apply (Preadditive.mono_iff_injective' D.L₂.f).1 inferInstance
  rw [← ConcreteCategory.comp_apply, φ₁_L₂_f]
  dsimp [φ₂]
  rw [ConcreteCategory.comp_apply, eq₁]
  exact h₁.symm

/-- This lemma allows the computation of the connecting homomorphism
`D.δ` when `D : SnakeInput C` and `C` is a concrete category. -/
/-
**CategoryTheory.ShortComplex.SnakeInput.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ShortComplex.SnakeInput`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma allows the computation of the connecting homomorphism
`D.δ` when `D : SnakeInput C` and `C` is a concrete category.
-/
lemma δ_apply' (x₃ : (forget₂ C Ab).obj D.L₀.X₃)
    (x₂ : (forget₂ C Ab).obj D.L₁.X₂) (x₁ : (forget₂ C Ab).obj D.L₂.X₁)
    (h₂ : (forget₂ C Ab).map D.L₁.g x₂ = (forget₂ C Ab).map D.v₀₁.τ₃ x₃)
    (h₁ : (forget₂ C Ab).map D.L₂.f x₁ = (forget₂ C Ab).map D.v₁₂.τ₂ x₂) :
    (forget₂ C Ab).map D.δ x₃ = (forget₂ C Ab).map D.v₂₃.τ₁ x₁ := by
  have e : forget₂ C Ab ⋙ forget Ab ≅ forget C := eqToIso (HasForget₂.forget_comp)
  apply (ofHom_mono_iff_injective (e.hom.app _)).1 inferInstance
  refine ((ConcreteCategory.congr_hom (e.hom.naturality D.δ) x₃).trans ?_).trans
    (ConcreteCategory.congr_hom (e.hom.naturality D.v₂₃.τ₁).symm x₁)
  exact D.δ_apply _ _ _
    (((ConcreteCategory.congr_hom (e.hom.naturality D.L₁.g) x₂).symm.trans (by simp_all)).trans
      (ConcreteCategory.congr_hom (e.hom.naturality D.v₀₁.τ₃) x₃))
    (((ConcreteCategory.congr_hom (e.hom.naturality D.L₂.f) x₁).symm.trans (by simp_all)).trans
      (ConcreteCategory.congr_hom (e.hom.naturality D.v₁₂.τ₂) x₂))

end SnakeInput

end ShortComplex

end abelian

end CategoryTheory

