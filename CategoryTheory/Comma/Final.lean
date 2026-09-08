/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Comma.StructuredArrow.CommaMap

/-!
# Finality of Projections in Comma Categories

We show that `fst L R` is final if `R` is and that `snd L R` is initial if `L` is.
As a corollary, we show that `Comma L R` with `L : A ⥤ T` and `R : B ⥤ T` is connected if `R` is
final and `A` is connected.

We then use this in a proof that derives finality of `map` between two comma categories
on a quasi-commutative diagram of functors, some of which need to be final.

Finally we prove filteredness of a `Comma L R` and finality of `snd L R`, given that `R` is final
and `A` and `B` are filtered.

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Lemma 3.4.3 -- 3.4.5
-/

public section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

namespace Comma

open Limits CategoryTheory.Functor CostructuredArrow

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]
variable (L : A ⥤ T) (R : B ⥤ T)

section Relative

/-
**CategoryTheory.Comma.isCofiltered_of_isCofiltered_costructuredArrow** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：isCofiltered_of_isCofiltered_costructuredArrow [IsCofiltered A] [IsCofilte
red B] [forall b, IsCofiltered (CostructuredArrow L (R.obj b))] : IsCofiltered (
Comma L R) where nonempty
参数：CostructuredArrow L (R.obj b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `CategoryTheory.IsCofiltered.nonempty`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C], Nonempty C
· 使用定理 `CategoryTheory.exists_eq_of_isCofiltered_costructuredArrow`：exists_eq_of
_isCofiltered_costructuredArrow {d : D} [IsCofiltered (CostructuredArrow F d)] {
c₁ c₂ : C} (s₁ : F.obj c₁ ⟶ d) (s₂ : F.obj c₂ ⟶ …
· 使用定理 `CategoryTheory.IsCofiltered.cospan`：cospan {i j j' : C} (f : j ⟶ i) (f' 
: j' ⟶ i) : exists (k : C) (g : k ⟶ j) (g' : k ⟶ j'), g ≫ f = g' ≫ f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `trivial`：True
· 使用定理 `CategoryTheory.IsCofiltered.bowtie`：bowtie {j₁ j₂ k₁ k₂ : C} (f₁ : k₁ ⟶ 
j₁) (g₁ : k₂ ⟶ j₁) (f₂ : k₁ ⟶ j₂) (g₂ : k₂ ⟶ j₂) : exists (s : C) (α : s ⟶ k₁) (
β : s ⟶ k₂), α ≫ f₁ = β …
· 使用定理 `CategoryTheory.IsCofiltered.eq_condition`：eq_condition {j j' : C} (f f' 
: j ⟶ j') : eqHom f f' ≫ f = eqHom f f' ≫ f'
· 使用引理 `CategoryTheory.Comma.hom_ext`：hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.lef
t) (h₂ : f.right = g.right) : f = g
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma isCofiltered_of_isCofiltered_costructuredArrow [IsCofiltered A] [IsCofiltered B]
    [∀ b, IsCofiltered (CostructuredArrow L (R.obj b))] : IsCofiltered (Comma L R) where
  nonempty := by
    obtain ⟨b⟩ := IsCofiltered.nonempty (C := B)
    obtain ⟨X⟩ : Nonempty (CostructuredArrow L (R.obj b)) := IsCofiltered.nonempty
    exact ⟨⟨X.left, b, X.hom⟩⟩
  toIsCofilteredOrEmpty := by
    refine ⟨fun j₁ j₂ ↦ ?_, fun j₁ j₂ u v ↦ ?_⟩
    · obtain ⟨Q⟩ : Nonempty (CostructuredArrow L (R.obj (IsCofiltered.min j₁.right j₂.right))) :=
        IsCofiltered.nonempty
      obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_isCofiltered_costructuredArrow L
        (Q.hom ≫ R.map (IsCofiltered.minToLeft j₁.right j₂.right)) j₁.hom
      obtain ⟨ib, vb₁, vb₂, heqb⟩ := exists_eq_of_isCofiltered_costructuredArrow L
        (Q.hom ≫ R.map (IsCofiltered.minToRight j₁.right j₂.right)) j₂.hom
      obtain ⟨i₀, il₀, ir₀, heq⟩ := IsCofiltered.cospan va₁ vb₁
      exact ⟨⟨i₀, IsCofiltered.min j₁.right j₂.right, L.map (il₀ ≫ va₁) ≫ Q.hom⟩,
        ⟨il₀ ≫ va₂, IsCofiltered.minToLeft _ _, by simp [← heqa]⟩,
        ⟨ir₀ ≫ vb₂, IsCofiltered.minToRight _ _, by cat_disch⟩, trivial⟩
    · obtain ⟨Q⟩ : Nonempty (CostructuredArrow L (R.obj (IsCofiltered.eq u.right v.right))) :=
        IsCofiltered.nonempty
      obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_isCofiltered_costructuredArrow L
        (Q.hom ≫ R.map (IsCofiltered.eqHom u.right v.right)) j₁.hom
      obtain ⟨i₀, α, β, hα, hβ⟩ := IsCofiltered.bowtie u.left (va₂ ≫ v.left) (𝟙 _) va₂
      have := IsCofiltered.eq_condition u.right v.right
      exact ⟨⟨i₀, IsCofiltered.eq u.right v.right, L.map (β ≫ va₁) ≫ Q.hom⟩,
        ⟨β ≫ va₂, IsCofiltered.eqHom u.right v.right, by cat_disch⟩, by cat_disch⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Comma.initial_fst_of_isCofiltered_costructuredArrow** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：initial_fst_of_isCofiltered_costructuredArrow [IsCofiltered A] [IsCofilter
ed B] [forall b, IsCofiltered (CostructuredArrow L (R.obj b))] : (fst L R).Initi
al
参数：CostructuredArrow L (R.obj b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Comma.isCofiltered_of_isCofiltered_costructuredArrow`：isC
ofiltered_of_isCofiltered_costructuredArrow [IsCofiltered A] [IsCofiltered B] [f
orall b, IsCofiltered (CostructuredArrow L (R.obj b))] : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.initial_iff_of_isCofiltered`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `CategoryTheory.IsCofiltered.nonempty`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C], Nonempty C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsCofiltered.eq_condition`：eq_condition {j j' : C} (f f' 
: j ⟶ j') : eqHom f f' ≫ f = eqHom f f' ≫ f'
-/
lemma initial_fst_of_isCofiltered_costructuredArrow [IsCofiltered A] [IsCofiltered B]
    [∀ b, IsCofiltered (CostructuredArrow L (R.obj b))] : (fst L R).Initial := by
  have := isCofiltered_of_isCofiltered_costructuredArrow L R
  rw [Functor.initial_iff_of_isCofiltered]
  refine ⟨fun a ↦ ?_, fun {a} A' s s' ↦ ?_⟩
  · obtain ⟨b⟩ := IsCofiltered.nonempty (C := B)
    obtain ⟨X⟩ : Nonempty (CostructuredArrow L (R.obj b)) := IsCofiltered.nonempty
    exact ⟨⟨IsCofiltered.min a X.left, b, L.map (IsCofiltered.minToRight a X.left) ≫ X.hom⟩,
      ⟨IsCofiltered.minToLeft a X.left⟩⟩
  · exact ⟨⟨_, A'.right, L.map (IsCofiltered.eqHom s s') ≫ A'.hom⟩,
      ⟨IsCofiltered.eqHom s s', 𝟙 A'.right, by simp⟩, IsCofiltered.eq_condition s s'⟩
/-
**CategoryTheory.Comma.initial_snd_of_isConnected_costructuredArrow** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：initial_snd_of_isConnected_costructuredArrow [forall b, IsConnected (Costr
ucturedArrow L (R.obj b))] : (snd L R).Initial where out b
参数：CostructuredArrow L (R.obj b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_adjunction`：final_of_adjunction {L : C ⥤
 D} {R : D ⥤ C} (adj : L ⊣ R) : Final R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.isConnected_iff_of_final`：isConnected_iff_of_fina
l (F : C ⥤ D) [F.Final] : IsConnected C ↔ IsConnected D
-/
lemma initial_snd_of_isConnected_costructuredArrow
    [∀ b, IsConnected (CostructuredArrow L (R.obj b))] : (snd L R).Initial where
  out b := by
    have := final_of_adjunction (costructuredArrowSndAdjunction L R b)
    rw [← isConnected_iff_of_final (costructuredArrowSndInclusion L R b)]
    infer_instance
/-
**CategoryTheory.Comma.isFiltered_of_isFiltered_structuredArrow** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：isFiltered_of_isFiltered_structuredArrow [IsFiltered A] [IsFiltered B] [fo
rall a, IsFiltered (StructuredArrow (L.obj a) R)] : IsFiltered (Comma L R)
参数：StructuredArrow (L.obj a) R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofiltered.of_equivalence`：of_equivalence (h : C ≌ D) :
 IsCofiltered D
· 使用引理 `CategoryTheory.Comma.isCofiltered_of_isCofiltered_costructuredArrow`：isC
ofiltered_of_isCofiltered_costructuredArrow [IsCofiltered A] [IsCofiltered B] [f
orall b, IsCofiltered (CostructuredArrow L (R.obj b))] : …
· 使用定理 `CategoryTheory.IsFiltered.of_equivalence`：of_equivalence (h : C ≌ D) : I
sFiltered D
-/
lemma isFiltered_of_isFiltered_structuredArrow [IsFiltered A] [IsFiltered B]
    [∀ a, IsFiltered (StructuredArrow (L.obj a) R)] : IsFiltered (Comma L R) := by
  have (a : Aᵒᵖ) : IsCofiltered (CostructuredArrow R.op (L.op.obj a)) :=
    IsCofiltered.of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))
  have : IsCofiltered (Comma R.op L.op) := isCofiltered_of_isCofiltered_costructuredArrow _ _
  exact IsFiltered.of_equivalence (opEquiv L R).symm
/-
**CategoryTheory.Comma.final_fst_of_isConnected_structuredArrow** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：final_fst_of_isConnected_structuredArrow [forall a, IsConnected (Structure
dArrow (L.obj a) R)] : (fst L R).Final
参数：StructuredArrow (L.obj a) R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.isConnected_iff_of_equivalence`：isConnected_iff_of_equiva
lence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) : IsConnected J ↔ IsConnected 
K
· 使用引理 `CategoryTheory.Comma.initial_snd_of_isConnected_costructuredArrow`：initi
al_snd_of_isConnected_costructuredArrow [forall b, IsConnected (CostructuredArro
w L (R.obj b))] : (snd L R).Initial where out b
· 使用定理 `CategoryTheory.Functor.initial_equivalence_comp`：initial_equivalence_com
p [IsEquivalence F] [Initial G] : Initial (F ⋙ G) where out d
· 使用定理 `CategoryTheory.Functor.instIsEquivalenceOppositeLeftOp`：∀ (C : Type u₁) 
[inst : CategoryTheory.Category.{v₁, u₁} C] (D : Type u₂) [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.Functor.initial_of_natIso`：initial_of_natIso {F F' : C ⥤ 
D} [Initial F] (i : F ≅ F') : Initial F' where out _
· 使用定理 `CategoryTheory.Functor.final_of_initial_op`：final_of_initial_op (F : C ⥤
 D) [Initial F.op] : Final F
-/
lemma final_fst_of_isConnected_structuredArrow
    [∀ a, IsConnected (StructuredArrow (L.obj a) R)] : (fst L R).Final := by
  have (a : Aᵒᵖ) : IsConnected (CostructuredArrow R.op (L.op.obj a)) :=
    (isConnected_iff_of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))).mp
      inferInstance
  have : (snd R.op L.op).Initial := initial_snd_of_isConnected_costructuredArrow _ _
  have : ((opFunctor L R).leftOp ⋙ snd R.op L.op).Initial :=
    initial_equivalence_comp (opEquiv L R).functor.leftOp _
  have : (fst L R).op.Initial := initial_of_natIso <| opFunctorCompSnd _ _
  apply final_of_initial_op
/-
**CategoryTheory.Comma.final_snd_of_isFiltered_structuredArrow** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Comma`。
形式化陈述：final_snd_of_isFiltered_structuredArrow [IsFiltered A] [IsFiltered B] [for
all a, IsFiltered (StructuredArrow (L.obj a) R)] : (snd L R).Final
参数：StructuredArrow (L.obj a) R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofiltered.of_equivalence`：of_equivalence (h : C ≌ D) :
 IsCofiltered D
· 使用引理 `CategoryTheory.Comma.initial_fst_of_isCofiltered_costructuredArrow`：init
ial_fst_of_isCofiltered_costructuredArrow [IsCofiltered A] [IsCofiltered B] [for
all b, IsCofiltered (CostructuredArrow L (R.obj b))] : (…
· 使用定理 `CategoryTheory.Functor.initial_equivalence_comp`：initial_equivalence_com
p [IsEquivalence F] [Initial G] : Initial (F ⋙ G) where out d
· 使用定理 `CategoryTheory.Functor.instIsEquivalenceOppositeLeftOp`：∀ (C : Type u₁) 
[inst : CategoryTheory.Category.{v₁, u₁} C] (D : Type u₂) [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.Functor.initial_of_natIso`：initial_of_natIso {F F' : C ⥤ 
D} [Initial F] (i : F ≅ F') : Initial F' where out _
· 使用定理 `CategoryTheory.Functor.final_of_initial_op`：final_of_initial_op (F : C ⥤
 D) [Initial F.op] : Final F
-/
lemma final_snd_of_isFiltered_structuredArrow [IsFiltered A] [IsFiltered B]
    [∀ a, IsFiltered (StructuredArrow (L.obj a) R)] : (snd L R).Final := by
  have (a : Aᵒᵖ) : IsCofiltered (CostructuredArrow R.op (L.op.obj a)) :=
    IsCofiltered.of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))
  have : (fst R.op L.op).Initial := initial_fst_of_isCofiltered_costructuredArrow _ _
  have : ((opFunctor L R).leftOp ⋙ fst R.op L.op).Initial :=
    initial_equivalence_comp (opEquiv L R).functor.leftOp _
  have : (snd L R).op.Initial := initial_of_natIso <| opFunctorCompFst _ _
  apply final_of_initial_op

end Relative

/-
**CategoryTheory.Comma.initial_snd** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Com
ma`。
形式化陈述：initial_snd [L.Initial] : (snd L R).Initial
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Comma.initial_snd_of_isConnected_costructuredArrow`：initi
al_snd_of_isConnected_costructuredArrow [forall b, IsConnected (CostructuredArro
w L (R.obj b))] : (snd L R).Initial where out b
· 使用定理 `CategoryTheory.Functor.Initial.out`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {F : CategoryTheor…
-/
instance initial_snd [L.Initial] : (snd L R).Initial :=
  initial_snd_of_isConnected_costructuredArrow L R
/-
**CategoryTheory.Comma.final_fst** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comma
`。
形式化陈述：final_fst [R.Final] : (fst L R).Final
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Comma.final_fst_of_isConnected_structuredArrow`：final_fst
_of_isConnected_structuredArrow [forall a, IsConnected (StructuredArrow (L.obj a
) R)] : (fst L R).Final
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…
-/
instance final_fst [R.Final] : (fst L R).Final :=
  final_fst_of_isConnected_structuredArrow L R

/-- `Comma L R` with `L : A ⥤ T` and `R : B ⥤ T` is connected if `R` is final and `A` is
connected. -/
/-
**CategoryTheory.Comma.isConnected_comma_of_final** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Comma`。
形式化陈述：isConnected_comma_of_final [IsConnected A] [R.Final] : IsConnected (Comma 
L R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.isConnected_iff_of_final`：isConnected_iff_of_fina
l (F : C ⥤ D) [F.Final] : IsConnected C ↔ IsConnected D

--- 原说明 ---
`Comma L R` with `L : A ⥤ T` and `R : B ⥤ T` is connected if `R` is final and `A
` is
connected.
-/
instance isConnected_comma_of_final [IsConnected A] [R.Final] : IsConnected (Comma L R) := by
  rwa [isConnected_iff_of_final (fst L R)]

/-- `Comma L R` with `L : A ⥤ T` and `R : B ⥤ T` is connected if `L` is initial and `B` is
connected. -/
/-
**CategoryTheory.Comma.isConnected_comma_of_initial** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Comma`。
形式化陈述：isConnected_comma_of_initial [IsConnected B] [L.Initial] : IsConnected (Co
mma L R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.isConnected_iff_of_initial`：isConnected_iff_of_in
itial (F : C ⥤ D) [F.Initial] : IsConnected C ↔ IsConnected D

--- 原说明 ---
`Comma L R` with `L : A ⥤ T` and `R : B ⥤ T` is connected if `L` is initial and 
`B` is
connected.
-/
instance isConnected_comma_of_initial [IsConnected B] [L.Initial] : IsConnected (Comma L R) := by
  rwa [isConnected_iff_of_initial (snd L R)]

set_option backward.defeqAttrib.useBackward true in
/-- Let the following diagram commute up to isomorphism:

```
      L       R
  A  ---→ T  ←--- B
  |       |       |
  | F     | H     | G
  ↓       ↓       ↓
  A' ---→ T' ←--- B'
      L'      R'
```

Let `F`, `G`, `R` and `R'` be final and `B` be filtered. Then, the induced functor between the comma
categories of the first and second row of the diagram is final. -/
/-
**CategoryTheory.Comma.map_final** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Comma
`。
形式化陈述：map_final {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] 
{T : Type u₃} [Category.{v₃} T] {L : A ⥤ T} {R : B ⥤ T} {A' : Type u₄} [Category
.{v₄} A'] {B' : Type u₅} [Category.{v₅} B'] {T' : Type u₆} [Category.{v₆} T'] {L
' : A' ⥤ T'} {R' : B' ⥤ T'} {F : A ⥤ A'} {G : B ⥤ B'} {H : T ⥤ T'} (iL : F ⋙ L' 
≅ L ⋙ H) (iR : G ⋙ R' ≅ R ⋙ H) [IsFiltered B] [R.Final] [R'.Final] [F.Final] [G.
Final] : (Comma.map iL.hom iR.inv).Final
参数：iL : F ⋙ L' ≅ L ⋙ H；iR : G ⋙ R' ≅ R ⋙ H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_natIso`：final_of_natIso {F F' : C ⥤ D} [
Final F] (i : F ≅ F') : Final F' where out _
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isConnected_iff_of_equivalence`：isConnected_iff_of_equiva
lence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) : IsConnected J ↔ IsConnected 
K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.whiskerRight_id'`：whiskerRight_id' {G : C ⥤ D} (F
 : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F)
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.StructuredArrow.final_post`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   [CategoryTheory.Is…
· 使用定理 `CategoryTheory.StructuredArrow.final_map₂_id`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   [CategoryTheory.Is…
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.StructuredArrow.final_pre`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…

--- 原说明 ---
Let the following diagram commute up to isomorphism:

```
      L       R
  A  ---→ T  ←--- B
  |       |       |
  | F     | H     | G
  ↓       ↓       ↓
  A' ---→ T' ←--- B'
      L'      R'
```

Let `F`, `G`, `R` and `R'` be final and `B` be filtered. Then, the induced funct
or between the comma
categories of the first and second row of the diagram is final.
-/
lemma map_final {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {T : Type u₃}
    [Category.{v₃} T] {L : A ⥤ T} {R : B ⥤ T} {A' : Type u₄} [Category.{v₄} A'] {B' : Type u₅}
    [Category.{v₅} B'] {T' : Type u₆} [Category.{v₆} T'] {L' : A' ⥤ T'} {R' : B' ⥤ T'} {F : A ⥤ A'}
    {G : B ⥤ B'} {H : T ⥤ T'} (iL : F ⋙ L' ≅ L ⋙ H) (iR : G ⋙ R' ≅ R ⋙ H) [IsFiltered B]
    [R.Final] [R'.Final] [F.Final] [G.Final] :
    (Comma.map iL.hom iR.inv).Final := ⟨fun ⟨i₂, j₂, u₂⟩ => by
  have := final_of_natIso iR
  rw [isConnected_iff_of_equivalence (StructuredArrow.commaMapEquivalence iL.hom iR.inv _)]
  have : StructuredArrow.map₂ u₂ iR.hom ≅ StructuredArrow.post j₂ G R' ⋙
      StructuredArrow.map₂ (G := 𝟭 _) (F := 𝟭 _) (R' := R ⋙ H) u₂ iR.hom ⋙
      StructuredArrow.pre _ R H :=
    eqToIso (by
      congr
      · simp
      · ext; simp) ≪≫
    (StructuredArrow.map₂CompMap₂Iso _ _ _ _).symm ≪≫
    isoWhiskerLeft _ ((StructuredArrow.map₂CompMap₂Iso _ _ _ _).symm ≪≫
      isoWhiskerLeft _ (StructuredArrow.preIsoMap₂ _ _ _).symm) ≪≫
    isoWhiskerRight (StructuredArrow.postIsoMap₂ j₂ G R').symm _
  have := final_of_natIso this.symm
  rw [IsIso.Iso.inv_inv]
  infer_instance⟩

section Filtered

/-- Let `A` and `B` be filtered categories, `R : B ⥤ T` be final and `L : A ⥤ T`. Then, the
comma category `Comma L R` is filtered. -/
/-
**CategoryTheory.Comma.isFiltered_of_final** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Comma`。
形式化陈述：isFiltered_of_final [IsFiltered A] [IsFiltered B] [R.Final] : IsFiltered (
Comma L R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.final_iff_isFiltered_structuredArrow`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用引理 `CategoryTheory.Comma.isFiltered_of_isFiltered_structuredArrow`：isFiltere
d_of_isFiltered_structuredArrow [IsFiltered A] [IsFiltered B] [forall a, IsFilte
red (StructuredArrow (L.obj a) R)] : IsFiltered (Co…

--- 原说明 ---
Let `A` and `B` be filtered categories, `R : B ⥤ T` be final and `L : A ⥤ T`. Th
en, the
comma category `Comma L R` is filtered.
-/
instance isFiltered_of_final [IsFiltered A] [IsFiltered B] [R.Final] : IsFiltered (Comma L R) := by
  have := R.final_iff_isFiltered_structuredArrow.mp inferInstance
  exact isFiltered_of_isFiltered_structuredArrow L R

/-- Let `A` and `B` be cofiltered categories, `L : A ⥤ T` be initial and `R : B ⥤ T`. Then, the
comma category `Comma L R` is cofiltered. -/
/-
**CategoryTheory.Comma.isCofiltered_of_initial** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Comma`。
形式化陈述：isCofiltered_of_initial [IsCofiltered A] [IsCofiltered B] [L.Initial] : Is
Cofiltered (Comma L R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.initial_iff_isCofiltered_costructuredArrow`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用引理 `CategoryTheory.Comma.isCofiltered_of_isCofiltered_costructuredArrow`：isC
ofiltered_of_isCofiltered_costructuredArrow [IsCofiltered A] [IsCofiltered B] [f
orall b, IsCofiltered (CostructuredArrow L (R.obj b))] : …

--- 原说明 ---
Let `A` and `B` be cofiltered categories, `L : A ⥤ T` be initial and `R : B ⥤ T`
. Then, the
comma category `Comma L R` is cofiltered.
-/
lemma isCofiltered_of_initial [IsCofiltered A] [IsCofiltered B] [L.Initial] :
    IsCofiltered (Comma L R) := by
  have := L.initial_iff_isCofiltered_costructuredArrow.mp inferInstance
  exact isCofiltered_of_isCofiltered_costructuredArrow L R

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `A` and `B` be filtered categories, `R : B ⥤ T` be final and `R : A ⥤ T`. Then, the
projection `snd L R : Comma L R ⥤ B` is final. -/
/-
**CategoryTheory.Comma.final_snd** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comma
`。
形式化陈述：final_snd [IsFiltered A] [IsFiltered B] [R.Final] : (snd L R).Final
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.final_iff_isFiltered_structuredArrow`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用引理 `CategoryTheory.Comma.final_snd_of_isFiltered_structuredArrow`：final_snd_
of_isFiltered_structuredArrow [IsFiltered A] [IsFiltered B] [forall a, IsFiltere
d (StructuredArrow (L.obj a) R)] : (snd L R).Final

--- 原说明 ---
Let `A` and `B` be filtered categories, `R : B ⥤ T` be final and `R : A ⥤ T`. Th
en, the
projection `snd L R : Comma L R ⥤ B` is final.
-/
instance final_snd [IsFiltered A] [IsFiltered B] [R.Final] : (snd L R).Final := by
  have := R.final_iff_isFiltered_structuredArrow.mp inferInstance
  exact final_snd_of_isFiltered_structuredArrow L R

/-- Let `A` and `B` be cofiltered categories, `L : A ⥤ T` be initial and `R : B ⥤ T`. Then, the
projection `fst L R : Comma L R ⥤ A` is initial. -/
/-
**CategoryTheory.Comma.initial_fst** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Com
ma`。
形式化陈述：initial_fst [IsCofiltered A] [IsCofiltered B] [L.Initial] : (fst L R).Init
ial
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.initial_iff_isCofiltered_costructuredArrow`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用引理 `CategoryTheory.Comma.initial_fst_of_isCofiltered_costructuredArrow`：init
ial_fst_of_isCofiltered_costructuredArrow [IsCofiltered A] [IsCofiltered B] [for
all b, IsCofiltered (CostructuredArrow L (R.obj b))] : (…

--- 原说明 ---
Let `A` and `B` be cofiltered categories, `L : A ⥤ T` be initial and `R : B ⥤ T`
. Then, the
projection `fst L R : Comma L R ⥤ A` is initial.
-/
instance initial_fst [IsCofiltered A] [IsCofiltered B] [L.Initial] : (fst L R).Initial := by
  have := L.initial_iff_isCofiltered_costructuredArrow.mp inferInstance
  exact initial_fst_of_isCofiltered_costructuredArrow L R

end Filtered

end Comma

end CategoryTheory

