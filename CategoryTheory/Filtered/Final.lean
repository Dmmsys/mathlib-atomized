/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Final.Connected
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Sifted

/-!
# Final functors with filtered (co)domain

If `C` is a filtered category, then the usual equivalent conditions for a functor `F : C ⥤ D` to be
final can be restated. We show:

* `final_iff_of_isFiltered`: a concrete description of finality which is sometimes a convenient way
  to show that a functor is final.
* `final_iff_isFiltered_structuredArrow`: `F` is final if and only if `StructuredArrow d F` is
  filtered for all `d : D`, which strengthens the usual statement that `F` is final if and only
  if `StructuredArrow d F` is connected for all `d : D`.
* Under categories of objects of filtered categories are filtered and their forgetful functors
  are final.
* If `D` is a filtered category and `F : C ⥤ D` is fully faithful and satisfies the additional
  condition that for every `d : D` there is an object `c : D` and a morphism `d ⟶ F.obj c`, then
  `C` is filtered and `F` is final.
* Finality and initiality of diagonal functors `diag : C ⥤ C × C` and of projection functors
  of (co)structured arrow categories.
* Finality of `StructuredArrow.post`, given the finality of its arguments.

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Section 3.2

-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/-- If `StructuredArrow d F` is filtered for any `d : D`, then `F : C ⥤ D` is final. This is
simply because filtered categories are connected. More profoundly, the converse is also true if
`C` is filtered, see `final_iff_isFiltered_structuredArrow`. -/
/-
**CategoryTheory.Functor.final_of_isFiltered_structuredArrow** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [∀ (d : D), CategoryTheory.IsFiltered (CategoryTheory.StructuredArrow d F)], F.
Final
参数：F : CategoryTheory.Functor C D；d : D；CategoryTheory.StructuredArrow d F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFiltered.isConnected`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [CategoryTheory.IsFiltered C], CategoryTheory.IsConnecte
d C

--- 原说明 ---
If `StructuredArrow d F` is filtered for any `d : D`, then `F : C ⥤ D` is final.
 This is
simply because filtered categories are connected. More profoundly, the converse 
is also true if
`C` is filtered, see `final_iff_isFiltered_structuredArrow`.
-/
theorem Functor.final_of_isFiltered_structuredArrow [∀ d, IsFiltered (StructuredArrow d F)] :
    Final F where
  out _ := IsFiltered.isConnected _

/-- If `CostructuredArrow F d` is filtered for any `d : D`, then `F : C ⥤ D` is initial. This is
simply because cofiltered categories are connected. More profoundly, the converse is also true
if `C` is cofiltered, see `initial_iff_isCofiltered_costructuredArrow`. -/
/-
**CategoryTheory.Functor.initial_of_isCofiltered_costructuredArrow** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [∀ (d : D), CategoryTheory.IsCofiltered (CategoryTheory.CostructuredArrow F d)]
,   F.Initial
参数：F : CategoryTheory.Functor C D；d : D；CategoryTheory.CostructuredArrow F d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofiltered.isConnected`：∀ (C : Type u) [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.IsCofiltered C], CategoryTheory.IsConn
ected C

--- 原说明 ---
If `CostructuredArrow F d` is filtered for any `d : D`, then `F : C ⥤ D` is init
ial. This is
simply because cofiltered categories are connected. More profoundly, the convers
e is also true
if `C` is cofiltered, see `initial_iff_isCofiltered_costructuredArrow`.
-/
theorem Functor.initial_of_isCofiltered_costructuredArrow
    [∀ d, IsCofiltered (CostructuredArrow F d)] : Initial F where
  out _ := IsCofiltered.isConnected _
/-
**CategoryTheory.isFiltered_structuredArrow_of_isFiltered_of_exists** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isFiltered_structuredArrow_of_isFiltered_of_exists [IsFilteredOrEmpty C] (
d : D) (h₁ : exists c, Nonempty (d ⟶ F.obj c)) (h₂ : forall {c : C} (s s' : d ⟶ 
F.obj c), exists (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t) : IsFiltered
 (StructuredArrow d F)
参数：d : D；h₁ : exists c, Nonempty (d ⟶ F.obj c)；h₂ : forall {c : C} (s s' : d ⟶ F
.obj c), exists (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `trivial`：True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.StructuredArrow.w_assoc`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {S : D} {T : Categ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsFiltered.coeq_condition`：coeq_condition {j j' : C} (f f
' : j ⟶ j') : f ≫ coeqHom f f' = f' ≫ coeqHom f f'
-/
theorem isFiltered_structuredArrow_of_isFiltered_of_exists [IsFilteredOrEmpty C] (d : D)
    (h₁ : ∃ c, Nonempty (d ⟶ F.obj c)) (h₂ : ∀ {c : C} (s s' : d ⟶ F.obj c),
      ∃ (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t) :
    IsFiltered (StructuredArrow d F) := by
  have : Nonempty (StructuredArrow d F) := by
    obtain ⟨c, ⟨f⟩⟩ := h₁
    exact ⟨.mk f⟩
  suffices IsFilteredOrEmpty (StructuredArrow d F) from IsFiltered.mk
  refine ⟨fun f g => ?_, fun f g η μ => ?_⟩
  · obtain ⟨c, ⟨t, ht⟩⟩ := h₂ (f.hom ≫ F.map (IsFiltered.leftToMax f.right g.right))
        (g.hom ≫ F.map (IsFiltered.rightToMax f.right g.right))
    refine ⟨.mk (f.hom ≫ F.map (IsFiltered.leftToMax f.right g.right ≫ t)), ?_, ?_, trivial⟩
    · exact StructuredArrow.homMk (IsFiltered.leftToMax _ _ ≫ t) rfl
    · exact StructuredArrow.homMk (IsFiltered.rightToMax _ _ ≫ t) (by simpa using ht.symm)
  · refine ⟨.mk (f.hom ≫ F.map (η.right ≫ IsFiltered.coeqHom η.right μ.right)),
      StructuredArrow.homMk (IsFiltered.coeqHom η.right μ.right) (by simp), ?_⟩
    simpa using IsFiltered.coeq_condition _ _
/-
**CategoryTheory.isCofiltered_costructuredArrow_of_isCofiltered_of_exists** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isCofiltered_costructuredArrow_of_isCofiltered_of_exists [IsCofilteredOrEm
pty C] (d : D) (h₁ : exists c, Nonempty (F.obj c ⟶ d)) (h₂ : forall {c : C} (s s
' : F.obj c ⟶ d), exists (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s') : Is
Cofiltered (CostructuredArrow F d)
参数：d : D；h₁ : exists c, Nonempty (F.obj c ⟶ d)；h₂ : forall {c : C} (s s' : F.obj
 c ⟶ d), exists (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isFiltered_structuredArrow_of_isFiltered_of_exists`：isFil
tered_structuredArrow_of_isFiltered_of_exists [IsFilteredOrEmpty C] (d : D) (h₁ 
: exists c, Nonempty (d ⟶ F.obj c)) (h₂ : forall {c : C…
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `CategoryTheory.IsFiltered.of_equivalence`：of_equivalence (h : C ≌ D) : I
sFiltered D
· 使用引理 `CategoryTheory.isCofiltered_of_isFiltered_op`：isCofiltered_of_isFiltered
_op [IsFiltered Cᵒᵖ] : IsCofiltered C
-/
theorem isCofiltered_costructuredArrow_of_isCofiltered_of_exists [IsCofilteredOrEmpty C] (d : D)
    (h₁ : ∃ c, Nonempty (F.obj c ⟶ d)) (h₂ : ∀ {c : C} (s s' : F.obj c ⟶ d),
      ∃ (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s') :
    IsCofiltered (CostructuredArrow F d) := by
  suffices IsFiltered (CostructuredArrow F d)ᵒᵖ from isCofiltered_of_isFiltered_op _
  suffices IsFiltered (StructuredArrow (op d) F.op) from
    IsFiltered.of_equivalence (costructuredArrowOpEquivalence _ _).symm
  apply isFiltered_structuredArrow_of_isFiltered_of_exists
  · obtain ⟨c, ⟨t⟩⟩ := h₁
    exact ⟨op c, ⟨Quiver.Hom.op t⟩⟩
  · intro c s s'
    obtain ⟨c', t, ht⟩ := h₂ s.unop s'.unop
    exact ⟨op c', Quiver.Hom.op t, Quiver.Hom.unop_inj ht⟩
/-
**CategoryTheory.exists_eq_of_isCofiltered_costructuredArrow** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory`。
形式化陈述：exists_eq_of_isCofiltered_costructuredArrow {d : D} [IsCofiltered (Costruc
turedArrow F d)] {c₁ c₂ : C} (s₁ : F.obj c₁ ⟶ d) (s₂ : F.obj c₂ ⟶ d) : exists (c
 : C) (t₁ : c ⟶ c₁) (t₂ : c ⟶ c₂), F.map t₁ ≫ s₁ = F.map t₂ ≫ s₂
参数：CostructuredArrow F d；s₁ : F.obj c₁ ⟶ d；s₂ : F.obj c₂ ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofilteredOrEmpty.cone_objs`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofilteredOrEmpty C] (X 
Y : C),   ∃ W x x, True
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CostructuredArrow.w`：w (f : X ⟶ Y) : S.map f.left ≫ Y.hom
 = X.hom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_eq_of_isCofiltered_costructuredArrow {d : D}
    [IsCofiltered (CostructuredArrow F d)] {c₁ c₂ : C}
    (s₁ : F.obj c₁ ⟶ d) (s₂ : F.obj c₂ ⟶ d) :
    ∃ (c : C) (t₁ : c ⟶ c₁) (t₂ : c ⟶ c₂), F.map t₁ ≫ s₁ = F.map t₂ ≫ s₂ := by
  obtain ⟨W, p₁, p₂, -⟩ := IsCofilteredOrEmpty.cone_objs
    (CostructuredArrow.mk s₁) (CostructuredArrow.mk s₂)
  exact ⟨W.left, p₁.left, p₂.left, (CostructuredArrow.w p₁).trans (CostructuredArrow.w p₂).symm⟩

/-- If `C` is filtered, then we can give an explicit condition for a functor `F : C ⥤ D` to
be final. The converse is also true, see `final_iff_of_isFiltered`. -/
/-
**CategoryTheory.Functor.final_of_exists_of_isFiltered** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.IsFilteredOrEmpty C],   (∀ (d : D), ∃ c, Nonempty (d ⟶ F.obj c)
) →     (∀ {d : D} {c : C} (s s' : d ⟶ F.obj c),         ∃ c' t, CategoryTheory.
CategoryStruct.comp s (F.map t) = CategoryTheory.CategoryStruct.comp s' (F.map t
)) →       F.Final
参数：F : CategoryTheory.Functor C D；∀ (d : D), ∃ c, Nonempty (d ⟶ F.obj c)；∀ {d : 
D} {c : C} (s s' : d ⟶ F.obj c),         ∃ c' t, CategoryTheory.CategoryStruct.c
omp s (F.map t) = CategoryTheory.CategoryStruct.comp s' (F.map t)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isFiltered_structuredArrow_of_isFiltered_of_exists`：isFil
tered_structuredArrow_of_isFiltered_of_exists [IsFilteredOrEmpty C] (d : D) (h₁ 
: exists c, Nonempty (d ⟶ F.obj c)) (h₂ : forall {c : C…
· 使用定理 `CategoryTheory.Functor.final_of_isFiltered_structuredArrow`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
If `C` is filtered, then we can give an explicit condition for a functor `F : C 
⥤ D` to
be final. The converse is also true, see `final_iff_of_isFiltered`.
-/
theorem Functor.final_of_exists_of_isFiltered [IsFilteredOrEmpty C]
    (h₁ : ∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) (h₂ : ∀ {d : D} {c : C} (s s' : d ⟶ F.obj c),
      ∃ (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t) : Functor.Final F := by
  suffices ∀ d, IsFiltered (StructuredArrow d F) from final_of_isFiltered_structuredArrow F
  exact fun d => isFiltered_structuredArrow_of_isFiltered_of_exists F d (h₁ d) h₂

/-- The inclusion of a terminal object is final. -/
/-
**CategoryTheory.Functor.final_const_of_isTerminal** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.IsFiltered C] {X
 : D} (hX : CategoryTheory.Limits.IsTerminal X),   ((CategoryTheory.Functor.cons
t C).obj X).Final
参数：hX : CategoryTheory.Limits.IsTerminal X；(CategoryTheory.Functor.const C).obj 
X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_exists_of_isFiltered`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory
.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.IsFiltered.nonempty`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.IsFiltered C], Nonempty C
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g

--- 原说明 ---
The inclusion of a terminal object is final.
-/
theorem Functor.final_const_of_isTerminal [IsFiltered C] {X : D} (hX : IsTerminal X) :
    ((Functor.const C).obj X).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun _ => ⟨IsFiltered.nonempty.some, ⟨hX.from _⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, hX.hom_ext _ _⟩)

/-- The inclusion of the terminal object is final. -/
/-
**CategoryTheory.Functor.final_const_terminal** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.IsFiltered C] [i
nst_3 : CategoryTheory.Limits.HasTerminal D],   ((CategoryTheory.Functor.const C
).obj (⊤_ D)).Final
参数：(CategoryTheory.Functor.const C).obj (⊤_ D)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_const_of_isTerminal`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   [CategoryTheory.Is…

--- 原说明 ---
The inclusion of the terminal object is final.
-/
theorem Functor.final_const_terminal [IsFiltered C] [HasTerminal D] :
    ((Functor.const C).obj (⊤_ D)).Final :=
  Functor.final_const_of_isTerminal terminalIsTerminal

/-- If `C` is cofiltered, then we can give an explicit condition for a functor `F : C ⥤ D` to
be final. The converse is also true, see `initial_iff_of_isCofiltered`. -/
/-
**CategoryTheory.Functor.initial_of_exists_of_isCofiltered** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.IsCofilteredOrEmpty C],   (∀ (d : D), ∃ c, Nonempty (F.obj c ⟶ 
d)) →     (∀ {d : D} {c : C} (s s' : F.obj c ⟶ d),         ∃ c' t, CategoryTheor
y.CategoryStruct.comp (F.map t) s = CategoryTheory.CategoryStruct.comp (F.map t)
 s') →       F.Initial
参数：F : CategoryTheory.Functor C D；∀ (d : D), ∃ c, Nonempty (F.obj c ⟶ d)；∀ {d : 
D} {c : C} (s s' : F.obj c ⟶ d),         ∃ c' t, CategoryTheory.CategoryStruct.c
omp (F.map t) s = CategoryTheory.CategoryStruct.comp (F.map t) s'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isCofiltered_costructuredArrow_of_isCofiltered_of_exists`
：isCofiltered_costructuredArrow_of_isCofiltered_of_exists [IsCofilteredOrEmpty C
] (d : D) (h₁ : exists c, Nonempty (F.obj c ⟶ d)) (h₂ : foral…
· 使用定理 `CategoryTheory.Functor.initial_of_isCofiltered_costructuredArrow`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
If `C` is cofiltered, then we can give an explicit condition for a functor `F : 
C ⥤ D` to
be final. The converse is also true, see `initial_iff_of_isCofiltered`.
-/
theorem Functor.initial_of_exists_of_isCofiltered [IsCofilteredOrEmpty C]
    (h₁ : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) (h₂ : ∀ {d : D} {c : C} (s s' : F.obj c ⟶ d),
      ∃ (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s') : Functor.Initial F := by
  suffices ∀ d, IsCofiltered (CostructuredArrow F d) from
    initial_of_isCofiltered_costructuredArrow F
  exact fun d => isCofiltered_costructuredArrow_of_isCofiltered_of_exists F d (h₁ d) h₂

/-- The inclusion of an initial object is initial. -/
/-
**CategoryTheory.Functor.initial_const_of_isInitial** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.IsCofiltered C] 
{X : D} (hX : CategoryTheory.Limits.IsInitial X),   ((CategoryTheory.Functor.con
st C).obj X).Initial
参数：hX : CategoryTheory.Limits.IsInitial X；(CategoryTheory.Functor.const C).obj X
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_of_exists_of_isCofiltered`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `CategoryTheory.IsCofiltered.nonempty`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C], Nonempty C
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g

--- 原说明 ---
The inclusion of an initial object is initial.
-/
theorem Functor.initial_const_of_isInitial [IsCofiltered C] {X : D} (hX : IsInitial X) :
    ((Functor.const C).obj X).Initial :=
  Functor.initial_of_exists_of_isCofiltered _ (fun _ => ⟨IsCofiltered.nonempty.some, ⟨hX.to _⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, hX.hom_ext _ _⟩)

/-- The inclusion of the initial object is initial. -/
/-
**CategoryTheory.Functor.initial_const_initial** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.IsCofiltered C] 
[inst_3 : CategoryTheory.Limits.HasInitial D],   ((CategoryTheory.Functor.const 
C).obj (⊥_ D)).Initial
参数：(CategoryTheory.Functor.const C).obj (⊥_ D)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_const_of_isInitial`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   [CategoryTheory.Is…

--- 原说明 ---
The inclusion of the initial object is initial.
-/
theorem Functor.initial_const_initial [IsCofiltered C] [HasInitial D] :
    ((Functor.const C).obj (⊥_ D)).Initial :=
  Functor.initial_const_of_isInitial initialIsInitial

/-- In this situation, `F` is also final, see
`Functor.final_of_exists_of_isFiltered_of_fullyFaithful`. -/
/-
**CategoryTheory.IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsFilteredOrEmpty`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.IsFilteredOrEmpty D] [F.Full] [F.Faithful],   (∀ (d : D), ∃ c, 
Nonempty (d ⟶ F.obj c)) → CategoryTheory.IsFilteredOrEmpty C
参数：F : CategoryTheory.Functor C D；∀ (d : D), ∃ c, Nonempty (d ⟶ F.obj c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.IsFiltered.coeq_condition`：coeq_condition {j j' : C} (f f
' : j ⟶ j') : f ≫ coeqHom f f' = f' ≫ coeqHom f f'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In this situation, `F` is also final, see
`Functor.final_of_exists_of_isFiltered_of_fullyFaithful`.
-/
theorem IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful [IsFilteredOrEmpty D] [F.Full]
    [F.Faithful] (h : ∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) : IsFilteredOrEmpty C where
  cocone_objs c c' := by
    obtain ⟨c₀, ⟨f⟩⟩ := h (IsFiltered.max (F.obj c) (F.obj c'))
    exact ⟨c₀, F.preimage (IsFiltered.leftToMax _ _ ≫ f),
      F.preimage (IsFiltered.rightToMax _ _ ≫ f), trivial⟩
  cocone_maps {c c'} f g := by
    obtain ⟨c₀, ⟨f₀⟩⟩ := h (IsFiltered.coeq (F.map f) (F.map g))
    refine ⟨_, F.preimage (IsFiltered.coeqHom (F.map f) (F.map g) ≫ f₀), F.map_injective ?_⟩
    simp [reassoc_of% (IsFiltered.coeq_condition (F.map f) (F.map g))]

/-- In this situation, `F` is also initial, see
`Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful`. -/
/-
**CategoryTheory.IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsCofilteredOrEmpty`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.IsCofilteredOrEmpty D] [F.Full] [F.Faithful],   (∀ (d : D), ∃ c
, Nonempty (F.obj c ⟶ d)) → CategoryTheory.IsCofilteredOrEmpty C
参数：F : CategoryTheory.Functor C D；∀ (d : D), ∃ c, Nonempty (F.obj c ⟶ d)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithfu
l`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [in
st_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFullOppositeOp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFaithfulOppositeOp`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.isCofilteredOrEmpty_of_isFilteredOrEmpty_op`：isCofiltered
OrEmpty_of_isFilteredOrEmpty_op [IsFilteredOrEmpty Cᵒᵖ] : IsCofilteredOrEmpty C

--- 原说明 ---
In this situation, `F` is also initial, see
`Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful`.
-/
theorem IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful [IsCofilteredOrEmpty D]
    [F.Full] [F.Faithful] (h : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) : IsCofilteredOrEmpty C := by
  suffices IsFilteredOrEmpty Cᵒᵖ from isCofilteredOrEmpty_of_isFilteredOrEmpty_op _
  refine IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F.op (fun d => ?_)
  obtain ⟨c, ⟨f⟩⟩ := h d.unop
  exact ⟨op c, ⟨f.op⟩⟩

/-- In this situation, `F` is also final, see
`Functor.final_of_exists_of_isFiltered_of_fullyFaithful`. -/
/-
**CategoryTheory.IsFiltered.of_exists_of_isFiltered_of_fullyFaithful** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.IsFiltered`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.IsFiltered D] [F.Full] [F.Faithful],   (∀ (d : D), ∃ c, Nonempt
y (d ⟶ F.obj c)) → CategoryTheory.IsFiltered C
参数：F : CategoryTheory.Functor C D；∀ (d : D), ∃ c, Nonempty (d ⟶ F.obj c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithfu
l`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [in
st_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.IsFiltered.nonempty`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.IsFiltered C], Nonempty C

--- 原说明 ---
In this situation, `F` is also final, see
`Functor.final_of_exists_of_isFiltered_of_fullyFaithful`.
-/
theorem IsFiltered.of_exists_of_isFiltered_of_fullyFaithful [IsFiltered D] [F.Full] [F.Faithful]
    (h : ∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) : IsFiltered C :=
  { IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F h with
    nonempty := by
      have : Nonempty D := IsFiltered.nonempty
      obtain ⟨c, -⟩ := h (Classical.arbitrary D)
      exact ⟨c⟩ }

/-- In this situation, `F` is also initial, see
`Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful`. -/
/-
**CategoryTheory.IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.IsCofiltered`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.IsCofiltered D] [F.Full] [F.Faithful],   (∀ (d : D), ∃ c, Nonem
pty (F.obj c ⟶ d)) → CategoryTheory.IsCofiltered C
参数：F : CategoryTheory.Functor C D；∀ (d : D), ∃ c, Nonempty (F.obj c ⟶ d)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFai
thful`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂}
 [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `CategoryTheory.IsCofiltered.nonempty`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C], Nonempty C

--- 原说明 ---
In this situation, `F` is also initial, see
`Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful`.
-/
theorem IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful [IsCofiltered D] [F.Full]
    [F.Faithful] (h : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) : IsCofiltered C :=
  { IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful F h with
    nonempty := by
      have : Nonempty D := IsCofiltered.nonempty
      obtain ⟨c, -⟩ := h (Classical.arbitrary D)
      exact ⟨c⟩ }

/-- In this situation, `C` is also filtered, see
`IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful`. -/
/-
**CategoryTheory.Functor.final_of_exists_of_isFiltered_of_fullyFaithful** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.IsFilteredOrEmpty D] [F.Full] [F.Faithful],   (∀ (d : D), ∃ c, 
Nonempty (d ⟶ F.obj c)) → F.Final
参数：F : CategoryTheory.Functor C D；∀ (d : D), ∃ c, Nonempty (d ⟶ F.obj c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithfu
l`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [in
st_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.final_of_exists_of_isFiltered`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory
.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.IsFiltered.coeq_condition`：coeq_condition {j j' : C} (f f
' : j ⟶ j') : f ≫ coeqHom f f' = f' ≫ coeqHom f f'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In this situation, `C` is also filtered, see
`IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful`.
-/
theorem Functor.final_of_exists_of_isFiltered_of_fullyFaithful [IsFilteredOrEmpty D] [F.Full]
    [F.Faithful] (h : ∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) : Final F := by
  have := IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F h
  refine Functor.final_of_exists_of_isFiltered F h (fun {d c} s s' => ?_)
  obtain ⟨c₀, ⟨f⟩⟩ := h (IsFiltered.coeq s s')
  refine ⟨c₀, F.preimage (IsFiltered.coeqHom s s' ≫ f), ?_⟩
  simp [reassoc_of% (IsFiltered.coeq_condition s s')]

/-- In this situation, `C` is also cofiltered, see
`IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful`. -/
/-
**CategoryTheory.Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.IsCofilteredOrEmpty D] [F.Full] [F.Faithful],   (∀ (d : D), ∃ c
, Nonempty (F.obj c ⟶ d)) → F.Initial
参数：F : CategoryTheory.Functor C D；∀ (d : D), ∃ c, Nonempty (F.obj c ⟶ d)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_exists_of_isFiltered_of_fullyFaithful`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1
 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFullOppositeOp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFaithfulOppositeOp`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.initial_of_final_op`：initial_of_final_op (F : C ⥤
 D) [Final F.op] : Initial F

--- 原说明 ---
In this situation, `C` is also cofiltered, see
`IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful`.
-/
theorem Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful [IsCofilteredOrEmpty D] [F.Full]
    [Faithful F] (h : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) : Initial F := by
  suffices Final F.op from initial_of_final_op _
  refine Functor.final_of_exists_of_isFiltered_of_fullyFaithful F.op (fun d => ?_)
  obtain ⟨c, ⟨f⟩⟩ := h d.unop
  exact ⟨op c, ⟨f.op⟩⟩

/-- Any under category on a filtered or empty category is filtered.
(Note that under categories are always cofiltered since they have an initial object.) -/
/-
**CategoryTheory.IsFiltered.under** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsFi
ltered`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.IsFilteredOrEmpty C] (c : C),   CategoryTheory.IsFiltered (CategoryTheory.Unde
r c)
参数：c : C；CategoryTheory.Under c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isFiltered_structuredArrow_of_isFiltered_of_exists`：isFil
tered_structuredArrow_of_isFiltered_of_exists [IsFilteredOrEmpty C] (d : D) (h₁ 
: exists c, Nonempty (d ⟶ F.obj c)) (h₂ : forall {c : C…
· 使用定理 `CategoryTheory.IsFilteredOrEmpty.cocone_maps`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFilteredOrEmpty C] ⦃X Y 
: C⦄   (f g : X ⟶ Y), ∃ Z h, Categ…

--- 原说明 ---
Any under category on a filtered or empty category is filtered.
(Note that under categories are always cofiltered since they have an initial obj
ect.)
-/
instance IsFiltered.under [IsFilteredOrEmpty C] (c : C) : IsFiltered (Under c) :=
  isFiltered_structuredArrow_of_isFiltered_of_exists _ c ⟨c, ⟨𝟙 _⟩⟩
    (fun s s' => IsFilteredOrEmpty.cocone_maps s s')

/-- Any over category on a cofiltered or empty category is cofiltered.
(Note that over categories are always filtered since they have a terminal object.) -/
/-
**CategoryTheory.IsCofiltered.over** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsC
ofiltered`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.IsCofilteredOrEmpty C] (c : C),   CategoryTheory.IsCofiltered (CategoryTheory.
Over c)
参数：c : C；CategoryTheory.Over c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isCofiltered_costructuredArrow_of_isCofiltered_of_exists`
：isCofiltered_costructuredArrow_of_isCofiltered_of_exists [IsCofilteredOrEmpty C
] (d : D) (h₁ : exists c, Nonempty (F.obj c ⟶ d)) (h₂ : foral…
· 使用定理 `CategoryTheory.IsCofilteredOrEmpty.cone_maps`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofilteredOrEmpty C] ⦃X 
Y : C⦄   (f g : X ⟶ Y), ∃ W h, Cat…

--- 原说明 ---
Any over category on a cofiltered or empty category is cofiltered.
(Note that over categories are always filtered since they have a terminal object
.)
-/
instance IsCofiltered.over [IsCofilteredOrEmpty C] (c : C) : IsCofiltered (Over c) :=
  isCofiltered_costructuredArrow_of_isCofiltered_of_exists _ c ⟨c, ⟨𝟙 _⟩⟩
    (fun s s' => IsCofilteredOrEmpty.cone_maps s s')

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The forgetful functor of the under category on any filtered or empty category is final. -/
/-
**CategoryTheory.Under.final_forget** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Un
der`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.IsFilteredOrEmpty C] (c : C),   (CategoryTheory.Under.forget c).Final
参数：c : C；CategoryTheory.Under.forget c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_exists_of_isFiltered`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory
.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.IsFiltered.under`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] [CategoryTheory.IsFilteredOrEmpty C] (c : C),   CategoryThe
ory.IsFiltered (Categ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsFiltered.coeq_condition`：coeq_condition {j j' : C} (f f
' : j ⟶ j') : f ≫ coeqHom f f' = f' ≫ coeqHom f f'

--- 原说明 ---
The forgetful functor of the under category on any filtered or empty category is
 final.
-/
instance Under.final_forget [IsFilteredOrEmpty C] (c : C) : Final (Under.forget c) :=
  final_of_exists_of_isFiltered _
    (fun c' => ⟨mk (IsFiltered.leftToMax c c'), ⟨IsFiltered.rightToMax c c'⟩⟩)
    (fun {_} {x} s s' => by
      use mk (x.hom ≫ IsFiltered.coeqHom s s')
      use homMk (IsFiltered.coeqHom s s') (by simp)
      simp only [forget_obj, mk_right, forget_map, homMk_right]
      rw [IsFiltered.coeq_condition])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The forgetful functor of the over category on any cofiltered or empty category is initial. -/
/-
**CategoryTheory.Over.initial_forget** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.O
ver`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.IsCofilteredOrEmpty C] (c : C),   (CategoryTheory.Over.forget c).Initial
参数：c : C；CategoryTheory.Over.forget c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_of_exists_of_isCofiltered`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `CategoryTheory.IsCofiltered.over`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] [CategoryTheory.IsCofilteredOrEmpty C] (c : C),   Category
Theory.IsCofiltered (C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsCofiltered.eq_condition`：eq_condition {j j' : C} (f f' 
: j ⟶ j') : eqHom f f' ≫ f = eqHom f f' ≫ f'

--- 原说明 ---
The forgetful functor of the over category on any cofiltered or empty category i
s initial.
-/
instance Over.initial_forget [IsCofilteredOrEmpty C] (c : C) : Initial (Over.forget c) :=
  initial_of_exists_of_isCofiltered _
    (fun c' => ⟨mk (IsCofiltered.minToLeft c c'), ⟨IsCofiltered.minToRight c c'⟩⟩)
    (fun {_} {x} s s' => by
      use mk (IsCofiltered.eqHom s s' ≫ x.hom)
      use homMk (IsCofiltered.eqHom s s') (by simp)
      simp only [forget_obj, mk_left, forget_map, homMk_left]
      rw [IsCofiltered.eq_condition])

section LocallySmall

variable {C : Type v₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D] (F : C ⥤ D)

set_option backward.defeqAttrib.useBackward true in
/-- Implementation; use `Functor.Final.exists_coeq instead`. -/
/-
**CategoryTheory.Functor.Final.exists_coeq_of_locally_small** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor.Final`。
形式化陈述：∀ {C : Type v₁} [inst : CategoryTheory.Category.{v₁, v₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₁, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.IsFilteredOrEmpty C] [F.Final] {d : D} {c : C} (s s' : d ⟶ F.ob
j c),   ∃ c' t, CategoryTheory.CategoryStruct.comp s (F.map t) = CategoryTheory.
CategoryStruct.comp s' (F.map t)
参数：F : CategoryTheory.Functor C D；s s' : d ⟶ F.obj c；F.map t；F.map t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `CategoryTheory.Coyoneda.instHasColimitObjOppositeFunctorTypeCoyoneda`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] (X : Cᵒᵖ),   CategoryTheo
ry.Limits.HasColimit (CategoryTheory.coyoneda.obj X)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff`：colimit_eq_i
ff [HasColimit F] {i j : J} {xi : F.obj i} {xj : F.obj j} : colimit.ι F i xi = c
olimit.ι F j xj ↔ exists (k : _) (f : i ⟶ k) (g …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsFiltered.coeq_condition`：coeq_condition {j j' : C} (f f
' : j ⟶ j') : f ≫ coeqHom f f' = f' ≫ coeqHom f f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Implementation; use `Functor.Final.exists_coeq instead`.
-/
theorem Functor.Final.exists_coeq_of_locally_small [IsFilteredOrEmpty C] [Final F] {d : D} {c : C}
    (s s' : d ⟶ F.obj c) : ∃ (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t := by
  have : colimit.ι (F ⋙ coyoneda.obj (op d)) c s = colimit.ι (F ⋙ coyoneda.obj (op d)) c s' := by
    apply (Final.colimitCompCoyonedaIso F d).toEquiv.injective
    subsingleton
  obtain ⟨c', t₁, t₂, h⟩ := (Types.FilteredColimit.colimit_eq_iff.{v₁, v₁, v₁} _).mp this
  refine ⟨IsFiltered.coeq t₁ t₂, t₁ ≫ IsFiltered.coeqHom t₁ t₂, ?_⟩
  conv_rhs => rw [IsFiltered.coeq_condition t₁ t₂]
  dsimp at h
  simp [reassoc_of% h]

end LocallySmall

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `C` is filtered, then we can give an explicit condition for a functor `F : C ⥤ D` to
be final. -/
/-
**CategoryTheory.Functor.final_iff_of_isFiltered** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.IsFilteredOrEmpty C],   F.Final ↔     (∀ (d : D), ∃ c, Nonempty
 (d ⟶ F.obj c)) ∧       ∀ {d : D} {c : C} (s s' : d ⟶ F.obj c),         ∃ c' t, 
CategoryTheory.CategoryStruct.comp s (F.map t) = CategoryTheory.CategoryStruct.c
omp s' (F.map t)
参数：F : CategoryTheory.Functor C D；∀ (d : D), ∃ c, Nonempty (d ⟶ F.obj c)；s s' : 
d ⟶ F.obj c；F.map t；F.map t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.IsFilteredOrEmpty.of_equivalence`：of_equivalence (h : C ≌
 D) : IsFilteredOrEmpty D
· 使用定理 `CategoryTheory.Functor.Final.exists_coeq_of_locally_small`：∀ {C : Type v
₁} [inst : CategoryTheory.Category.{v₁, v₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₁, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.final_of_exists_of_isFiltered`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory
.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `C` is filtered, then we can give an explicit condition for a functor `F : C 
⥤ D` to
be final.
-/
theorem Functor.final_iff_of_isFiltered [IsFilteredOrEmpty C] :
    Final F ↔ (∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) ∧ (∀ {d : D} {c : C} (s s' : d ⟶ F.obj c),
      ∃ (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t) := by
  refine ⟨fun hF => ⟨?_, ?_⟩, fun h => final_of_exists_of_isFiltered F h.1 h.2⟩
  · intro d
    obtain ⟨f⟩ : Nonempty (StructuredArrow d F) := IsConnected.is_nonempty
    exact ⟨_, ⟨f.hom⟩⟩
  · let s₁ : C ≌ AsSmall.{max u₁ v₁ u₂ v₂} C := AsSmall.equiv
    let s₂ : D ≌ AsSmall.{max u₁ v₁ u₂ v₂} D := AsSmall.equiv
    have : IsFilteredOrEmpty (AsSmall.{max u₁ v₁ u₂ v₂} C) := .of_equivalence s₁
    intro d c s s'
    obtain ⟨c', t, ht⟩ := Functor.Final.exists_coeq_of_locally_small (s₁.inverse ⋙ F ⋙ s₂.functor)
      (AsSmall.up.map s) (AsSmall.up.map s')
    exact ⟨AsSmall.down.obj c', AsSmall.down.map t, s₂.functor.map_injective (by simp_all [s₁, s₂])⟩

/-- If `C` is cofiltered, then we can give an explicit condition for a functor `F : C ⥤ D` to
be initial. -/
/-
**CategoryTheory.Functor.initial_iff_of_isCofiltered** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.IsCofilteredOrEmpty C],   F.Initial ↔     (∀ (d : D), ∃ c, None
mpty (F.obj c ⟶ d)) ∧       ∀ {d : D} {c : C} (s s' : F.obj c ⟶ d),         ∃ c'
 t, CategoryTheory.CategoryStruct.comp (F.map t) s = CategoryTheory.CategoryStru
ct.comp (F.map t) s'
参数：F : CategoryTheory.Functor C D；∀ (d : D), ∃ c, Nonempty (F.obj c ⟶ d)；s s' : 
F.obj c ⟶ d；F.map t；F.map t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.final_iff_of_isFiltered`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `CategoryTheory.Functor.initial_of_exists_of_isCofiltered`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `C` is cofiltered, then we can give an explicit condition for a functor `F : 
C ⥤ D` to
be initial.
-/
theorem Functor.initial_iff_of_isCofiltered [IsCofilteredOrEmpty C] :
    Initial F ↔ (∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) ∧ (∀ {d : D} {c : C} (s s' : F.obj c ⟶ d),
      ∃ (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s') := by
  refine ⟨fun hF => ?_, fun h => initial_of_exists_of_isCofiltered F h.1 h.2⟩
  obtain ⟨h₁, h₂⟩ := F.op.final_iff_of_isFiltered.mp inferInstance
  refine ⟨?_, ?_⟩
  · intro d
    obtain ⟨c, ⟨t⟩⟩ := h₁ (op d)
    exact ⟨c.unop, ⟨t.unop⟩⟩
  · intro d c s s'
    obtain ⟨c', t, ht⟩ := h₂ (Quiver.Hom.op s) (Quiver.Hom.op s')
    exact ⟨c'.unop, t.unop, Quiver.Hom.op_inj ht⟩
/-
**CategoryTheory.Functor.Final.exists_coeq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor.Final`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.IsFilteredOrEmpty C] [F.Final] {d : D} {c : C} (s s' : d ⟶ F.ob
j c),   ∃ c' t, CategoryTheory.CategoryStruct.comp s (F.map t) = CategoryTheory.
CategoryStruct.comp s' (F.map t)
参数：F : CategoryTheory.Functor C D；s s' : d ⟶ F.obj c；F.map t；F.map t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.final_iff_of_isFiltered`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
-/
theorem Functor.Final.exists_coeq [IsFilteredOrEmpty C] [Final F] {d : D} {c : C}
    (s s' : d ⟶ F.obj c) : ∃ (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t :=
  ((final_iff_of_isFiltered F).1 inferInstance).2 s s'
/-
**CategoryTheory.Functor.Initial.exists_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor.Initial`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.IsCofilteredOrEmpty C] [F.Initial] {d : D} {c : C}   (s s' : F.
obj c ⟶ d),   ∃ c' t, CategoryTheory.CategoryStruct.comp (F.map t) s = CategoryT
heory.CategoryStruct.comp (F.map t) s'
参数：F : CategoryTheory.Functor C D；s s' : F.obj c ⟶ d；F.map t；F.map t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.initial_iff_of_isCofiltered`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   (F : CategoryTheor…
-/
theorem Functor.Initial.exists_eq [IsCofilteredOrEmpty C] [Initial F] {d : D} {c : C}
    (s s' : F.obj c ⟶ d) : ∃ (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s' :=
  ((initial_iff_of_isCofiltered F).1 inferInstance).2 s s'

/-- If `C` is filtered, then `F : C ⥤ D` is final if and only if `StructuredArrow d F` is filtered
for all `d : D`. -/
/-
**CategoryTheory.Functor.final_iff_isFiltered_structuredArrow** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.IsFilteredOrEmpty C],   F.Final ↔ ∀ (d : D), CategoryTheory.IsF
iltered (CategoryTheory.StructuredArrow d F)
参数：F : CategoryTheory.Functor C D；d : D；CategoryTheory.StructuredArrow d F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.final_iff_of_isFiltered`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.isFiltered_structuredArrow_of_isFiltered_of_exists`：isFil
tered_structuredArrow_of_isFiltered_of_exists [IsFilteredOrEmpty C] (d : D) (h₁ 
: exists c, Nonempty (d ⟶ F.obj c)) (h₂ : forall {c : C…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.Functor.final_of_isFiltered_structuredArrow`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
If `C` is filtered, then `F : C ⥤ D` is final if and only if `StructuredArrow d 
F` is filtered
for all `d : D`.
-/
theorem Functor.final_iff_isFiltered_structuredArrow [IsFilteredOrEmpty C] :
    Final F ↔ ∀ d, IsFiltered (StructuredArrow d F) := by
  refine ⟨?_, fun h => final_of_isFiltered_structuredArrow F⟩
  rw [final_iff_of_isFiltered]
  exact fun h d => isFiltered_structuredArrow_of_isFiltered_of_exists F d (h.1 d) h.2

/-- If `C` is cofiltered, then `F : C ⥤ D` is initial if and only if `CostructuredArrow F d` is
cofiltered for all `d : D`. -/
/-
**CategoryTheory.Functor.initial_iff_isCofiltered_costructuredArrow** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.IsCofilteredOrEmpty C],   F.Initial ↔ ∀ (d : D), CategoryTheory
.IsCofiltered (CategoryTheory.CostructuredArrow F d)
参数：F : CategoryTheory.Functor C D；d : D；CategoryTheory.CostructuredArrow F d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.initial_iff_of_isCofiltered`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.isCofiltered_costructuredArrow_of_isCofiltered_of_exists`
：isCofiltered_costructuredArrow_of_isCofiltered_of_exists [IsCofilteredOrEmpty C
] (d : D) (h₁ : exists c, Nonempty (F.obj c ⟶ d)) (h₂ : foral…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.Functor.initial_of_isCofiltered_costructuredArrow`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
If `C` is cofiltered, then `F : C ⥤ D` is initial if and only if `CostructuredAr
row F d` is
cofiltered for all `d : D`.
-/
theorem Functor.initial_iff_isCofiltered_costructuredArrow [IsCofilteredOrEmpty C] :
    Initial F ↔ ∀ d, IsCofiltered (CostructuredArrow F d) := by
  refine ⟨?_, fun h => initial_of_isCofiltered_costructuredArrow F⟩
  rw [initial_iff_of_isCofiltered]
  exact fun h d => isCofiltered_costructuredArrow_of_isCofiltered_of_exists F d (h.1 d) h.2

/-- If `C` is filtered, then the structured arrow category on the diagonal functor `C ⥤ C × C`
is filtered as well. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is filtered, then the structured arrow category on the diagonal functor `
C ⥤ C × C`
is filtered as well.
-/
instance [IsFilteredOrEmpty C] (X : C × C) : IsFiltered (StructuredArrow X (diag C)) := by
  have : ∀ Y, IsFiltered (StructuredArrow Y (Under.forget X.1)) := by
    rw [← final_iff_isFiltered_structuredArrow (Under.forget X.1)]
    infer_instance
  apply IsFiltered.of_equivalence (StructuredArrow.ofDiagEquivalence X).symm

/-- The diagonal functor on any filtered category is final. -/
/-
**CategoryTheory.Functor.final_diag_of_isFiltered** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.IsFilteredOrEmpty C],   (CategoryTheory.Functor.diag C).Final
参数：CategoryTheory.Functor.diag C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_isFiltered_structuredArrow`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instIsFilteredStructuredArrowProdDiagOfIsFilteredOrEmpty`
：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsF
ilteredOrEmpty C] (X : C × C),   CategoryTheory.IsFiltered (C…

--- 原说明 ---
The diagonal functor on any filtered category is final.
-/
instance Functor.final_diag_of_isFiltered [IsFilteredOrEmpty C] : Final (Functor.diag C) :=
  final_of_isFiltered_structuredArrow _

-- Adding this instance causes performance problems elsewhere, even with low priority
/-
**CategoryTheory.IsFilteredOrEmpty.isSiftedOrEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.IsFilteredOrEmpty`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.IsFilteredOrEmpty C],   CategoryTheory.IsSiftedOrEmpty C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_diag_of_isFiltered`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsFilteredOrEmpty C],   (Ca
tegoryTheory.Functor.diag C).Final
-/
theorem IsFilteredOrEmpty.isSiftedOrEmpty [IsFilteredOrEmpty C] : IsSiftedOrEmpty C :=
  Functor.final_diag_of_isFiltered

-- Adding this instance causes performance problems elsewhere, even with low priority
attribute [local instance] IsFiltered.nonempty in
/-
**CategoryTheory.IsFiltered.isSifted** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.I
sFiltered`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.IsFiltered C], CategoryTheory.IsSifted C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_diag_of_isFiltered`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsFilteredOrEmpty C],   (Ca
tegoryTheory.Functor.diag C).Final
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.IsFiltered.nonempty`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.IsFiltered C], Nonempty C
-/
theorem IsFiltered.isSifted [IsFiltered C] : IsSifted C where

/-- If `C` is cofiltered, then the costructured arrow category on the diagonal functor `C ⥤ C × C`
is cofiltered as well. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is cofiltered, then the costructured arrow category on the diagonal funct
or `C ⥤ C × C`
is cofiltered as well.
-/
instance [IsCofilteredOrEmpty C] (X : C × C) : IsCofiltered (CostructuredArrow (diag C) X) := by
  have : ∀ Y, IsCofiltered (CostructuredArrow (Over.forget X.1) Y) := by
    rw [← initial_iff_isCofiltered_costructuredArrow (Over.forget X.1)]
    infer_instance
  apply IsCofiltered.of_equivalence (CostructuredArrow.ofDiagEquivalence X).symm

/-- The diagonal functor on any cofiltered category is initial. -/
/-
**CategoryTheory.Functor.initial_diag_of_isFiltered** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.IsCofilteredOrEmpty C],   (CategoryTheory.Functor.diag C).Initial
参数：CategoryTheory.Functor.diag C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_of_isCofiltered_costructuredArrow`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instIsCofilteredCostructuredArrowProdDiagOfIsCofilteredOr
Empty`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheo
ry.IsCofilteredOrEmpty C] (X : C × C),   CategoryTheory.IsCofiltere…

--- 原说明 ---
The diagonal functor on any cofiltered category is initial.
-/
instance Functor.initial_diag_of_isFiltered [IsCofilteredOrEmpty C] : Initial (Functor.diag C) :=
  initial_of_isCofiltered_costructuredArrow _

/-- If `C` is filtered, then every functor `F : C ⥤ Discrete PUnit` is final. -/
/-
**CategoryTheory.Functor.final_of_isFiltered_of_pUnit** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.IsFiltered C]   (F : CategoryTheory.Functor C (CategoryTheory.Discrete PUnit.{
u_1 + 1})), F.Final
参数：F : CategoryTheory.Functor C (CategoryTheory.Discrete PUnit.{u_1 + 1})。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_exists_of_isFiltered`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory
.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.IsFiltered.nonempty`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.IsFiltered C], Nonempty C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
If `C` is filtered, then every functor `F : C ⥤ Discrete PUnit` is final.
-/
theorem Functor.final_of_isFiltered_of_pUnit [IsFiltered C] (F : C ⥤ Discrete PUnit) :
    Final F := by
  refine final_of_exists_of_isFiltered F (fun _ => ?_) (fun {_} {c} _ _ => ?_)
  · use Classical.choice IsFiltered.nonempty
    exact ⟨Discrete.eqToHom (by simp)⟩
  · use c; use 𝟙 c
    apply Subsingleton.elim

/-- If `C` is cofiltered, then every functor `F : C ⥤ Discrete PUnit` is initial. -/
/-
**CategoryTheory.Functor.initial_of_isCofiltered_pUnit** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.IsCofiltered C]   (F : CategoryTheory.Functor C (CategoryTheory.Discrete PUnit
.{u_1 + 1})), F.Initial
参数：F : CategoryTheory.Functor C (CategoryTheory.Discrete PUnit.{u_1 + 1})。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_of_exists_of_isCofiltered`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `CategoryTheory.IsCofiltered.nonempty`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C], Nonempty C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
If `C` is cofiltered, then every functor `F : C ⥤ Discrete PUnit` is initial.
-/
theorem Functor.initial_of_isCofiltered_pUnit [IsCofiltered C] (F : C ⥤ Discrete PUnit) :
    Initial F := by
  refine initial_of_exists_of_isCofiltered F (fun _ => ?_) (fun {_} {c} _ _ => ?_)
  · use Classical.choice IsCofiltered.nonempty
    exact ⟨Discrete.eqToHom (by simp)⟩
  · use c; use 𝟙 c
    apply Subsingleton.elim

/-- The functor `StructuredArrow.proj : StructuredArrow Y T ⥤ C` is final if `T : C ⥤ D` is final
and `C` is filtered. -/
/-
**CategoryTheory.StructuredArrow.final_proj_of_isFiltered** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.StructuredArrow`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.IsFilteredOrEmpt
y C] (T : CategoryTheory.Functor C D) [T.Final] (Y : D),   (CategoryTheory.Struc
turedArrow.proj Y T).Final
参数：T : CategoryTheory.Functor C D；Y : D；CategoryTheory.StructuredArrow.proj Y T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isConnected_iff_of_equivalence`：isConnected_iff_of_equiva
lence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) : IsConnected J ↔ IsConnected 
K
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Under.final_forget`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] [CategoryTheory.IsFilteredOrEmpty C] (c : C),   (Category
Theory.Under.forget c).…

--- 原说明 ---
The functor `StructuredArrow.proj : StructuredArrow Y T ⥤ C` is final if `T : C 
⥤ D` is final
and `C` is filtered.
-/
instance StructuredArrow.final_proj_of_isFiltered [IsFilteredOrEmpty C]
    (T : C ⥤ D) [Final T] (Y : D) : Final (StructuredArrow.proj Y T) := by
  refine ⟨fun X => ?_⟩
  rw [isConnected_iff_of_equivalence (ofStructuredArrowProjEquivalence T Y X)]
  exact (final_comp (Under.forget X) T).out _

/-- The functor `CostructuredArrow.proj : CostructuredArrow Y T ⥤ C` is initial if `T : C ⥤ D` is
initial and `C` is cofiltered. -/
/-
**CategoryTheory.CostructuredArrow.initial_proj_of_isCofiltered** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.IsCofilteredOrEm
pty C] (T : CategoryTheory.Functor C D) [T.Initial] (Y : D),   (CategoryTheory.C
ostructuredArrow.proj T Y).Initial
参数：T : CategoryTheory.Functor C D；Y : D；CategoryTheory.CostructuredArrow.proj T 
Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isConnected_iff_of_equivalence`：isConnected_iff_of_equiva
lence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) : IsConnected J ↔ IsConnected 
K
· 使用定理 `CategoryTheory.Functor.Initial.out`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Over.initial_forget`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] [CategoryTheory.IsCofilteredOrEmpty C] (c : C),   (Categ
oryTheory.Over.forget c)…

--- 原说明 ---
The functor `CostructuredArrow.proj : CostructuredArrow Y T ⥤ C` is initial if `
T : C ⥤ D` is
initial and `C` is cofiltered.
-/
instance CostructuredArrow.initial_proj_of_isCofiltered [IsCofilteredOrEmpty C]
    (T : C ⥤ D) [Initial T] (Y : D) : Initial (CostructuredArrow.proj T Y) := by
  refine ⟨fun X => ?_⟩
  rw [isConnected_iff_of_equivalence (ofCostructuredArrowProjEquivalence T Y X)]
  exact (initial_comp (Over.forget X) T).out _

/-- The functor `StructuredArrow d T ⥤ StructuredArrow e (T ⋙ S)` that `u : e ⟶ S.obj d`
induces via `StructuredArrow.map₂` is final, if `T` and `S` are final and the domain of `T` is
filtered. -/
/-
**CategoryTheory.StructuredArrow.final_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.StructuredArrow`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.IsFiltered C] {S
 S' : D} (f : S ⟶ S') (T : CategoryTheory.Functor C D) [T.Final],   (CategoryThe
ory.StructuredArrow.map f).Final
参数：f : S ⟶ S'；T : CategoryTheory.Functor C D；CategoryTheory.StructuredArrow.map 
f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.StructuredArrow.final_map₂_id`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   [CategoryTheory.Is…
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.final_of_natIso`：final_of_natIso {F F' : C ⥤ D} [
Final F] (i : F ≅ F') : Final F' where out _

--- 原说明 ---
The functor `StructuredArrow d T ⥤ StructuredArrow e (T ⋙ S)` that `u : e ⟶ S.ob
j d`
induces via `StructuredArrow.map₂` is final, if `T` and `S` are final and the do
main of `T` is
filtered.
-/
instance StructuredArrow.final_map₂_id [IsFiltered C] {E : Type u₃} [Category.{v₃} E]
    {T : C ⥤ D} [T.Final] {S : D ⥤ E} [S.Final] {T' : C ⥤ E}
    {d : D} {e : E} (u : e ⟶ S.obj d) (α : T ⋙ S ⟶ T') [IsIso α] :
    Final (map₂ (F := 𝟭 _) u α) := by
  have : IsFiltered (StructuredArrow e (T ⋙ S)) :=
    (T ⋙ S).final_iff_isFiltered_structuredArrow.mp inferInstance e
  apply final_of_natIso (map₂IsoPreEquivalenceInverseCompProj d e u α).symm

/-- `StructuredArrow.map` is final if the functor `T` is final and its domain is filtered. -/
/-
**CategoryTheory.StructuredArrow.final_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.StructuredArrow`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.IsFiltered C] {S
 S' : D} (f : S ⟶ S') (T : CategoryTheory.Functor C D) [T.Final],   (CategoryThe
ory.StructuredArrow.map f).Final
参数：f : S ⟶ S'；T : CategoryTheory.Functor C D；CategoryTheory.StructuredArrow.map 
f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.StructuredArrow.final_map₂_id`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   [CategoryTheory.Is…
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.final_of_natIso`：final_of_natIso {F F' : C ⥤ D} [
Final F] (i : F ≅ F') : Final F' where out _

--- 原说明 ---
`StructuredArrow.map` is final if the functor `T` is final and its domain is fil
tered.
-/
instance StructuredArrow.final_map [IsFiltered C] {S S' : D} (f : S ⟶ S') (T : C ⥤ D) [T.Final] :
    Final (map (T := T) f) := by
  have := NatIso.isIso_of_isIso_app (𝟙 T)
  have : (map₂ (F := 𝟭 C) (G := 𝟭 D) f (𝟙 T)).Final := by
    apply StructuredArrow.final_map₂_id (S := 𝟭 D) (T := T) (T' := T) f (𝟙 T)
  apply final_of_natIso (mapIsoMap₂ f).symm

/-- `StructuredArrow.post X T S` is final if `T` and `S` are final and the domain of `T` is
filtered. -/
/-
**CategoryTheory.StructuredArrow.final_post** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.StructuredArrow`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.IsFiltered C] {E
 : Type u₃} [inst_3 : CategoryTheory.Category.{v₃, u₃} E] (X : D)   (T : Categor
yTheory.Functor C D) [T.Final] (S : CategoryTheory.Functor D E) [S.Final],   (Ca
tegoryTheory.StructuredArrow.post X T S).Final
参数：X : D；T : CategoryTheory.Functor C D；S : CategoryTheory.Functor D E；CategoryT
heory.StructuredArrow.post X T S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_natIso`：final_of_natIso {F F' : C ⥤ D} [
Final F] (i : F ≅ F') : Final F' where out _
· 使用定理 `CategoryTheory.StructuredArrow.final_map₂_id`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   [CategoryTheory.Is…

--- 原说明 ---
`StructuredArrow.post X T S` is final if `T` and `S` are final and the domain of
 `T` is
filtered.
-/
instance StructuredArrow.final_post [IsFiltered C] {E : Type u₃} [Category.{v₃} E] (X : D)
    (T : C ⥤ D) [T.Final] (S : D ⥤ E) [S.Final] : Final (post X T S) := by
  apply final_of_natIso (postIsoMap₂ X T S).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `CostructuredArrow T d ⥤ CostructuredArrow (T ⋙ S) e` that `u : S.obj d ⟶ e`
induces via `CostructuredArrow.map₂` is initial, if `T` and `S` are initial and the domain of `T` is
filtered. -/
/-
**CategoryTheory.CostructuredArrow.initial_map** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `CostructuredArrow T d ⥤ CostructuredArrow (T ⋙ S) e` that `u : S.ob
j d ⟶ e`
induces via `CostructuredArrow.map₂` is initial, if `T` and `S` are initial and 
the domain of `T` is
filtered.
-/
instance CostructuredArrow.initial_map₂_id [IsCofiltered C] {E : Type u₃} [Category.{v₃} E]
    (T : C ⥤ D) [T.Initial] (S : D ⥤ E) [S.Initial] (d : D) (e : E)
    (u : S.obj d ⟶ e) : Initial (map₂ (F := 𝟭 _) (U := T ⋙ S) (𝟙 (T ⋙ S)) u) := by
  have := (T ⋙ S).initial_iff_isCofiltered_costructuredArrow.mp inferInstance e
  apply initial_of_natIso (map₂IsoPreEquivalenceInverseCompProj T S d e u).symm

/-- `CostructuredArrow.post T S X` is initial if `T` and `S` are initial and the domain of `T` is
cofiltered. -/
/-
**CategoryTheory.CostructuredArrow.initial_post** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.CostructuredArrow`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.IsCofiltered C] 
{E : Type u₃} [inst_3 : CategoryTheory.Category.{v₃, u₃} E] (X : D)   (T : Categ
oryTheory.Functor C D) [T.Initial] (S : CategoryTheory.Functor D E) [S.Initial],
   (CategoryTheory.CostructuredArrow.post T S X).Initial
参数：X : D；T : CategoryTheory.Functor C D；S : CategoryTheory.Functor D E；CategoryT
heory.CostructuredArrow.post T S X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_of_natIso`：initial_of_natIso {F F' : C ⥤ 
D} [Initial F] (i : F ≅ F') : Initial F' where out _
· 使用定理 `CategoryTheory.CostructuredArrow.initial_map₂_id`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   [CategoryTheory.Is…

--- 原说明 ---
`CostructuredArrow.post T S X` is initial if `T` and `S` are initial and the dom
ain of `T` is
cofiltered.
-/
instance CostructuredArrow.initial_post [IsCofiltered C] {E : Type u₃} [Category.{v₃} E] (X : D)
    (T : C ⥤ D) [T.Initial] (S : D ⥤ E) [S.Initial] : Initial (post T S X) := by
  apply initial_of_natIso (postIsoMap₂ X T S).symm

section Pi

variable {α : Type u₁} {I : α → Type u₂} [∀ s, Category.{v₂} (I s)]

set_option backward.defeqAttrib.useBackward true in
open IsFiltered in
/-
**CategoryTheory.final_eval** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：final_eval [forall s, IsFiltered (I s)] (s : α) : (Pi.eval I s).Final
参数：I s；s : α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_exists_of_isFiltered`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory
.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instIsFilteredOrEmptyForall`：∀ {α : Type w} {I : α → Type
 u₁} [inst : (i : α) → CategoryTheory.Category.{v₁, u₁} (I i)]   [∀ (i : α), Cat
egoryTheory.IsFilteredOrEmpty (I…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.IsFiltered.nonempty`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.IsFiltered C], Nonempty C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `CategoryTheory.IsFiltered.coeq_condition`：coeq_condition {j j' : C} (f f
' : j ⟶ j') : f ≫ coeqHom f f' = f' ≫ coeqHom f f'
-/
instance final_eval [∀ s, IsFiltered (I s)] (s : α) : (Pi.eval I s).Final := by
  classical
  apply Functor.final_of_exists_of_isFiltered
  · exact fun i => ⟨Function.update (fun t => nonempty.some) s i, ⟨by simpa using 𝟙 _⟩⟩
  · intro d c f g
    let c't : (∀ s, (c' : I s) × (c s ⟶ c')) := Function.update (fun t => ⟨c t, 𝟙 (c t)⟩)
      s ⟨coeq f g, coeqHom f g⟩
    refine ⟨fun t => (c't t).1, fun t => (c't t).2, ?_⟩
    dsimp only [Pi.eval_obj, Pi.eval_map, c't]
    rw [Function.update_self]
    simpa using coeq_condition _ _

set_option backward.defeqAttrib.useBackward true in
open IsCofiltered in
/-
**CategoryTheory.initial_eval** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：initial_eval [forall s, IsCofiltered (I s)] (s : α) : (Pi.eval I s).Initia
l
参数：I s；s : α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_of_exists_of_isCofiltered`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instIsCofilteredOrEmptyForall`：∀ {α : Type w} {I : α → Ty
pe u₁} [inst : (i : α) → CategoryTheory.Category.{v₁, u₁} (I i)]   [∀ (i : α), C
ategoryTheory.IsCofilteredOrEmpty …
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `CategoryTheory.IsCofiltered.nonempty`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C], Nonempty C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `CategoryTheory.IsCofiltered.eq_condition`：eq_condition {j j' : C} (f f' 
: j ⟶ j') : eqHom f f' ≫ f = eqHom f f' ≫ f'
-/
instance initial_eval [∀ s, IsCofiltered (I s)] (s : α) : (Pi.eval I s).Initial := by
  classical
  apply Functor.initial_of_exists_of_isCofiltered
  · exact fun i => ⟨Function.update (fun t => nonempty.some) s i, ⟨by simpa using 𝟙 _⟩⟩
  · intro d c f g
    let c't : (∀ s, (c' : I s) × (c' ⟶ c s)) := Function.update (fun t => ⟨c t, 𝟙 (c t)⟩)
      s ⟨eq f g, eqHom f g⟩
    refine ⟨fun t => (c't t).1, fun t => (c't t).2, ?_⟩
    dsimp only [Pi.eval_obj, Pi.eval_map, c't]
    rw [Function.update_self]
    simpa using eq_condition _ _

end Pi

section Prod

namespace IsFiltered

attribute [local instance] IsFiltered.isConnected IsCofiltered.isConnected

/-
**CategoryTheory.IsFiltered.final_fst** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
IsFiltered`。
形式化陈述：final_fst [IsFiltered D] : (Prod.fst C D).Final
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFiltered.isConnected`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [CategoryTheory.IsFiltered C], CategoryTheory.IsConnecte
d C
-/
instance final_fst [IsFiltered D] : (Prod.fst C D).Final := inferInstance
/-
**CategoryTheory.IsFiltered.final_snd** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
IsFiltered`。
形式化陈述：final_snd [IsFiltered C] : (Prod.snd C D).Final
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFiltered.isConnected`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [CategoryTheory.IsFiltered C], CategoryTheory.IsConnecte
d C
-/
instance final_snd [IsFiltered C] : (Prod.snd C D).Final := inferInstance
/-
**CategoryTheory.IsFiltered.initial_fst** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.IsFiltered`。
形式化陈述：initial_fst [IsCofiltered D] : (Prod.fst C D).Initial
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofiltered.isConnected`：∀ (C : Type u) [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.IsCofiltered C], CategoryTheory.IsConn
ected C
-/
instance initial_fst [IsCofiltered D] : (Prod.fst C D).Initial := inferInstance
/-
**CategoryTheory.IsFiltered.initial_snd** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.IsFiltered`。
形式化陈述：initial_snd [IsCofiltered C] : (Prod.snd C D).Initial
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofiltered.isConnected`：∀ (C : Type u) [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.IsCofiltered C], CategoryTheory.IsConn
ected C
-/
instance initial_snd [IsCofiltered C] : (Prod.snd C D).Initial := inferInstance

end IsFiltered

end Prod

end CategoryTheory

open CategoryTheory

/-
**Monotone.final_functor_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.final_functor_iff {J₁ J₂ : Type*} [Preorder J₁] [Preorder J₂] [Is
DirectedOrder J₁] {f : J₁ -> J₂} (hf : Monotone f) : hf.functor.Final ↔ forall (
j₂ : J₂), exists (j₁ : J₁), j₂ <= f j₁
参数：hf : Monotone f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.final_iff_of_isFiltered`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.isFilteredOrEmpty_of_directed_le`：∀ (α : Type u) [inst : 
Preorder α] [IsDirectedOrder α], CategoryTheory.IsFilteredOrEmpty α
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
-/
lemma Monotone.final_functor_iff {J₁ J₂ : Type*} [Preorder J₁] [Preorder J₂]
    [IsDirectedOrder J₁] {f : J₁ → J₂} (hf : Monotone f) :
    hf.functor.Final ↔ ∀ (j₂ : J₂), ∃ (j₁ : J₁), j₂ ≤ f j₁ := by
  rw [Functor.final_iff_of_isFiltered]
  constructor
  · rintro ⟨h, _⟩ j₂
    obtain ⟨j₁, ⟨φ⟩⟩ := h j₂
    exact ⟨j₁, leOfHom φ⟩
  · intro h
    constructor
    · intro j₂
      obtain ⟨j₁, h₁⟩ := h j₂
      exact ⟨j₁, ⟨homOfLE h₁⟩⟩
    · intro _ c _ _
      exact ⟨c, 𝟙 _, rfl⟩
/-
**Monotone.initial_functor_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.initial_functor_iff {J₁ J₂ : Type*} [Preorder J₁] [Preorder J₂] [
IsCodirectedOrder J₁] {f : J₁ -> J₂} (hf : Monotone f) : hf.functor.Initial ↔ ( 
forall j₁,exists j₂, f j₂ <= j₁)
参数：hf : Monotone f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.initial_iff_of_isCofiltered`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.isCofilteredOrEmpty_of_directed_ge`：∀ (α : Type u) [inst 
: Preorder α] [IsCodirectedOrder α], CategoryTheory.IsCofilteredOrEmpty α
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
-/
lemma Monotone.initial_functor_iff {J₁ J₂ : Type*} [Preorder J₁] [Preorder J₂]
    [IsCodirectedOrder J₁] {f : J₁ → J₂} (hf : Monotone f) :
    hf.functor.Initial ↔ ( ∀ j₁,∃ j₂, f j₂ ≤ j₁) := by
  rw [Functor.initial_iff_of_isCofiltered]
  constructor
  · rintro ⟨h, _⟩ j₂
    obtain ⟨j₁, ⟨φ⟩⟩ := h j₂
    exact ⟨j₁,leOfHom φ⟩
  · intro h
    constructor
    · intro j₂
      obtain ⟨j₁, h₁⟩ := h j₂
      exact ⟨j₁, ⟨homOfLE h₁⟩⟩
    · intro _ c _ _
      exact ⟨ c, 𝟙 _, rfl⟩
