/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Tactic.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Gluing data

We define `GlueData` as a family of data needed to glue topological spaces, schemes, etc. We
provide the API to realize it as a multispan diagram, and also state lemmas about its
interaction with a functor that preserves certain pullbacks.

-/

@[expose] public section


noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

universe v u₁ u₂

variable (C : Type u₁) [Category.{v} C] {C' : Type u₂} [Category.{v} C']

/-- A gluing datum consists of
1. An index type `J`
2. An object `U i` for each `i : J`.
3. An object `V i j` for each `i j : J`.
4. A monomorphism `f i j : V i j ⟶ U i` for each `i j : J`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : J`.

such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. The pullback for `f i j` and `f i k` exists.
9. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
10. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.
-/
/-
**CategoryTheory.GlueData** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：GlueData where /-- The index type `J` of a gluing datum -/ J : Type v /-- 
For each `i : J`, an object `U i` -/ U : J -> C /-- For each `i j : J`, an objec
t `V i j` -/ V : J × J -> C /-- For each `i j : J`, a monomorphism `f i j : V i 
j ⟶ U i` -/ f : forall i j, V (i, j) ⟶ U i f_mono : forall i j, Mono (f i j)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A gluing datum consists of
1. An index type `J`
2. An object `U i` for each `i : J`.
3. An object `V i j` for each `i j : J`.
4. A monomorphism `f i j : V i j ⟶ U i` for each `i j : J`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : J`.

such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. The pullback for `f i j` and `f i k` exists.
9. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V 
j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
10. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.
-/
structure GlueData where
  /-- The index type `J` of a gluing datum -/
  J : Type v
  /-- For each `i : J`, an object `U i` -/
  U : J → C
  /-- For each `i j : J`, an object `V i j` -/
  V : J × J → C
  /-- For each `i j : J`, a monomorphism `f i j : V i j ⟶ U i` -/
  f : ∀ i j, V (i, j) ⟶ U i
  f_mono : ∀ i j, Mono (f i j) := by infer_instance
  f_hasPullback : ∀ i j k, HasPullback (f i j) (f i k) := by infer_instance
  f_id : ∀ i, IsIso (f i i) := by infer_instance
  /-- For each `i j : J`, a transition map `t i j : V i j ⟶ V j i` -/
  t : ∀ i j, V (i, j) ⟶ V (j, i)
  t_id : ∀ i, t i i = 𝟙 _
  /-- The morphism via which `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through
  `V j k ×[U j] V j i ⟶ V j i` -/
  t' : ∀ i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)
  t_fac : ∀ i j k, t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j
  cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _

attribute [simp] GlueData.t_id

attribute [instance] GlueData.f_id GlueData.f_mono GlueData.f_hasPullback

attribute [reassoc] GlueData.t_fac GlueData.cocycle

namespace GlueData

variable {C}
variable (D : GlueData C)

@[simp]
/-
**CategoryTheory.GlueData.t'_iij** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GlueD
ata`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v, u₁} C] (D : CategoryTh
eory.GlueData C) (i j : D.J),   D.t' i i j = (CategoryTheory.Limits.pullbackSymm
etry (D.f i i) (D.f i j)).hom
参数：D : CategoryTheory.GlueData C；i j : D.J；CategoryTheory.Limits.pullbackSymmetr
y (D.f i i) (D.f i j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GlueData.f_hasPullback`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),  
 CategoryTheory.Limits.HasP…
· 使用定理 `CategoryTheory.GlueData.t'`：t'_iij (i j : D.J) : D.t' i i j = (pullbackS
ymmetry _ _).hom
· 使用定理 `CategoryTheory.GlueData.t_fac`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),   Categor
yTheory.CategoryStr…
· 使用定理 `CategoryTheory.GlueData.f_id`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i : self.J),   CategoryTheo
ry.IsIso (self.f i…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.IsIso.eq_comp_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.GlueData.t_id`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i : self.J),   self.t i i =
 CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Mono.right_cancellation`：∀ {C : Type u} {inst : CategoryT
heory.Category.{v, u} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.Mono f] {Z
 : C}   (g h : Z ⟶ X), Categ…
· 使用定理 `CategoryTheory.Limits.pullback.fst_of_mono`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cat
egoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.GlueData.f_mono`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j : self.J),   Category
Theory.Mono (self.f …
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst`：pullbackSymmetry_ho
m_comp_fst [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.fst g f = p
ullback.snd f g
-/
theorem t'_iij (i j : D.J) : D.t' i i j = (pullbackSymmetry _ _).hom := by
  have eq₁ := D.t_fac i i j
  have eq₂ := (IsIso.eq_comp_inv (D.f i i)).mpr (@pullback.condition _ _ _ _ _ _ (D.f i j) _)
  rw [D.t_id, Category.comp_id, eq₂] at eq₁
  have eq₃ := (IsIso.eq_comp_inv (D.f i i)).mp eq₁
  rw [Category.assoc, ← pullback.condition, ← Category.assoc] at eq₃
  exact
    Mono.right_cancellation _ _
      ((Mono.right_cancellation _ _ eq₃).trans (pullbackSymmetry_hom_comp_fst _ _).symm)
/-
**CategoryTheory.GlueData.t'_jii** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GlueD
ata`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v, u₁} C] (D : CategoryTh
eory.GlueData C) (i j : D.J),   D.t' j i i =     CategoryTheory.CategoryStruct.c
omp (CategoryTheory.Limits.pullback.fst (D.f j i) (D.f j i))       (CategoryTheo
ry.CategoryStruct.comp (D.t j i)         (CategoryTheory.inv (CategoryTheory.Lim
its.pullback.snd (D.f i i) (D.f i j))))
参数：D : CategoryTheory.GlueData C；i j : D.J；CategoryTheory.Limits.pullback.fst (D
.f j i) (D.f j i)；CategoryTheory.CategoryStruct.comp (D.t j i)         (Category
Theory.inv (CategoryTheory.Limits.pullback.snd (D.f i i) (D.f i j)))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GlueData.f_hasPullback`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),  
 CategoryTheory.Limits.HasP…
· 使用定理 `CategoryTheory.GlueData.t'`：t'_iij (i j : D.J) : D.t' i i j = (pullbackS
ymmetry _ _).hom
· 使用定理 `CategoryTheory.GlueData.f_id`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i : self.J),   CategoryTheo
ry.IsIso (self.f i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GlueData.t_fac`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),   Categor
yTheory.CategoryStr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem t'_jii (i j : D.J) : D.t' j i i = pullback.fst _ _ ≫ D.t j i ≫ inv (pullback.snd _ _) := by
  rw [← Category.assoc, ← D.t_fac]
  simp
/-
**CategoryTheory.GlueData.t'_iji** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GlueD
ata`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v, u₁} C] (D : CategoryTh
eory.GlueData C) (i j : D.J),   D.t' i j i =     CategoryTheory.CategoryStruct.c
omp (CategoryTheory.Limits.pullback.fst (D.f i j) (D.f i i))       (CategoryTheo
ry.CategoryStruct.comp (D.t i j)         (CategoryTheory.inv (CategoryTheory.Lim
its.pullback.snd (D.f j i) (D.f j i))))
参数：D : CategoryTheory.GlueData C；i j : D.J；CategoryTheory.Limits.pullback.fst (D
.f i j) (D.f i i)；CategoryTheory.CategoryStruct.comp (D.t i j)         (Category
Theory.inv (CategoryTheory.Limits.pullback.snd (D.f j i) (D.f j i)))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GlueData.f_hasPullback`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),  
 CategoryTheory.Limits.HasP…
· 使用定理 `CategoryTheory.GlueData.t'`：t'_iij (i j : D.J) : D.t' i i j = (pullbackS
ymmetry _ _).hom
· 使用定理 `CategoryTheory.GlueData.f_mono`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j : self.J),   Category
Theory.Mono (self.f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GlueData.t_fac`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),   Categor
yTheory.CategoryStr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem t'_iji (i j : D.J) : D.t' i j i = pullback.fst _ _ ≫ D.t i j ≫ inv (pullback.snd _ _) := by
  rw [← Category.assoc, ← D.t_fac]
  simp

@[reassoc, elementwise (attr := simp)]
/-
**CategoryTheory.GlueData.t_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GlueDa
ta`。
形式化陈述：t_inv (i j : D.J) : D.t i j ≫ D.t j i = 𝟙 _
参数：i j : D.J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GlueData.f_hasPullback`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),  
 CategoryTheory.Limits.HasP…
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `CategoryTheory.GlueData.f_id`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i : self.J),   CategoryTheo
ry.IsIso (self.f i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst`：pullbackSymmetry_ho
m_comp_fst [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.fst g f = p
ullback.snd f g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.GlueData.t'`：t'_iij (i j : D.J) : D.t' i i j = (pullbackS
ymmetry _ _).hom
· 使用定理 `CategoryTheory.GlueData.cocycle`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),   Categ
oryTheory.CategoryStr…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.IsIso.comp_inv_eq`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.eq_inv_comp`：eq_inv_comp (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f
· 使用定理 `CategoryTheory.GlueData.f_mono`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j : self.J),   Category
Theory.Mono (self.f …
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Limits.fst_eq_snd_of_mono_eq`：fst_eq_snd_of_mono_eq : pul
lback.fst f f = pullback.snd f f
· 使用定理 `CategoryTheory.GlueData.t'_iji`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v, u₁} C] (D : CategoryTheory.GlueData C) (i j : D.J),   D.t' i j i =  
   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.GlueData.t'_jii`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v, u₁} C] (D : CategoryTheory.GlueData C) (i j : D.J),   D.t' j i i =  
   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.GlueData.t'_iij`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v, u₁} C] (D : CategoryTheory.GlueData C) (i j : D.J),   D.t' i i j = (
CategoryTheory.Limit…
-/
theorem t_inv (i j : D.J) : D.t i j ≫ D.t j i = 𝟙 _ := by
  have eq : (pullbackSymmetry (D.f i i) (D.f i j)).hom =
      pullback.snd _ _ ≫ inv (pullback.fst _ _) := by simp
  have := D.cocycle i j i
  rw [D.t'_iij, D.t'_jii, D.t'_iji, fst_eq_snd_of_mono_eq, eq] at this
  simp only [Category.assoc, IsIso.inv_hom_id_assoc] at this
  rw [← IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq] at this
  simpa using this
/-
**CategoryTheory.GlueData.t'_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GlueD
ata`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v, u₁} C] (D : CategoryTh
eory.GlueData C) (i j k : D.J),   CategoryTheory.CategoryStruct.comp (D.t' i j k
)       (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullbackSymme
try (D.f j k) (D.f j i)).hom         (CategoryTheory.CategoryStruct.comp (D.t' j
 i k)           (CategoryTheory.Limits.pullbackSymmetry (D.f i k) (D.f i j)).hom
)) =     CategoryTheory.CategoryStruct.id (CategoryTheory.Limits.pullback (D.f i
 j) (D.f i k))
参数：D : CategoryTheory.GlueData C；i j k : D.J；D.t' i j k；CategoryTheory.CategoryS
truct.comp (CategoryTheory.Limits.pullbackSymmetry (D.f j k) (D.f j i)).hom     
    (CategoryTheory.CategoryStruct.comp (D.t' j i k)           (CategoryTheory.L
imits.pullbackSymmetry (D.f i k) (D.f i j)).hom)；CategoryTheory.Limits.pullback 
(D.f i j) (D.f i k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GlueData.f_hasPullback`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),  
 CategoryTheory.Limits.HasP…
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `CategoryTheory.GlueData.t'`：t'_iij (i j : D.J) : D.t' i i j = (pullbackS
ymmetry _ _).hom
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.pullback.fst_of_mono`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cat
egoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.GlueData.f_mono`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j : self.J),   Category
Theory.Mono (self.f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst`：pullbackSymmetry_ho
m_comp_fst [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.fst g f = p
ullback.snd f g
· 使用定理 `CategoryTheory.GlueData.t_fac`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),   Categor
yTheory.CategoryStr…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.GlueData.t_fac_assoc`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J) {Z :
 C}   (h : self.V (j, i) …
· 使用定理 `CategoryTheory.GlueData.t_inv`：t_inv (i j : D.J) : D.t i j ≫ D.t j i = 𝟙
 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem t'_inv (i j k : D.J) :
    D.t' i j k ≫ (pullbackSymmetry _ _).hom ≫ D.t' j i k ≫ (pullbackSymmetry _ _).hom = 𝟙 _ := by
  rw [← cancel_mono (pullback.fst (D.f i j) (D.f i k))]
  simp [t_fac, t_fac_assoc]
/-
**CategoryTheory.GlueData.t_isIso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Glue
Data`。
形式化陈述：t_isIso (i j : D.J) : IsIso (D.t i j)
参数：i j : D.J。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GlueData.t_inv`：t_inv (i j : D.J) : D.t i j ≫ D.t j i = 𝟙
 _
-/
instance t_isIso (i j : D.J) : IsIso (D.t i j) :=
  ⟨⟨D.t j i, D.t_inv _ _, D.t_inv _ _⟩⟩
/-
**CategoryTheory.GlueData.t'_isIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Glu
eData`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v, u₁} C] (D : CategoryTh
eory.GlueData C) (i j k : D.J),   CategoryTheory.IsIso (D.t' i j k)
参数：D : CategoryTheory.GlueData C；i j k : D.J；D.t' i j k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GlueData.f_hasPullback`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),  
 CategoryTheory.Limits.HasP…
· 使用定理 `CategoryTheory.GlueData.t'`：t'_iij (i j : D.J) : D.t' i i j = (pullbackS
ymmetry _ _).hom
· 使用定理 `CategoryTheory.GlueData.cocycle`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),   Categ
oryTheory.CategoryStr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
instance t'_isIso (i j k : D.J) : IsIso (D.t' i j k) :=
  ⟨⟨D.t' j k i ≫ D.t' k i j, D.cocycle _ _ _, by simpa using D.cocycle _ _ _⟩⟩

@[reassoc]
/-
**CategoryTheory.GlueData.t'_comp_eq_pullbackSymmetry** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.GlueData`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v, u₁} C] (D : CategoryTh
eory.GlueData C) (i j k : D.J),   CategoryTheory.CategoryStruct.comp (D.t' j k i
) (D.t' k i j) =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.p
ullbackSymmetry (D.f j k) (D.f j i)).hom       (CategoryTheory.CategoryStruct.co
mp (D.t' j i k) (CategoryTheory.Limits.pullbackSymmetry (D.f i k) (D.f i j)).hom
)
参数：D : CategoryTheory.GlueData C；i j k : D.J；D.t' j k i；D.t' k i j；CategoryTheor
y.Limits.pullbackSymmetry (D.f j k) (D.f j i)；CategoryTheory.CategoryStruct.comp
 (D.t' j i k) (CategoryTheory.Limits.pullbackSymmetry (D.f i k) (D.f i j)).hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GlueData.f_hasPullback`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),  
 CategoryTheory.Limits.HasP…
· 使用定理 `CategoryTheory.GlueData.t'`：t'_iij (i j : D.J) : D.t' i i j = (pullbackS
ymmetry _ _).hom
· 使用定理 `CategoryTheory.GlueData.t'_isIso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v, u₁} C] (D : CategoryTheory.GlueData C) (i j k : D.J),   CategoryTh
eory.IsIso (D.t' i j k…
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_hom_inv_id`：eq_inv_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : g = inv f
· 使用定理 `CategoryTheory.GlueData.cocycle`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),   Categ
oryTheory.CategoryStr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.pullback.fst_of_mono`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cat
egoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.GlueData.f_mono`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j : self.J),   Category
Theory.Mono (self.f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst`：pullbackSymmetry_ho
m_comp_fst [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.fst g f = p
ullback.snd f g
· 使用定理 `CategoryTheory.GlueData.t_fac`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),   Categor
yTheory.CategoryStr…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.GlueData.t_fac_assoc`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J) {Z :
 C}   (h : self.V (j, i) …
· 使用定理 `CategoryTheory.GlueData.t_inv`：t_inv (i j : D.J) : D.t i j ≫ D.t j i = 𝟙
 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem t'_comp_eq_pullbackSymmetry (i j k : D.J) :
    D.t' j k i ≫ D.t' k i j =
      (pullbackSymmetry _ _).hom ≫ D.t' j i k ≫ (pullbackSymmetry _ _).hom := by
  trans inv (D.t' i j k)
  · exact IsIso.eq_inv_of_hom_inv_id (D.cocycle _ _ _)
  · rw [← cancel_mono (pullback.fst (D.f i j) (D.f i k))]
    simp [t_fac, t_fac_assoc]

/-- (Implementation) The disjoint union of `U i`. -/
/-
**CategoryTheory.GlueData.sigmaOpens** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.G
lueData`。
形式化陈述：sigmaOpens [HasCoproduct D.U] : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) The disjoint union of `U i`.
-/
def sigmaOpens [HasCoproduct D.U] : C :=
  ∐ D.U

/-- (Implementation) The diagram to take colimit of. -/
/-
**CategoryTheory.GlueData.diagram** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Glue
Data`。
形式化陈述：diagram : MultispanIndex (.prod D.J) C where left
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) The diagram to take colimit of.
-/
def diagram : MultispanIndex (.prod D.J) C where
  left := D.V
  right := D.U
  fst := fun ⟨i, j⟩ => D.f i j
  snd := fun ⟨i, j⟩ => D.t i j ≫ D.f j i

@[simp]
/-
**CategoryTheory.GlueData.diagram_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
GlueData`。
形式化陈述：diagram_fst (i j : D.J) : D.diagram.fst ⟨i, j⟩ = D.f i j
参数：i j : D.J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagram_fst (i j : D.J) : D.diagram.fst ⟨i, j⟩ = D.f i j :=
  rfl

@[simp]
/-
**CategoryTheory.GlueData.diagram_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
GlueData`。
形式化陈述：diagram_snd (i j : D.J) : D.diagram.snd ⟨i, j⟩ = D.t i j ≫ D.f j i
参数：i j : D.J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagram_snd (i j : D.J) : D.diagram.snd ⟨i, j⟩ = D.t i j ≫ D.f j i :=
  rfl

@[simp]
/-
**CategoryTheory.GlueData.diagram_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.GlueData`。
形式化陈述：diagram_left : D.diagram.left = D.V
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagram_left : D.diagram.left = D.V :=
  rfl

@[simp]
/-
**CategoryTheory.GlueData.diagram_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.GlueData`。
形式化陈述：diagram_right : D.diagram.right = D.U
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagram_right : D.diagram.right = D.U :=
  rfl

section

variable [HasMulticoequalizer D.diagram]

/-- The glued object given a family of gluing data. -/
/-
**CategoryTheory.GlueData.glued** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GlueDa
ta`。
形式化陈述：glued : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The glued object given a family of gluing data.
-/
def glued : C :=
  multicoequalizer D.diagram

/-- The map `D.U i ⟶ D.glued` for each `i`. -/
/-
**CategoryTheory.GlueData.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `D.U i ⟶ D.glued` for each `i`.
-/
def ι (i : D.J) : D.U i ⟶ D.glued :=
  Multicoequalizer.π D.diagram i

@[elementwise (attr := simp)]
/-
**CategoryTheory.GlueData.glue_condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.GlueData`。
形式化陈述：glue_condition (i j : D.J) : D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i
参数：i j : D.J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Multicoequalizer.condition`：condition (a) : I.fst 
a ≫ Multicoequalizer.π I (J.fst a) = I.snd a ≫ Multicoequalizer.π I (J.snd a)
-/
theorem glue_condition (i j : D.J) : D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i :=
  (Category.assoc _ _ _).symm.trans (Multicoequalizer.condition D.diagram ⟨i, j⟩).symm

/-- The pullback cone spanned by `V i j ⟶ U i` and `V i j ⟶ U j`.
This will often be a pullback diagram. -/
/-
**CategoryTheory.GlueData.vPullbackCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.GlueData`。
形式化陈述：vPullbackCone (i j : D.J) : PullbackCone (D.ι i) (D.ι j)
参数：i j : D.J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback cone spanned by `V i j ⟶ U i` and `V i j ⟶ U j`.
This will often be a pullback diagram.
-/
def vPullbackCone (i j : D.J) : PullbackCone (D.ι i) (D.ι j) :=
  PullbackCone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)

variable [HasColimits C]

/-- The projection `∐ D.U ⟶ D.glued` given by the colimit. -/
/-
**CategoryTheory.GlueData.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection `∐ D.U ⟶ D.glued` given by the colimit.
-/
def π : D.sigmaOpens ⟶ D.glued :=
  Multicoequalizer.sigmaπ D.diagram
/-
**CategoryTheory.GlueData.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance π_epi : Epi D.π := inferInstanceAs <| Epi (Multicoequalizer.sigmaπ D.diagram)

end

/-
**CategoryTheory.GlueData.types_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GlueD
ata`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem types_π_surjective (D : GlueData Type*) : Function.Surjective D.π :=
  (epi_iff_surjective _).mp inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.GlueData.types_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GlueD
ata`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem types_ι_jointly_surjective (D : GlueData (Type v)) (x : D.glued) :
    ∃ (i : _) (y : D.U i), D.ι i y = x := by
  delta CategoryTheory.GlueData.ι
  simp_rw [← Multicoequalizer.ι_sigmaπ D.diagram]
  rcases D.types_π_surjective x with ⟨x', rfl⟩
  rw [← dsimp% ConcreteCategory.congr_hom
    (colimit.isoColimitCocone (Types.coproductColimitCocone _)).hom_inv_id x']
  rcases (colimit.isoColimitCocone (Types.coproductColimitCocone _)).hom x' with ⟨i, y⟩
  refine ⟨i, y, ?_⟩
  simp
  rfl

variable (F : C ⥤ C')

section
variable [∀ i j k, PreservesLimit (cospan (D.f i j) (D.f i k)) F]

/-
**CategoryTheory.GlueData.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i j k : D.J) : HasPullback (F.map (D.f i j)) (F.map (D.f i k)) :=
  ⟨⟨⟨_, isLimitOfHasPullbackOfPreservesLimit F (D.f i j) (D.f i k)⟩⟩⟩

/-- A functor that preserves the pullbacks of `f i j` and `f i k` can map a family of glue data. -/
@[simps]
/-
**CategoryTheory.GlueData.mapGlueData** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
GlueData`。
形式化陈述：mapGlueData : GlueData C' where J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GlueData.f_hasPullback`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),  
 CategoryTheory.Limits.HasP…
· 使用定理 `CategoryTheory.GlueData.instHasPullbackMapF`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v, u₁} C] {C' : Type u₂} [inst_1 : CategoryTheory.Category
.{v, u₂} C']   (D : CategoryTheor…
· 使用定理 `CategoryTheory.GlueData.t'`：t'_iij (i j : D.J) : D.t' i i j = (pullbackS
ymmetry _ _).hom

--- 原说明 ---
A functor that preserves the pullbacks of `f i j` and `f i k` can map a family o
f glue data.
-/
def mapGlueData : GlueData C' where
  J := D.J
  U i := F.obj (D.U i)
  V i := F.obj (D.V i)
  f i j := F.map (D.f i j)
  f_mono _ _ := preserves_mono_of_preservesLimit _ _
  f_id _ := inferInstance
  t i j := F.map (D.t i j)
  t_id i := by
    simp
  t' i j k :=
    (PreservesPullback.iso F (D.f i j) (D.f i k)).inv ≫
      F.map (D.t' i j k) ≫ (PreservesPullback.iso F (D.f j k) (D.f j i)).hom
  t_fac i j k := by simpa [Iso.inv_comp_eq] using congr_arg (fun f => F.map f) (D.t_fac i j k)
  cocycle i j k := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, D.cocycle,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The diagram of the image of a `GlueData` under a functor `F` is naturally isomorphic to the
original diagram of the `GlueData` via `F`.
-/
/-
**CategoryTheory.GlueData.diagramIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.G
lueData`。
形式化陈述：diagramIso : D.diagram.multispan ⋙ F ≅ (D.mapGlueData F).diagram.multispan
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram of the image of a `GlueData` under a functor `F` is naturally isomor
phic to the
original diagram of the `GlueData` via `F`.
-/
def diagramIso : D.diagram.multispan ⋙ F ≅ (D.mapGlueData F).diagram.multispan :=
  NatIso.ofComponents
    (fun x =>
      match x with
      | WalkingMultispan.left _ => Iso.refl _
      | WalkingMultispan.right _ => Iso.refl _)
    (by
      rintro (⟨_, _⟩ | _) _ (_ | _ | _) <;> simp)

@[simp]
/-
**CategoryTheory.GlueData.diagramIso_app_left** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.GlueData`。
形式化陈述：diagramIso_app_left (i : D.J × D.J) : (D.diagramIso F).app (WalkingMultisp
an.left i) = Iso.refl _
参数：i : D.J × D.J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagramIso_app_left (i : D.J × D.J) :
    (D.diagramIso F).app (WalkingMultispan.left i) = Iso.refl _ :=
  rfl

@[simp]
/-
**CategoryTheory.GlueData.diagramIso_app_right** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.GlueData`。
形式化陈述：diagramIso_app_right (i : D.J) : (D.diagramIso F).app (WalkingMultispan.ri
ght i) = Iso.refl _
参数：i : D.J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagramIso_app_right (i : D.J) :
    (D.diagramIso F).app (WalkingMultispan.right i) = Iso.refl _ :=
  rfl

@[simp]
/-
**CategoryTheory.GlueData.diagramIso_hom_app_left** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.GlueData`。
形式化陈述：diagramIso_hom_app_left (i : D.J × D.J) : (D.diagramIso F).hom.app (Walkin
gMultispan.left i) = 𝟙 _
参数：i : D.J × D.J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagramIso_hom_app_left (i : D.J × D.J) :
    (D.diagramIso F).hom.app (WalkingMultispan.left i) = 𝟙 _ :=
  rfl

@[simp]
/-
**CategoryTheory.GlueData.diagramIso_hom_app_right** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.GlueData`。
形式化陈述：diagramIso_hom_app_right (i : D.J) : (D.diagramIso F).hom.app (WalkingMult
ispan.right i) = 𝟙 _
参数：i : D.J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagramIso_hom_app_right (i : D.J) :
    (D.diagramIso F).hom.app (WalkingMultispan.right i) = 𝟙 _ :=
  rfl

@[simp]
/-
**CategoryTheory.GlueData.diagramIso_inv_app_left** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.GlueData`。
形式化陈述：diagramIso_inv_app_left (i : D.J × D.J) : (D.diagramIso F).inv.app (Walkin
gMultispan.left i) = 𝟙 _
参数：i : D.J × D.J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagramIso_inv_app_left (i : D.J × D.J) :
    (D.diagramIso F).inv.app (WalkingMultispan.left i) = 𝟙 _ :=
  rfl

@[simp]
/-
**CategoryTheory.GlueData.diagramIso_inv_app_right** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.GlueData`。
形式化陈述：diagramIso_inv_app_right (i : D.J) : (D.diagramIso F).inv.app (WalkingMult
ispan.right i) = 𝟙 _
参数：i : D.J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagramIso_inv_app_right (i : D.J) :
    (D.diagramIso F).inv.app (WalkingMultispan.right i) = 𝟙 _ :=
  rfl

end

variable [HasMulticoequalizer D.diagram] [PreservesColimit D.diagram.multispan F]

/-
**CategoryTheory.GlueData.hasColimit_multispan_comp** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.GlueData`。
形式化陈述：hasColimit_multispan_comp : HasColimit (D.diagram.multispan ⋙ F)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hasColimit_multispan_comp : HasColimit (D.diagram.multispan ⋙ F) :=
  ⟨⟨⟨_, isColimitOfPreserves _ (colimit.isColimit _)⟩⟩⟩

attribute [local instance] hasColimit_multispan_comp

variable [∀ i j k, PreservesLimit (cospan (D.f i j) (D.f i k)) F]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GlueData.hasColimit_mapGlueData_diagram** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.GlueData`。
形式化陈述：hasColimit_mapGlueData_diagram : HasMulticoequalizer (D.mapGlueData F).dia
gram
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_iso`：hasColimit_of_iso {F G : J ⥤ C}
 [HasColimit F] (α : G ≅ F) : HasColimit G
· 使用定理 `CategoryTheory.GlueData.hasColimit_multispan_comp`：hasColimit_multispan_
comp : HasColimit (D.diagram.multispan ⋙ F)
-/
theorem hasColimit_mapGlueData_diagram : HasMulticoequalizer (D.mapGlueData F).diagram :=
  hasColimit_of_iso (D.diagramIso F).symm

attribute [local instance] hasColimit_mapGlueData_diagram

set_option backward.isDefEq.respectTransparency false in
/-- If `F` preserves the gluing, we obtain an iso between the glued objects. -/
/-
**CategoryTheory.GlueData.gluedIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Glu
eData`。
形式化陈述：gluedIso : F.obj D.glued ≅ (D.mapGlueData F).glued
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GlueData.hasColimit_mapGlueData_diagram`：hasColimit_mapGl
ueData_diagram : HasMulticoequalizer (D.mapGlueData F).diagram

--- 原说明 ---
If `F` preserves the gluing, we obtain an iso between the glued objects.
-/
def gluedIso : F.obj D.glued ≅ (D.mapGlueData F).glued :=
  haveI : HasColimit (MultispanIndex.multispan (diagram (mapGlueData D F))) := inferInstance
  preservesColimitIso F D.diagram.multispan ≪≫ Limits.HasColimit.isoOfNatIso (D.diagramIso F)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_gluedIso_hom (i : D.J) : F.map (D.ι i) ≫ (D.gluedIso F).hom = (D.mapGlueData F).ι i := by
  simp [gluedIso, GlueData.ι]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_gluedIso_inv (i : D.J) : (D.mapGlueData F).ι i ≫ (D.gluedIso F).inv = F.map (D.ι i) := by
  rw [Iso.comp_inv_eq, ι_gluedIso_hom]

set_option backward.isDefEq.respectTransparency false in
/-- If `F` preserves the gluing, and reflects the pullback of `U i ⟶ glued` and `U j ⟶ glued`,
then `F` reflects the fact that `V_pullback_cone` is a pullback. -/
/-
**CategoryTheory.GlueData.vPullbackConeIsLimitOfMap** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.GlueData`。
形式化陈述：vPullbackConeIsLimitOfMap (i j : D.J) [ReflectsLimit (cospan (D.ι i) (D.ι 
j)) F] (hc : IsLimit ((D.mapGlueData F).vPullbackCone i j)) : IsLimit (D.vPullba
ckCone i j)
参数：i j : D.J；cospan (D.ι i) (D.ι j)；hc : IsLimit ((D.mapGlueData F).vPullbackCon
e i j)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GlueData.hasColimit_mapGlueData_diagram`：hasColimit_mapGl
ueData_diagram : HasMulticoequalizer (D.mapGlueData F).diagram
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `F` preserves the gluing, and reflects the pullback of `U i ⟶ glued` and `U j
 ⟶ glued`,
then `F` reflects the fact that `V_pullback_cone` is a pullback.
-/
def vPullbackConeIsLimitOfMap (i j : D.J) [ReflectsLimit (cospan (D.ι i) (D.ι j)) F]
    (hc : IsLimit ((D.mapGlueData F).vPullbackCone i j)) : IsLimit (D.vPullbackCone i j) := by
  apply isLimitOfReflects F
  apply (isLimitMapConePullbackConeEquiv _ _).symm _
  let e : cospan (F.map (D.ι i)) (F.map (D.ι j)) ≅
      cospan ((D.mapGlueData F).ι i) ((D.mapGlueData F).ι j) :=
    NatIso.ofComponents
      (fun x => by
        cases x
        exacts [D.gluedIso F, Iso.refl _])
      (by rintro (_ | _) (_ | _) (_ | _ | _) <;> simp)
  apply IsLimit.postcomposeHomEquiv e _ _
  apply hc.ofIsoLimit
  refine Cone.ext (Iso.refl _) ?_
  rintro (_ | _ | _)
  all_goals simp [e]; rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- If there is a forgetful functor into `Type` that preserves enough (co)limits, then `D.ι` will
be jointly surjective. -/
/-
**CategoryTheory.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If there is a forgetful functor into `Type` that preserves enough (co)limits, th
en `D.ι` will
be jointly surjective.
-/
theorem ι_jointly_surjective (F : C ⥤ Type v) [PreservesColimit D.diagram.multispan F]
    [∀ i j k : D.J, PreservesLimit (cospan (D.f i j) (D.f i k)) F] (x : F.obj D.glued) :
    ∃ (i : _) (y : F.obj (D.U i)), F.map (D.ι i) y = x := by
  let e := D.gluedIso F
  obtain ⟨i, y, eq⟩ := (D.mapGlueData F).types_ι_jointly_surjective (e.hom x)
  replace eq := congr_arg e.inv eq
  change ((D.mapGlueData F).ι i ≫ e.inv) y = (e.hom ≫ e.inv) x at eq
  rw [e.hom_inv_id, D.ι_gluedIso_inv] at eq
  exact ⟨i, y, eq⟩

end GlueData

section GlueData'

/--
This is a variant of `GlueData` that only requires conditions on `V (i, j)` when `i ≠ j`.
See `GlueData.ofGlueData'`
-/
/-
**CategoryTheory.GlueData'** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：GlueData' where /-- Indexing type of a glue data. -/ J : Type v /-- Object
s of a glue data to be glued. -/ U : J -> C /-- Objects representing the interse
ctions. -/ V : forall (i j : J), i != j -> C /-- The inclusion maps of the inter
section into the object. -/ f : forall i j h, V i j h ⟶ U i f_mono : forall i j 
h, Mono (f i j h)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a variant of `GlueData` that only requires conditions on `V (i, j)` when
 `i ≠ j`.
See `GlueData.ofGlueData'`
-/
structure GlueData' where
  /-- Indexing type of a glue data. -/
  J : Type v
  /-- Objects of a glue data to be glued. -/
  U : J → C
  /-- Objects representing the intersections. -/
  V : ∀ (i j : J), i ≠ j → C
  /-- The inclusion maps of the intersection into the object. -/
  f : ∀ i j h, V i j h ⟶ U i
  f_mono : ∀ i j h, Mono (f i j h) := by infer_instance
  f_hasPullback : ∀ i j k hij hik, HasPullback (f i j hij) (f i k hik) := by infer_instance
  /-- The transition maps between the intersections. -/
  t : ∀ i j h, V i j h ⟶ V j i h.symm
  /-- The transition maps between the intersection of intersections. -/
  t' : ∀ i j k hij hik hjk,
    pullback (f i j hij) (f i k hik) ⟶ pullback (f j k hjk) (f j i hij.symm)
  t_fac : ∀ i j k hij hik hjk, t' i j k hij hik hjk ≫ pullback.snd _ _ =
    pullback.fst _ _ ≫ t i j hij
  t_inv : ∀ i j hij, t i j hij ≫ t j i hij.symm = 𝟙 _
  cocycle : ∀ i j k hij hik hjk, t' i j k hij hik hjk ≫
    t' j k i hjk hij.symm hik.symm ≫ t' k i j hik.symm hjk.symm hij = 𝟙 _

attribute [local instance] GlueData'.f_mono GlueData'.f_hasPullback

attribute [reassoc (attr := simp)] GlueData'.t_inv GlueData'.cocycle

variable {C}

open scoped Classical in
/-- (Implementation detail) the constructed `GlueData.f` from a `GlueData'`. -/
/-
**CategoryTheory.GlueData'.f'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GlueData
'`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v, u₁} C] →     (D : Ca
tegoryTheory.GlueData' C) → (i j : D.J) → (if h : i = j then D.U i else D.V i j 
h) ⟶ D.U i
参数：D : CategoryTheory.GlueData' C；i j : D.J；if h : i = j then D.U i else D.V i j
 h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation detail) the constructed `GlueData.f` from a `GlueData'`.
-/
abbrev GlueData'.f' (D : GlueData' C) (i j : D.J) :
    (if h : i = j then D.U i else D.V i j h) ⟶ D.U i :=
  if h : i = j then eqToHom (dif_pos h) else eqToHom (dif_neg h) ≫ D.f i j h
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (D : GlueData' C) (i j : D.J) :
    Mono (D.f' i j) := by dsimp [GlueData'.f']; split_ifs <;> infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (D : GlueData' C) (i : D.J) :
    IsIso (D.f' i i) := by simp only [GlueData'.f', ↓reduceDIte]; infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (D : GlueData' C) (i j k : D.J) :
    HasPullback (D.f' i j) (D.f' i k) := by
  if hij : i = j then
    apply +allowSynthFailures hasPullback_of_left_iso
    simp only [GlueData'.f', dif_pos hij]
    infer_instance
  else if hik : i = k then
    apply +allowSynthFailures hasPullback_of_right_iso
    simp only [GlueData'.f', dif_pos hik]
    infer_instance
  else
    have {X Y Z : C} (f : X ⟶ Y) (e : Z = X) : eqToHom e ≫ f ≍ f := by subst e; simp
    convert! D.f_hasPullback i j k hij hik <;> simp [GlueData'.f', hij, hik, this]

open scoped Classical in
/-- (Implementation detail) the constructed `GlueData.t'` from a `GlueData'`. -/
/-
**CategoryTheory.GlueData'.t''** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GlueDat
a'`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v, u₁} C] →     (D : Ca
tegoryTheory.GlueData' C) →       (i j k : D.J) →         CategoryTheory.Limits.
pullback (D.f' i j) (D.f' i k) ⟶ CategoryTheory.Limits.pullback (D.f' j k) (D.f'
 j i)
参数：D : CategoryTheory.GlueData' C；i j k : D.J；D.f' i j；D.f' i k；D.f' j k；D.f' j 
i。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasPullbackF'`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v, u₁} C] (D : CategoryTheory.GlueData' C) (i j k : D.J),   CategoryT
heory.Limits.HasPullba…
· 使用定理 `CategoryTheory.GlueData'.f_hasPullback`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v, u₁} C] (self : CategoryTheory.GlueData' C) (i j k : self.J) 
  (hij : i ≠ j) (hik : i ≠ k…

--- 原说明 ---
(Implementation detail) the constructed `GlueData.t'` from a `GlueData'`.
-/
def GlueData'.t'' (D : GlueData' C) (i j k : D.J) :
    pullback (D.f' i j) (D.f' i k) ⟶ pullback (D.f' j k) (D.f' j i) :=
  if hij : i = j then
    (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ (eqToHom (by aesop)) (eqToHom (by aesop)) (eqToHom (by aesop))
        (by aesop) (by aesop)
  else if hik : i = k then
    have : IsIso (pullback.snd (D.f' j k) (D.f' j i)) := by
      subst hik; infer_instance
    pullback.fst _ _ ≫ eqToHom (dif_neg hij) ≫ D.t _ _ _ ≫
      eqToHom (dif_neg (Ne.symm hij)).symm ≫ inv (pullback.snd _ _)
  else if hjk : j = k then
    have : IsIso (pullback.snd (D.f' j k) (D.f' j i)) := by
      apply +allowSynthFailures pullback_snd_iso_of_left_iso
      simp only [hjk, GlueData'.f', ↓reduceDIte]
      infer_instance
    pullback.fst _ _ ≫ eqToHom (dif_neg hij) ≫ D.t _ _ _ ≫
      eqToHom (dif_neg (Ne.symm hij)).symm ≫ inv (pullback.snd _ _)
  else
    haveI := Ne.symm hij
    pullback.map _ _ _ _ (eqToHom (by aesop)) (eqToHom (by rw [dif_neg hik]))
        (eqToHom (by simp)) (by delta f'; aesop) (by delta f'; aesop) ≫
      D.t' i j k hij hik hjk ≫
      pullback.map _ _ _ _ (eqToHom (by aesop)) (eqToHom (by aesop)) (eqToHom (by simp))
        (by delta f'; aesop) (by delta f'; aesop)

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
The constructed `GlueData` of a `GlueData'`, where `GlueData'` is a variant of `GlueData` that only
requires conditions on `V (i, j)` when `i ≠ j`.
-/
/-
**CategoryTheory.GlueData.ofGlueData'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
GlueData`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v, u₁} C] → CategoryTheor
y.GlueData' C → CategoryTheory.GlueData C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructed `GlueData` of a `GlueData'`, where `GlueData'` is a variant of `
GlueData` that only
requires conditions on `V (i, j)` when `i ≠ j`.
-/
def GlueData.ofGlueData' (D : GlueData' C) : GlueData C where
  J := D.J
  U := D.U
  V ij := if h : ij.1 = ij.2 then D.U ij.1 else D.V ij.1 ij.2 h
  f i j := D.f' i j
  f_id i := by simp only [↓reduceDIte, GlueData'.f']; infer_instance
  t i j := if h : i = j then eqToHom (by simp [h]) else
    eqToHom (dif_neg h) ≫ D.t i j h ≫ eqToHom (dif_neg (Ne.symm h)).symm
  t_id i := by simp
  t' := D.t''
  t_fac i j k := by
    delta GlueData'.t''
    obtain rfl | _ := eq_or_ne i j
    · simp
    obtain rfl | _ := eq_or_ne i k
    · simp [*]
    obtain rfl | _ := eq_or_ne j k
    · simp [*]
    · simp [*, reassoc_of% D.t_fac]
  cocycle i j k := by
    delta GlueData'.t''
    if hij : i = j then
      subst hij
      if hik : i = k then
        subst hik
        ext <;> simp
      else
        simp [hik, Ne.symm hik, fst_eq_snd_of_mono_eq]
    else if hik : i = k then
      subst hik
      ext <;> simp [hij, Ne.symm hij, fst_eq_snd_of_mono_eq, pullback.condition_assoc]
    else if hjk : j = k then
      subst hjk
      ext <;> simp [hij, Ne.symm hij, fst_eq_snd_of_mono_eq]
    else
      ext <;> simp [hij, Ne.symm hij, hik, Ne.symm hik, hjk, Ne.symm hjk,
        pullback.map_comp_assoc]

end GlueData'

end CategoryTheory

