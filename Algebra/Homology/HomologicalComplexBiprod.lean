/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Additive

/-! # Binary biproducts of homological complexes

In this file, it is shown that if two homological complex `K` and `L` in
a preadditive category are such that for all `i : ι`, the binary biproduct
`K.X i ⊞ L.X i` exists, then `K ⊞ L` exists, and there is an isomorphism
`biprodXIso K L i : (K ⊞ L).X i ≅ (K.X i) ⊞ (L.X i)`.

-/

@[expose] public section
open CategoryTheory Limits

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]

/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : ι) : HasBinaryBiproduct ((eval C c i).obj K) ((eval C c i).obj L) := by
  dsimp [eval]
  infer_instance
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : ι) : HasLimit ((pair K L) ⋙ (eval C c i)) := by
  have e : _ ≅ pair (K.X i) (L.X i) := diagramIsoPair (pair K L ⋙ eval C c i)
  exact hasLimit_of_iso e.symm
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : ι) : HasColimit ((pair K L) ⋙ (eval C c i)) := by
  have e : _ ≅ pair (K.X i) (L.X i) := diagramIsoPair (pair K L ⋙ eval C c i)
  exact hasColimit_of_iso e
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasBinaryBiproduct K L := HasBinaryBiproduct.of_hasBinaryProduct _ _
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : ι) : PreservesBinaryBiproduct K L (eval C c i) :=
  preservesBinaryBiproduct_of_preservesBinaryProduct _

/-- The canonical isomorphism `(K ⊞ L).X i ≅ (K.X i) ⊞ (L.X i)`. -/
/-
**HomologicalComplex.biprodXIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：biprodXIso (i : ι) : (K ⊞ L).X i ≅ (K.X i) ⊞ (L.X i)
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `HomologicalComplex.instPreservesBinaryBiproductEval`：∀ {C : Type u_1} {ι
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryThe
ory.Preadditive C]   {c : ComplexShape ι}…

--- 原说明 ---
The canonical isomorphism `(K ⊞ L).X i ≅ (K.X i) ⊞ (L.X i)`.
-/
noncomputable def biprodXIso (i : ι) : (K ⊞ L).X i ≅ (K.X i) ⊞ (L.X i) :=
  (eval C c i).mapBiprod K L

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.inl_biprodXIso_inv** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：inl_biprodXIso_inv (i : ι) : biprod.inl ≫ (biprodXIso K L i).inv = (biprod
.inl : K ⟶ K ⊞ L).f i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_biprodXIso_inv (i : ι) :
    biprod.inl ≫ (biprodXIso K L i).inv = (biprod.inl : K ⟶ K ⊞ L).f i := by
  simp [biprodXIso]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.inr_biprodXIso_inv** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：inr_biprodXIso_inv (i : ι) : biprod.inr ≫ (biprodXIso K L i).inv = (biprod
.inr : L ⟶ K ⊞ L).f i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_biprodXIso_inv (i : ι) :
    biprod.inr ≫ (biprodXIso K L i).inv = (biprod.inr : L ⟶ K ⊞ L).f i := by
  simp [biprodXIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.biprodXIso_hom_fst** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：biprodXIso_hom_fst (i : ι) : (biprodXIso K L i).hom ≫ biprod.fst = (biprod
.fst : K ⊞ L ⟶ K).f i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `HomologicalComplex.instPreservesBinaryBiproductEval`：∀ {C : Type u_1} {ι
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryThe
ory.Preadditive C]   {c : ComplexShape ι}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma biprodXIso_hom_fst (i : ι) :
    (biprodXIso K L i).hom ≫ biprod.fst = (biprod.fst : K ⊞ L ⟶ K).f i := by
  simp [biprodXIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.biprodXIso_hom_snd** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：biprodXIso_hom_snd (i : ι) : (biprodXIso K L i).hom ≫ biprod.snd = (biprod
.snd : K ⊞ L ⟶ L).f i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `HomologicalComplex.instPreservesBinaryBiproductEval`：∀ {C : Type u_1} {ι
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryThe
ory.Preadditive C]   {c : ComplexShape ι}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma biprodXIso_hom_snd (i : ι) :
    (biprodXIso K L i).hom ≫ biprod.snd = (biprod.snd : K ⊞ L ⟶ L).f i := by
  simp [biprodXIso]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.biprod_inl_fst_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：biprod_inl_fst_f (i : ι) : (biprod.inl : K ⟶ K ⊞ L).f i ≫ (biprod.fst : K 
⊞ L ⟶ K).f i = 𝟙 _
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.comp_f`：comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f
 : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : (f ≫ g).f i = f.f i ≫ g.f i
· 使用定理 `CategoryTheory.Limits.biprod.inl_fst`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
· 使用定理 `HomologicalComplex.id_f`：id_f (C : HomologicalComplex V c) (i : ι) : Hom
.f (𝟙 C) i = 𝟙 (C.X i)
-/
lemma biprod_inl_fst_f (i : ι) :
    (biprod.inl : K ⟶ K ⊞ L).f i ≫ (biprod.fst : K ⊞ L ⟶ K).f i = 𝟙 _ := by
  rw [← comp_f, biprod.inl_fst, id_f]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.biprod_inl_snd_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：biprod_inl_snd_f (i : ι) : (biprod.inl : K ⟶ K ⊞ L).f i ≫ (biprod.snd : K 
⊞ L ⟶ L).f i = 0
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.comp_f`：comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f
 : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : (f ≫ g).f i = f.f i ≫ g.f i
· 使用定理 `CategoryTheory.Limits.biprod.inl_snd`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
· 使用定理 `HomologicalComplex.zero_f`：zero_f (C D : HomologicalComplex V c) (i : ι)
 : (0 : C ⟶ D).f i = 0
-/
lemma biprod_inl_snd_f (i : ι) :
    (biprod.inl : K ⟶ K ⊞ L).f i ≫ (biprod.snd : K ⊞ L ⟶ L).f i = 0 := by
  rw [← comp_f, biprod.inl_snd, zero_f]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.biprod_inr_fst_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：biprod_inr_fst_f (i : ι) : (biprod.inr : L ⟶ K ⊞ L).f i ≫ (biprod.fst : K 
⊞ L ⟶ K).f i = 0
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.comp_f`：comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f
 : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : (f ≫ g).f i = f.f i ≫ g.f i
· 使用定理 `CategoryTheory.Limits.biprod.inr_fst`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
· 使用定理 `HomologicalComplex.zero_f`：zero_f (C D : HomologicalComplex V c) (i : ι)
 : (0 : C ⟶ D).f i = 0
-/
lemma biprod_inr_fst_f (i : ι) :
    (biprod.inr : L ⟶ K ⊞ L).f i ≫ (biprod.fst : K ⊞ L ⟶ K).f i = 0 := by
  rw [← comp_f, biprod.inr_fst, zero_f]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.biprod_inr_snd_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：biprod_inr_snd_f (i : ι) : (biprod.inr : L ⟶ K ⊞ L).f i ≫ (biprod.snd : K 
⊞ L ⟶ L).f i = 𝟙 _
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.comp_f`：comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f
 : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : (f ≫ g).f i = f.f i ≫ g.f i
· 使用定理 `CategoryTheory.Limits.biprod.inr_snd`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
· 使用定理 `HomologicalComplex.id_f`：id_f (C : HomologicalComplex V c) (i : ι) : Hom
.f (𝟙 C) i = 𝟙 (C.X i)
-/
lemma biprod_inr_snd_f (i : ι) :
    (biprod.inr : L ⟶ K ⊞ L).f i ≫ (biprod.snd : K ⊞ L ⟶ L).f i = 𝟙 _ := by
  rw [← comp_f, biprod.inr_snd, id_f]

@[simp]
/-
**HomologicalComplex.biprod_total_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：biprod_total_f (i : ι) : (biprod.fst : K ⊞ L ⟶ K).f i ≫ (biprod.inl : K ⟶ 
K ⊞ L).f i + (biprod.snd : K ⊞ L ⟶ L).f i ≫ (biprod.inr : L ⟶ K ⊞ L).f i = 𝟙 ((b
iprod K L).X i)
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.biprod.total`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y : C}   [inst_2
 : CategoryTheory.Limits…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma biprod_total_f (i : ι) :
    (biprod.fst : K ⊞ L ⟶ K).f i ≫ (biprod.inl : K ⟶ K ⊞ L).f i +
      (biprod.snd : K ⊞ L ⟶ L).f i ≫ (biprod.inr : L ⟶ K ⊞ L).f i =
    𝟙 ((biprod K L).X i) := by
  simp [← comp_f, ← add_f_apply]

variable {K L}

section

variable {A : C} {i : ι}

/-
**HomologicalComplex.biprodX_ext_from_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homological
Complex`。
形式化陈述：biprodX_ext_from_iff {f g : (K ⊞ L).X i ⟶ A} : f = g ↔ (biprod.inl : K ⟶ K
 ⊞ L).f i ≫ f = (biprod.inl : K ⟶ K ⊞ L).f i ≫ g ∧ (biprod.inr : L ⟶ K ⊞ L).f i 
≫ f = (biprod.inr : L ⟶ K ⊞ L).f i ≫ g
参数：K ⊞ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
lemma biprodX_ext_from_iff {f g : (K ⊞ L).X i ⟶ A} :
    f = g ↔ (biprod.inl : K ⟶ K ⊞ L).f i ≫ f = (biprod.inl : K ⟶ K ⊞ L).f i ≫ g ∧
      (biprod.inr : L ⟶ K ⊞ L).f i ≫ f = (biprod.inr : L ⟶ K ⊞ L).f i ≫ g := by
  refine ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  rw [← cancel_epi (𝟙 _)]
  simp [← biprod_total_f, h₁, h₂]

@[ext]
/-
**HomologicalComplex.biprodX_ext_from** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：biprodX_ext_from {f g : (K ⊞ L).X i ⟶ A} (h₁ : (biprod.inl : K ⟶ K ⊞ L).f 
i ≫ f = (biprod.inl : K ⟶ K ⊞ L).f i ≫ g) (h₂ : (biprod.inr : L ⟶ K ⊞ L).f i ≫ f
 = (biprod.inr : L ⟶ K ⊞ L).f i ≫ g) : f = g
参数：K ⊞ L；h₁ : (biprod.inl : K ⟶ K ⊞ L).f i ≫ f = (biprod.inl : K ⟶ K ⊞ L).f i ≫ 
g；h₂ : (biprod.inr : L ⟶ K ⊞ L).f i ≫ f = (biprod.inr : L ⟶ K ⊞ L).f i ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma biprodX_ext_from {f g : (K ⊞ L).X i ⟶ A}
    (h₁ : (biprod.inl : K ⟶ K ⊞ L).f i ≫ f = (biprod.inl : K ⟶ K ⊞ L).f i ≫ g)
    (h₂ : (biprod.inr : L ⟶ K ⊞ L).f i ≫ f = (biprod.inr : L ⟶ K ⊞ L).f i ≫ g) :
    f = g := by
  simp [biprodX_ext_from_iff, h₁, h₂]
/-
**HomologicalComplex.biprodX_ext_to_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：biprodX_ext_to_iff {f g : A ⟶ (K ⊞ L).X i} : f = g ↔ f ≫ (biprod.fst : K ⊞
 L ⟶ K).f i = g ≫ (biprod.fst : K ⊞ L ⟶ K).f i ∧ f ≫ (biprod.snd : K ⊞ L ⟶ L).f 
i = g ≫ (biprod.snd : K ⊞ L ⟶ L).f i
参数：K ⊞ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
-/
lemma biprodX_ext_to_iff {f g : A ⟶ (K ⊞ L).X i} :
    f = g ↔ f ≫ (biprod.fst : K ⊞ L ⟶ K).f i = g ≫ (biprod.fst : K ⊞ L ⟶ K).f i ∧
      f ≫ (biprod.snd : K ⊞ L ⟶ L).f i = g ≫ (biprod.snd : K ⊞ L ⟶ L).f i := by
  refine ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  rw [← cancel_mono (𝟙 _)]
  simp [← biprod_total_f, reassoc_of% h₁, reassoc_of% h₂]

@[ext]
/-
**HomologicalComplex.biprodX_ext_to** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：biprodX_ext_to {f g : A ⟶ (K ⊞ L).X i} (h₁ : f ≫ (biprod.fst : K ⊞ L ⟶ K).
f i = g ≫ (biprod.fst : K ⊞ L ⟶ K).f i) (h₂ : f ≫ (biprod.snd : K ⊞ L ⟶ L).f i =
 g ≫ (biprod.snd : K ⊞ L ⟶ L).f i) : f = g
参数：K ⊞ L；h₁ : f ≫ (biprod.fst : K ⊞ L ⟶ K).f i = g ≫ (biprod.fst : K ⊞ L ⟶ K).f 
i；h₂ : f ≫ (biprod.snd : K ⊞ L ⟶ L).f i = g ≫ (biprod.snd : K ⊞ L ⟶ L).f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma biprodX_ext_to {f g : A ⟶ (K ⊞ L).X i}
    (h₁ : f ≫ (biprod.fst : K ⊞ L ⟶ K).f i = g ≫ (biprod.fst : K ⊞ L ⟶ K).f i)
    (h₂ : f ≫ (biprod.snd : K ⊞ L ⟶ L).f i = g ≫ (biprod.snd : K ⊞ L ⟶ L).f i) :
    f = g := by
  simp [biprodX_ext_to_iff, h₁, h₂]

end

variable {M : HomologicalComplex C c}

@[reassoc (attr := simp)]
/-
**HomologicalComplex.biprod_inl_desc_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：biprod_inl_desc_f (α : K ⟶ M) (β : L ⟶ M) (i : ι) : (biprod.inl : K ⟶ K ⊞ 
L).f i ≫ (biprod.desc α β).f i = α.f i
参数：α : K ⟶ M；β : L ⟶ M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.comp_f`：comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f
 : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : (f ≫ g).f i = f.f i ≫ g.f i
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
lemma biprod_inl_desc_f (α : K ⟶ M) (β : L ⟶ M) (i : ι) :
    (biprod.inl : K ⟶ K ⊞ L).f i ≫ (biprod.desc α β).f i = α.f i := by
  rw [← comp_f, biprod.inl_desc]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.biprod_inr_desc_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：biprod_inr_desc_f (α : K ⟶ M) (β : L ⟶ M) (i : ι) : (biprod.inr : L ⟶ K ⊞ 
L).f i ≫ (biprod.desc α β).f i = β.f i
参数：α : K ⟶ M；β : L ⟶ M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.comp_f`：comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f
 : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : (f ≫ g).f i = f.f i ≫ g.f i
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
lemma biprod_inr_desc_f (α : K ⟶ M) (β : L ⟶ M) (i : ι) :
    (biprod.inr : L ⟶ K ⊞ L).f i ≫ (biprod.desc α β).f i = β.f i := by
  rw [← comp_f, biprod.inr_desc]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.biprod_lift_fst_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：biprod_lift_fst_f (α : M ⟶ K) (β : M ⟶ L) (i : ι) : (biprod.lift α β).f i 
≫ (biprod.fst : K ⊞ L ⟶ K).f i = α.f i
参数：α : M ⟶ K；β : M ⟶ L；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.comp_f`：comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f
 : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : (f ≫ g).f i = f.f i ≫ g.f i
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
lemma biprod_lift_fst_f (α : M ⟶ K) (β : M ⟶ L) (i : ι) :
    (biprod.lift α β).f i ≫ (biprod.fst : K ⊞ L ⟶ K).f i = α.f i := by
  rw [← comp_f, biprod.lift_fst]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.biprod_lift_snd_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：biprod_lift_snd_f (α : M ⟶ K) (β : M ⟶ L) (i : ι) : (biprod.lift α β).f i 
≫ (biprod.snd : K ⊞ L ⟶ L).f i = β.f i
参数：α : M ⟶ K；β : M ⟶ L；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.comp_f`：comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f
 : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : (f ≫ g).f i = f.f i ≫ g.f i
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
lemma biprod_lift_snd_f (α : M ⟶ K) (β : M ⟶ L) (i : ι) :
    (biprod.lift α β).f i ≫ (biprod.snd : K ⊞ L ⟶ L).f i = β.f i := by
  rw [← comp_f, biprod.lift_snd]

end HomologicalComplex

