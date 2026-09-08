/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# The mapping cocone

Given a morphism `φ : K ⟶ L` of cochain complexes, the mapping cone
allows to obtain a triangle `K ⟶ L ⟶ mappingCone φ ⟶ ...`. In this
file, we define the mapping cocone, which fits in a rotated triangle:
`mappingCocone φ ⟶ K ⟶ L ⟶ ...`.

-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex Pretriangulated

namespace CochainComplex

open HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-- The mapping cocone of a morphism `φ : K ⟶ L` of cochain complexes: it is
`(mappingCone φ)⟦(-1 : ℤ)⟧`. -/
/-
**CochainComplex.mappingCocone** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：mappingCocone [HasHomotopyCofiber φ] : CochainComplex C Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The mapping cocone of a morphism `φ : K ⟶ L` of cochain complexes: it is
`(mappingCone φ)⟦(-1 : ℤ)⟧`.
-/
noncomputable def mappingCocone [HasHomotopyCofiber φ] :
    CochainComplex C ℤ := (mappingCone φ)⟦(-1 : ℤ)⟧

namespace mappingCocone

section

variable [HasHomotopyCofiber φ]

/-- The first projection `mappingCocone φ ⟶ K`. -/
/-
**CochainComplex.mappingCocone.fst** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.map
pingCocone`。
形式化陈述：fst : mappingCocone φ ⟶ K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection `mappingCocone φ ⟶ K`.
-/
noncomputable def fst : mappingCocone φ ⟶ K :=
  -((mappingCone.fst φ).leftShift (-1) 0 (add_neg_cancel 1)).homOf

/-- The second projection in `Cochain (mappingCocone φ) L (-1)`. -/
/-
**CochainComplex.mappingCocone.snd** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.map
pingCocone`。
形式化陈述：snd : Cochain (mappingCocone φ) L (-1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection in `Cochain (mappingCocone φ) L (-1)`.
-/
noncomputable def snd : Cochain (mappingCocone φ) L (-1) :=
  (mappingCone.snd φ).leftShift (-1) (-1) (zero_add _)

/-- The left inclusion in `Cochain K (mappingCocone φ) 0`. -/
/-
**CochainComplex.mappingCocone.inl** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.map
pingCocone`。
形式化陈述：inl : Cochain K (mappingCocone φ) 0
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left inclusion in `Cochain K (mappingCocone φ) 0`.
-/
noncomputable def inl : Cochain K (mappingCocone φ) 0 :=
  (mappingCone.inl φ).rightShift (-1) 0 (zero_add _)

/-- The right inclusion in `Cocycle L (mappingCocone φ) 1`. -/
/-
**CochainComplex.mappingCocone.inr** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.map
pingCocone`。
形式化陈述：inr : Cocycle L (mappingCocone φ) 1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right inclusion in `Cocycle L (mappingCocone φ) 1`.
-/
noncomputable def inr : Cocycle L (mappingCocone φ) 1 :=
  (Cocycle.ofHom (mappingCone.inr φ)).rightShift (-1) 1 (by lia)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCocone.inl_v_fst_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex.mappingCocone`。
形式化陈述：inl_v_fst_f (p : Int) : (inl φ).v p p (add_zero p) ≫ (fst φ).f p = 𝟙 _
参数：p : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Int.ediv_self`：∀ {a : ℤ}, a ≠ 0 → a / a = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Units.neg_smul`：Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u
 : Rˣ) (x : M) : -u • x = -(u • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `CochainComplex.mappingCone.inl_v_fst_v`：inl_v_fst_v (p q : Int) (hpq : q
 + 1 = p) : (inl φ).v p q (by rw [← hpq, add_neg_cancel_right]) ≫ (fst φ : Cocha
in (mappingCone φ) F 1).v q …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_v_fst_f (p : ℤ) :
    (inl φ).v p p (add_zero p) ≫ (fst φ).f p = 𝟙 _ := by
  simp [inl, fst, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCocone.inl_v_snd_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex.mappingCocone`。
形式化陈述：inl_v_snd_v (p q : Int) (hpq : p + -1 = q) : (inl φ).v p p (add_zero p) ≫ 
(snd φ).v p q hpq = 0
参数：p q : Int；hpq : p + -1 = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Int.ediv_self`：∀ {a : ℤ}, a ≠ 0 → a / a = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.Linear.comp_units_smul`：comp_units_smul {X Y Z : C} (f : 
X ⟶ Y) (r : Rˣ) (g : Y ⟶ Z) : f ≫ (r • g) = r • f ≫ g
· 使用引理 `CochainComplex.mappingCone.inl_v_snd_v`：inl_v_snd_v (p q : Int) (hpq : p
 + (-1) = q) : (inl φ).v p q hpq ≫ (snd φ).v q q (add_zero q) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma inl_v_snd_v (p q : ℤ) (hpq : p + -1 = q) :
    (inl φ).v p p (add_zero p) ≫ (snd φ).v p q hpq = 0 := by
  obtain rfl : q = p + -1 := by lia
  simp [inl, snd, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v _ _ _ _ _ _ hpq]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCocone.inr_v_fst_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex.mappingCocone`。
形式化陈述：inr_v_fst_f (p q : Int) (hpq : p + 1 = q) : (inr φ).1.v p q hpq ≫ (fst φ).
f q = 0
参数：p q : Int；hpq : p + 1 = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.rightShift_coe`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {K 
L : CochainComplex C ℤ} {n : ℤ} (γ : C…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CochainComplex.HomComplex.Cocycle.ofHom_coe`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : C
ochainComplex C ℤ} (φ : F ⟶ G),  …
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `CochainComplex.HomComplex.Cocycle.homOf_f`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} (z : CochainCo…
· 使用定理 `CochainComplex.HomComplex.Cocycle.leftShift_coe`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {K L
 : CochainComplex C ℤ} {n : ℤ} (γ : C…
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Int.ediv_self`：∀ {a : ℤ}, a ≠ 0 → a / a = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Units.neg_smul`：Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u
 : Rˣ) (x : M) : -u • x = -(u • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
（共 32 条，此处仅展示前 30 条）
-/
lemma inr_v_fst_f (p q : ℤ) (hpq : p + 1 = q) :
    (inr φ).1.v p q hpq ≫ (fst φ).f q = 0 := by
  simp [inr, fst, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ hpq]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCocone.inr_v_snd_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex.mappingCocone`。
形式化陈述：inr_v_snd_v (p q : Int) (hpq : p + 1 = q) : (inr φ).1.v p q hpq ≫ (snd φ).
v q p (by lia) = 𝟙 _
参数：p q : Int；hpq : p + 1 = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.rightShift_coe`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {K 
L : CochainComplex C ℤ} {n : ℤ} (γ : C…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CochainComplex.HomComplex.Cocycle.ofHom_coe`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : C
ochainComplex C ℤ} (φ : F ⟶ G),  …
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Int.ediv_self`：∀ {a : ℤ}, a ≠ 0 → a / a = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Int.negOnePow_even`：negOnePow_even (n : Int) (hn : Even n) : n.negOnePow
 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用引理 `CochainComplex.mappingCone.inr_f_snd_v`：inr_f_snd_v (p : Int) : (inr φ).
f p ≫ (snd φ).v p p (add_zero p) = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_v_snd_v (p q : ℤ) (hpq : p + 1 = q) :
    (inr φ).1.v p q hpq ≫ (snd φ).v q p (by lia) = 𝟙 _ := by
  simp [inr, snd, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.mappingCocone.id_X** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.ma
ppingCocone`。
形式化陈述：id_X (p q : Int) (hpq : p + -1 = q) : (fst φ).f p ≫ (inl φ).v p p (add_zer
o p) + (snd φ).v p q hpq ≫ (inr φ).1.v q p (by lia) = 𝟙 _
参数：p q : Int；hpq : p + -1 = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.homOf_f`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} (z : CochainCo…
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.leftShift_coe`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {K L
 : CochainComplex C ℤ} {n : ℤ} (γ : C…
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Int.ediv_self`：∀ {a : ℤ}, a ≠ 0 → a / a = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Units.neg_smul`：Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u
 : Rˣ) (x : M) : -u • x = -(u • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Int.negOnePow_even`：negOnePow_even (n : Int) (hn : Even n) : n.negOnePow
 = 1
· 使用定理 `CochainComplex.HomComplex.Cocycle.rightShift_coe`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {K 
L : CochainComplex C ℤ} {n : ℤ} (γ : C…
（共 36 条，此处仅展示前 30 条）
-/
lemma id_X (p q : ℤ) (hpq : p + -1 = q) :
    (fst φ).f p ≫ (inl φ).v p p (add_zero p) +
      (snd φ).v p q hpq ≫ (inr φ).1.v q p (by lia) = 𝟙 _ := by
  obtain rfl : q = p + -1 := by lia
  simp [fst, inl, snd, inr, mappingCocone,
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ hpq,
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Int.negOnePow_even 2 ⟨1, rfl⟩,
    mappingCone.id_X φ (p + -1) p (by lia)]

section

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain K M m) (β : Cochain L M n) (h : m + 1 = n)

/-- Constructor for cochains from `mappingCocone`. -/
/-
**CochainComplex.mappingCocone.descCochain** 是 Mathlib 中的一个定义，位于命名空间 `CochainCom
plex.mappingCocone`。
形式化陈述：descCochain : Cochain (mappingCocone φ) M m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for cochains from `mappingCocone`.
-/
noncomputable def descCochain : Cochain (mappingCocone φ) M m :=
  (-m + 1).negOnePow • (mappingCone.descCochain φ α β h).leftShift (-1) m (by lia)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCocone.inl_v_descCochain_v** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.mappingCocone`。
形式化陈述：inl_v_descCochain_v (p q : Int) (hpq : p + m = q) : (inl φ).v p p (add_zer
o _) ≫ (descCochain φ α β h).v p q hpq = α.v p q hpq
参数：p q : Int；hpq : p + m = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Int.ediv_self`：∀ {a : ℤ}, a ≠ 0 → a / a = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Int.units_mul_self`：units_mul_self (u : Intˣ) : u * u = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `CochainComplex.mappingCone.inl_v_descCochain_v`：inl_v_descCochain_v (p₁ 
p₂ p₃ : Int) (h₁₂ : p₁ + (-1) = p₂) (h₂₃ : p₂ + n = p₃) : (inl φ).v p₁ p₂ h₁₂ ≫ 
(descCochain φ α β h).v p₂ p₃ h₂₃ = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_v_descCochain_v (p q : ℤ) (hpq : p + m = q) :
    (inl φ).v p p (add_zero _) ≫ (descCochain φ α β h).v p q hpq = α.v p q hpq := by
  simp [inl, descCochain, mappingCocone,
    Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia), smul_smul,
    Cochain.leftShift_v (n := n) _ (-1) m (by lia) _ _ hpq (p + -1) (by lia)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCocone.inr_v_descCochain_v** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.mappingCocone`。
形式化陈述：inr_v_descCochain_v (p q : Int) (hpq : p + 1 = q) (r : Int) (hr : q + m = 
r) : (inr φ).1.v p q hpq ≫ (descCochain φ α β h).v q r hr = β.v p r (by lia)
参数：p q : Int；hpq : p + 1 = q；r : Int；hr : q + m = r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Int.ediv_self`：∀ {a : ℤ}, a ≠ 0 → a / a = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Int.units_mul_self`：units_mul_self (u : Intˣ) : u * u = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `CochainComplex.mappingCone.inr_f_descCochain_v`：inr_f_descCochain_v (p₁ 
p₂ : Int) (h₁₂ : p₁ + n = p₂) : (inr φ).f p₁ ≫ (descCochain φ α β h).v p₁ p₂ h₁₂
 = β.v p₁ p₂ h₁₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma inr_v_descCochain_v (p q : ℤ) (hpq : p + 1 = q) (r : ℤ) (hr : q + m = r) :
    (inr φ).1.v p q hpq ≫ (descCochain φ α β h).v q r hr = β.v p r (by lia) := by
  obtain rfl : p = q + -1 := by lia
  simp [inr, descCochain, mappingCocone, smul_smul,
    Cochain.rightShift_v _ _ _ _ _ _ hpq _ (add_zero (q + -1)),
    Cochain.leftShift_v (n := n) _ _ _ _ _ r _ (q + -1) (by lia)]

@[simp]
/-
**CochainComplex.mappingCocone.inl_comp_descCochain** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.mappingCocone`。
形式化陈述：inl_comp_descCochain : (inl φ).comp (descCochain φ α β h) (zero_add m) = α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.zero_cochain_comp_v`：zero_cochain_comp
_v (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (zero_add n)).v p q hpq = z₁.v p p…
· 使用引理 `CochainComplex.mappingCocone.inl_v_descCochain_v`：inl_v_descCochain_v (p
 q : Int) (hpq : p + m = q) : (inl φ).v p p (add_zero _) ≫ (descCochain φ α β h)
.v p q hpq = α.v p q hpq
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_comp_descCochain :
    (inl φ).comp (descCochain φ α β h) (zero_add m) = α := by
  cat_disch

@[simp]
/-
**CochainComplex.mappingCocone.inr_comp_descCochain** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.mappingCocone`。
形式化陈述：inr_comp_descCochain : (inr φ).1.comp (descCochain φ α β h) (by lia) = β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用引理 `CochainComplex.mappingCocone.inr_v_descCochain_v`：inr_v_descCochain_v (p
 q : Int) (hpq : p + 1 = q) (r : Int) (hr : q + m = r) : (inr φ).1.v p q hpq ≫ (
descCochain φ α β h).v q r hr = β.v p …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_comp_descCochain :
    (inr φ).1.comp (descCochain φ α β h) (by lia) = β := by
  ext p q hpq
  simp [Cochain.comp_v (n₂ := m) _ _ _ _ (p + 1) q rfl (by lia)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.mappingCocone.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.mappin
gCocone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_descCochain (n' : ℤ) (hn' : n + 1 = n') :
    δ m n (descCochain φ α β h) =
      (Cochain.ofHom (fst φ)).comp
        (δ m n α + m.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (zero_add n) +
      (snd φ).comp (δ n n' β) (by lia) := by
  dsimp [descCochain, fst, snd, mappingCocone]
  ext p q hpq
  subst h
  obtain rfl : n' = m + 2 := by lia
  simp [Cochain.δ_leftShift _ (-1) _ (m + 1) _ (m + 2) (by lia),
    mappingCone.δ_descCochain (m := m) (n := m + 1) _ _ _ _ (m + 2) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ p p _ (p + -1) (by lia),
    Cochain.leftShift_v (n := m + 2) _ (-1) _ _ _ q _ (p + -1) (by lia),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Cochain.comp_v (n₁ := 1) _ _ _ (p + -1) p _ (by lia) hpq,
    Cochain.comp_v (n₂ := m + 2) _ _ _ p (p + -1) q rfl (by lia),
    smul_smul, Int.negOnePow_add, Int.negOnePow_even 2 ⟨1, rfl⟩]
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  abel

end

/-- Constructor for cocycles from `mappingCocone`. -/
@[simps]
/-
**CochainComplex.mappingCocone.descCocycle** 是 Mathlib 中的一个定义，位于命名空间 `CochainCom
plex.mappingCocone`。
形式化陈述：descCocycle {M : CochainComplex C Int} {n m : Int} (α : Cochain K M m) (β 
: Cocycle L M n) (h : m + 1 = n) (hαβ : δ m n α + m.negOnePow • (Cochain.ofHom φ
).comp β.1 (zero_add n) = 0) : Cocycle (mappingCocone φ) M m
参数：α : Cochain K M m；β : Cocycle L M n；h : m + 1 = n；hαβ : δ m n α + m.negOnePow
 • (Cochain.ofHom φ).comp β.1 (zero_add n) = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for cocycles from `mappingCocone`.
-/
noncomputable def descCocycle {M : CochainComplex C ℤ} {n m : ℤ}
    (α : Cochain K M m) (β : Cocycle L M n) (h : m + 1 = n)
    (hαβ : δ m n α + m.negOnePow • (Cochain.ofHom φ).comp β.1 (zero_add n) = 0) :
    Cocycle (mappingCocone φ) M m :=
  ⟨descCochain φ α β h, by
    simp [Cocycle.mem_iff _ n h, δ_descCochain _ _ _ h (n + 1) (by lia), hαβ]⟩

section

variable {M : CochainComplex C ℤ} (α : Cochain K M 0) (β : Cocycle L M 1)
  (hαβ : δ 0 1 α + (Cochain.ofHom φ).comp β.1 (zero_add 1) = 0)

/-- Constructor for morphisms from `mappingCocone`. -/
/-
**CochainComplex.mappingCocone.desc** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.ma
ppingCocone`。
形式化陈述：desc : mappingCocone φ ⟶ M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms from `mappingCocone`.
-/
noncomputable def desc : mappingCocone φ ⟶ M :=
  (descCocycle φ α β (zero_add 1) (by simpa)).homOf

@[simp]
/-
**CochainComplex.mappingCocone.ofHom_desc** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex.mappingCocone`。
形式化陈述：ofHom_desc : Cochain.ofHom (desc φ α β hαβ) = descCochain φ α β.1 (by lia)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cocycle.cochain_ofHom_homOf_eq_coe`：cochain_of
Hom_homOf_eq_coe (z : Cocycle F G 0) : Cochain.ofHom (homOf z) = (z : Cochain F 
G 0)
· 使用定理 `CochainComplex.mappingCocone.descCocycle_coe`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {
K L : CochainComplex C ℤ} (φ : K ⟶…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofHom_desc :
    Cochain.ofHom (desc φ α β hαβ) = descCochain φ α β.1 (by lia) := by
  simp [desc]

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCocone.inl_v_desc_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainCo
mplex.mappingCocone`。
形式化陈述：inl_v_desc_f (p : Int) : (inl φ).v p p (add_zero p) ≫ (desc φ α β hαβ).f p
 = α.v p p (add_zero p)
参数：p : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.homOf_f`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} (z : CochainCo…
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.mappingCocone.descCocycle_coe`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {
K L : CochainComplex C ℤ} (φ : K ⟶…
· 使用引理 `CochainComplex.mappingCocone.inl_v_descCochain_v`：inl_v_descCochain_v (p
 q : Int) (hpq : p + m = q) : (inl φ).v p p (add_zero _) ≫ (descCochain φ α β h)
.v p q hpq = α.v p q hpq
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_v_desc_f (p : ℤ) :
    (inl φ).v p p (add_zero p) ≫ (desc φ α β hαβ).f p = α.v p p (add_zero p) := by
  simp [desc]

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCocone.inr_v_desc_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainCo
mplex.mappingCocone`。
形式化陈述：inr_v_desc_f (p q : Int) (hpq : p + 1 = q) : (inr φ).1.v p q hpq ≫ (desc φ
 α β hαβ).f q = β.1.v p q hpq
参数：p q : Int；hpq : p + 1 = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.homOf_f`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} (z : CochainCo…
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.mappingCocone.descCocycle_coe`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {
K L : CochainComplex C ℤ} (φ : K ⟶…
· 使用引理 `CochainComplex.mappingCocone.inr_v_descCochain_v`：inr_v_descCochain_v (p
 q : Int) (hpq : p + 1 = q) (r : Int) (hr : q + m = r) : (inr φ).1.v p q hpq ≫ (
descCochain φ α β h).v q r hr = β.v p …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_v_desc_f (p q : ℤ) (hpq : p + 1 = q) :
    (inr φ).1.v p q hpq ≫ (desc φ α β hαβ).f q = β.1.v p q hpq := by
  simp [desc]

end

section

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain M K n) (β : Cochain M L m) (h : m + 1 = n)

/-- Constructor for cochains to `mappingCocone`. -/
/-
**CochainComplex.mappingCocone.liftCochain** 是 Mathlib 中的一个定义，位于命名空间 `CochainCom
plex.mappingCocone`。
形式化陈述：liftCochain : Cochain M (mappingCocone φ) n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for cochains to `mappingCocone`.
-/
noncomputable def liftCochain : Cochain M (mappingCocone φ) n :=
  (mappingCone.liftCochain φ α β h).rightShift (-1) n (by lia)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCocone.liftCochain_v_fst_f** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.mappingCocone`。
形式化陈述：liftCochain_v_fst_f (p₁ p₂ : Int) (h₁₂ : p₁ + n = p₂) : (liftCochain φ α β
 h).v p₁ p₂ h₁₂ ≫ (fst φ).f p₂ = α.v p₁ p₂ h₁₂
参数：p₁ p₂ : Int；h₁₂ : p₁ + n = p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Int.ediv_self`：∀ {a : ℤ}, a ≠ 0 → a / a = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Units.neg_smul`：Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u
 : Rˣ) (x : M) : -u • x = -(u • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `CochainComplex.mappingCone.liftCochain_v_fst_v`：liftCochain_v_fst_v (p₁ 
p₂ p₃ : Int) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + 1 = p₃) : (liftCochain φ α β h).v p
₁ p₂ h₁₂ ≫ (fst φ).1.v p₂ p₃ h₂₃ = α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftCochain_v_fst_f (p₁ p₂ : ℤ) (h₁₂ : p₁ + n = p₂) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (fst φ).f p₂ = α.v p₁ p₂ h₁₂ := by
  simp [liftCochain, mappingCocone, fst,
    Cochain.rightShift_v (n := m) _ _ _ _ p₁ _ _ (p₂ + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p₂ _ (p₂ + -1) (by lia)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCocone.liftCochain_v_snd_v** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.mappingCocone`。
形式化陈述：liftCochain_v_snd_v (p₁ p₂ p₃ : Int) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + -1 = 
p₃) : (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (snd φ).v p₂ p₃ h₂₃ = β.v p₁ p₃ (by li
a)
参数：p₁ p₂ p₃ : Int；h₁₂ : p₁ + n = p₂；h₂₃ : p₂ + -1 = p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Int.ediv_self`：∀ {a : ℤ}, a ≠ 0 → a / a = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Int.negOnePow_even`：negOnePow_even (n : Int) (hn : Even n) : n.negOnePow
 = 1
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `CochainComplex.mappingCone.liftCochain_v_snd_v`：liftCochain_v_snd_v (p₁ 
p₂ : Int) (h₁₂ : p₁ + n = p₂) : (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (snd φ).v p₂
 p₂ (add_zero p₂) = β.v p₁ p₂ h₁₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftCochain_v_snd_v (p₁ p₂ p₃ : ℤ) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + -1 = p₃) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (snd φ).v p₂ p₃ h₂₃ = β.v p₁ p₃ (by lia) := by
  subst h₂₃
  simp [liftCochain, mappingCocone, snd,
    Cochain.rightShift_v (n := m) _ _ _ _ p₁ _ _ (p₂ + -1) (by lia),
    Cochain.leftShift_v (n := 0) _ _ _ _ _ _ _ _ (add_zero _),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

@[simp]
/-
**CochainComplex.mappingCocone.liftCochain_comp_fst** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.mappingCocone`。
形式化陈述：liftCochain_comp_fst : (liftCochain φ α β h).comp (Cochain.ofHom (fst φ)) 
(add_zero _) = α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_zero_cochain_v`：comp_zero_cochain
_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (add_zero n)).v p q hpq = z₁.v p q…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用引理 `CochainComplex.mappingCocone.liftCochain_v_fst_f`：liftCochain_v_fst_f (p
₁ p₂ : Int) (h₁₂ : p₁ + n = p₂) : (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (fst φ).f 
p₂ = α.v p₁ p₂ h₁₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftCochain_comp_fst :
    (liftCochain φ α β h).comp (Cochain.ofHom (fst φ)) (add_zero _) = α := by
  cat_disch

@[simp]
/-
**CochainComplex.mappingCocone.liftCochain_comp_snd** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.mappingCocone`。
形式化陈述：liftCochain_comp_snd : (liftCochain φ α β h).comp (snd φ) (by lia) = β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.add_neg_cancel_right`：∀ (a b : ℤ), a + b + -b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用引理 `CochainComplex.mappingCocone.liftCochain_v_snd_v`：liftCochain_v_snd_v (p
₁ p₂ p₃ : Int) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + -1 = p₃) : (liftCochain φ α β h).
v p₁ p₂ h₁₂ ≫ (snd φ).v p₂ p₃ h₂₃ = β.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftCochain_comp_snd :
    (liftCochain φ α β h).comp (snd φ) (by lia) = β := by
  ext p q hpq
  simp [Cochain.comp_v (n₁ := n) (n₂ := -1) (n₁₂ := m) _ _ _ p _ _ (by lia)
    (Int.add_neg_cancel_right q 1)]

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.mappingCocone.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.mappin
gCocone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_liftCochain (n' : ℤ) (hn' : n + 1 = n') :
    δ n n' (liftCochain φ α β h) =
      (δ n n' α).comp (inl φ) (add_zero _) -
        (δ m n β + α.comp (Cochain.ofHom φ) (add_zero n)).comp (inr φ).1 hn' := by
  dsimp [liftCochain, inl, inr]
  ext p q hpq
  simp [mappingCone.δ_liftCochain _ _ _ _ n' hn',
    Cochain.δ_rightShift _ (-1) _ n' _ n (by lia),
    Cochain.rightShift_v (n := n) _ _ _ _ p _ _ (q + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ (q + -1) rfl,
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero (q + -1)),
    Cochain.comp_v _ _ _ p q _ hpq rfl,
    Cochain.comp_v (n₁ := n) (n₂ := 1) _ _ _ p (q + -1) q (by lia) (by lia)]
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  abel

end

/-- Constructor for cocycles to `mappingCocone`. -/
@[simps]
/-
**CochainComplex.mappingCocone.liftCocycle** 是 Mathlib 中的一个定义，位于命名空间 `CochainCom
plex.mappingCocone`。
形式化陈述：liftCocycle {M : CochainComplex C Int} {n m : Int} (α : Cocycle M K n) (β 
: Cochain M L m) (h : m + 1 = n) (hαβ : δ m n β + α.1.comp (Cochain.ofHom φ) (ad
d_zero n) = 0) : Cocycle M (mappingCocone φ) n
参数：α : Cocycle M K n；β : Cochain M L m；h : m + 1 = n；hαβ : δ m n β + α.1.comp (C
ochain.ofHom φ) (add_zero n) = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for cocycles to `mappingCocone`.
-/
noncomputable def liftCocycle {M : CochainComplex C ℤ} {n m : ℤ}
    (α : Cocycle M K n) (β : Cochain M L m) (h : m + 1 = n)
    (hαβ : δ m n β + α.1.comp (Cochain.ofHom φ) (add_zero n) = 0) :
    Cocycle M (mappingCocone φ) n :=
  ⟨liftCochain φ α β h,
    by simp [Cocycle.mem_iff _ _ rfl, δ_liftCochain _ _ _ _ _ rfl, hαβ]⟩

section

variable {M : CochainComplex C ℤ} (α : M ⟶ K) (β : Cochain M L (-1))
  (hαβ : δ (-1) 0 β + Cochain.ofHom (α ≫ φ) = 0)

/-- Constructor for morphisms to `mappingCocone`. -/
/-
**CochainComplex.mappingCocone.lift** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.ma
ppingCocone`。
形式化陈述：lift : M ⟶ mappingCocone φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms to `mappingCocone`.
-/
noncomputable def lift : M ⟶ mappingCocone φ :=
  Cocycle.homOf (liftCocycle φ (Cocycle.ofHom α) β (by simp) (by simpa [← Cochain.ofHom_comp]))

@[simp]
/-
**CochainComplex.mappingCocone.ofHom_lift** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex.mappingCocone`。
形式化陈述：ofHom_lift : Cochain.ofHom (lift φ α β hαβ) = liftCochain φ (Cochain.ofHom
 α) β (by simp)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cocycle.cochain_ofHom_homOf_eq_coe`：cochain_of
Hom_homOf_eq_coe (z : Cocycle F G 0) : Cochain.ofHom (homOf z) = (z : Cochain F 
G 0)
· 使用定理 `CochainComplex.mappingCocone.liftCocycle_coe`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {
K L : CochainComplex C ℤ} (φ : K ⟶…
· 使用定理 `CochainComplex.HomComplex.Cocycle.ofHom_coe`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : C
ochainComplex C ℤ} (φ : F ⟶ G),  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofHom_lift :
    Cochain.ofHom (lift φ α β hαβ) = liftCochain φ (Cochain.ofHom α) β (by simp) := by
  simp [lift]

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCocone.lift_f_fst_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainCo
mplex.mappingCocone`。
形式化陈述：lift_f_fst_f (p : Int) : (lift φ α β hαβ).f p ≫ (fst φ).f p = α.f p
参数：p : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.homOf_f`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} (z : CochainCo…
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.mappingCocone.liftCocycle_coe`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {
K L : CochainComplex C ℤ} (φ : K ⟶…
· 使用定理 `CochainComplex.HomComplex.Cocycle.ofHom_coe`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : C
ochainComplex C ℤ} (φ : F ⟶ G),  …
· 使用引理 `CochainComplex.mappingCocone.liftCochain_v_fst_f`：liftCochain_v_fst_f (p
₁ p₂ : Int) (h₁₂ : p₁ + n = p₂) : (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (fst φ).f 
p₂ = α.v p₁ p₂ h₁₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_f_fst_f (p : ℤ) :
    (lift φ α β hαβ).f p ≫ (fst φ).f p = α.f p := by
  simp [lift]

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCocone.lift_fst** 是 Mathlib 中的一个引理，位于命名空间 `CochainComple
x.mappingCocone`。
形式化陈述：lift_fst : lift φ α β hαβ ≫ fst φ = α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.mappingCocone.lift_f_fst_f`：lift_f_fst_f (p : Int) : (lif
t φ α β hαβ).f p ≫ (fst φ).f p = α.f p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_fst :
    lift φ α β hαβ ≫ fst φ = α := by
  cat_disch

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCocone.lift_f_snd_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainCo
mplex.mappingCocone`。
形式化陈述：lift_f_snd_v (p q : Int) (hpq : p + (-1) = q) : (lift φ α β hαβ).f p ≫ (sn
d φ).v p q hpq = β.v p q hpq
参数：p q : Int；hpq : p + (-1) = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.homOf_f`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} (z : CochainCo…
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.mappingCocone.liftCocycle_coe`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {
K L : CochainComplex C ℤ} (φ : K ⟶…
· 使用定理 `CochainComplex.HomComplex.Cocycle.ofHom_coe`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : C
ochainComplex C ℤ} (φ : F ⟶ G),  …
· 使用引理 `CochainComplex.mappingCocone.liftCochain_v_snd_v`：liftCochain_v_snd_v (p
₁ p₂ p₃ : Int) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + -1 = p₃) : (liftCochain φ α β h).
v p₁ p₂ h₁₂ ≫ (snd φ).v p₂ p₃ h₂₃ = β.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_f_snd_v (p q : ℤ) (hpq : p + (-1) = q) :
    (lift φ α β hαβ).f p ≫ (snd φ).v p q hpq = β.v p q hpq := by
  simp [lift]

end

end

section

variable [HasBinaryBiproducts C]

/-- Given a morphism `φ : K ⟶ L` of cochain complexes, this is the triangle
`mappingCocone φ ⟶ K ⟶ L ⟶ ...`. -/
@[simps! obj₁ obj₂ obj₃ mor₁ mor₂]
/-
**CochainComplex.mappingCocone.triangle** 是 Mathlib 中的一个定义，位于命名空间 `CochainComple
x.mappingCocone`。
形式化陈述：triangle : Triangle (CochainComplex C Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `φ : K ⟶ L` of cochain complexes, this is the triangle
`mappingCocone φ ⟶ K ⟶ L ⟶ ...`.
-/
noncomputable def triangle : Triangle (CochainComplex C ℤ) :=
  Triangle.mk (fst φ) φ
    ((mappingCone.triangle φ).mor₂ ≫ (shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by lia)).inv.app _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Rotating the triangle `mappingCocone.triangle φ` gives a triangle that is
isomorphic to `mappingCone.triangle φ`. -/
/-
**CochainComplex.mappingCocone.rotateTriangleIso** 是 Mathlib 中的一个定义，位于命名空间 `Coch
ainComplex.mappingCocone`。
形式化陈述：rotateTriangleIso : (triangle φ).rotate ≅ mappingCone.triangle φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rotating the triangle `mappingCocone.triangle φ` gives a triangle that is
isomorphic to `mappingCone.triangle φ`.
-/
noncomputable def rotateTriangleIso :
    (triangle φ).rotate ≅ mappingCone.triangle φ := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by lia)).app _)
    (by simp) (by simp [triangle]) ?_
  dsimp
  ext n
  simp [fst, mappingCone.triangle, Cochain.leftShift_v _ _ _ _ _ _ _ _ rfl,
    Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
    shiftFunctorCompIsoId, shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f]

end

end mappingCocone

end CochainComplex

