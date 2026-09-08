/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Tactic.Linarith

/-! # The mapping cone of a morphism of cochain complexes

In this file, we study the homotopy cofiber `HomologicalComplex.homotopyCofiber`
of a morphism `φ : F ⟶ G` of cochain complexes indexed by `ℤ`. In this case,
we redefine it as `CochainComplex.mappingCone φ`. The API involves definitions
- `mappingCone.inl φ : Cochain F (mappingCone φ) (-1)`,
- `mappingCone.inr φ : G ⟶ mappingCone φ`,
- `mappingCone.fst φ : Cocycle (mappingCone φ) F 1` and
- `mappingCone.snd φ : Cochain (mappingCone φ) G 0`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Limits

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

universe v v'

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

namespace CochainComplex

open HomologicalComplex

section

variable {ι : Type*} [AddRightCancelSemigroup ι] [One ι]
    {F G : CochainComplex C ι} (φ : F ⟶ G)

/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ p, HasBinaryBiproduct (F.X (p + 1)) (G.X p)] :
    HasHomotopyCofiber φ where
  hasBinaryBiproduct := by
    rintro i _ rfl
    infer_instance

end

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)
variable [HasHomotopyCofiber φ]

/-- The mapping cone of a morphism of cochain complexes indexed by `ℤ`. -/
/-
**CochainComplex.mappingCone** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：mappingCone : CochainComplex C Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The mapping cone of a morphism of cochain complexes indexed by `ℤ`.
-/
noncomputable def mappingCone : CochainComplex C ℤ := homotopyCofiber φ

namespace mappingCone

open HomComplex

@[simp]
/-
**CochainComplex.mappingCone.isZero_X_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex.mappingCone`。
形式化陈述：isZero_X_iff (i : Int) : IsZero ((mappingCone φ).X i) ↔ IsZero (F.X (i + 1
)) ∧ IsZero (G.X i)
参数：i : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadd
itive C} {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Limits.biprod_isZero_iff`：biprod_isZero_iff (A B : C) [Ha
sBinaryBiproduct A B] : IsZero (biprod A B) ↔ IsZero A ∧ IsZero B
· 使用定理 `CategoryTheory.Iso.isZero_iff`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (e : X ≅ Y),   CategoryTheory.Limits.IsZero X ↔ Catego
ryTheory.Limits.IsZ…
-/
lemma isZero_X_iff (i : ℤ) :
    IsZero ((mappingCone φ).X i) ↔ IsZero (F.X (i + 1)) ∧ IsZero (G.X i) := by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ i (i + 1) rfl
  rw [← biprod_isZero_iff]
  exact (homotopyCofiber.XIsoBiprod φ i (i + 1) rfl).isZero_iff

set_option backward.defeqAttrib.useBackward true in
/-- The left inclusion in the mapping cone, as a cochain of degree `-1`. -/
/-
**CochainComplex.mappingCone.inl** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.mappi
ngCone`。
形式化陈述：inl : Cochain F (mappingCone φ) (-1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left inclusion in the mapping cone, as a cochain of degree `-1`.
-/
noncomputable def inl : Cochain F (mappingCone φ) (-1) :=
  Cochain.mk (fun p q hpq => homotopyCofiber.inlX φ p q (by dsimp; lia))

/-- The right inclusion in the mapping cone. -/
/-
**CochainComplex.mappingCone.inr** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.mappi
ngCone`。
形式化陈述：inr : G ⟶ mappingCone φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right inclusion in the mapping cone.
-/
noncomputable def inr : G ⟶ mappingCone φ := homotopyCofiber.inr φ

set_option backward.isDefEq.respectTransparency false in
/-- The first projection from the mapping cone, as a cocycle of degree `1`. -/
/-
**CochainComplex.mappingCone.fst** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.mappi
ngCone`。
形式化陈述：fst : Cocycle (mappingCone φ) F 1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection from the mapping cone, as a cocycle of degree `1`.
-/
noncomputable def fst : Cocycle (mappingCone φ) F 1 :=
  Cocycle.mk (Cochain.mk (fun p q hpq => homotopyCofiber.fstX φ p q hpq)) 2 (by lia) (by
    ext p _ rfl
    simp [δ_v 1 2 (by lia) _ p (p + 2) (by lia) (p + 1) (p + 1) (by lia) rfl,
      homotopyCofiber.d_fstX φ p (p + 1) (p + 2) rfl, mappingCone,
      show Int.negOnePow 2 = 1 by rfl])

/-- The second projection from the mapping cone, as a cochain of degree `0`. -/
/-
**CochainComplex.mappingCone.snd** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.mappi
ngCone`。
形式化陈述：snd : Cochain (mappingCone φ) G 0
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection from the mapping cone, as a cochain of degree `0`.
-/
noncomputable def snd : Cochain (mappingCone φ) G 0 :=
  Cochain.ofHoms (homotopyCofiber.sndX φ)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.inl_v_fst_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainCompl
ex.mappingCone`。
形式化陈述：inl_v_fst_v (p q : Int) (hpq : q + 1 = p) : (inl φ).v p q (by rw [← hpq, a
dd_neg_cancel_right]) ≫ (fst φ : Cochain (mappingCone φ) F 1).v q p hpq = 𝟙 _
参数：p q : Int；hpq : q + 1 = p。
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
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.mk_coe`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coch
ainComplex C ℤ} {n : ℤ} (z : C…
· 使用引理 `HomologicalComplex.homotopyCofiber.inlX_fstX`：inlX_fstX (i j : ι) (hij :
 c.Rel j i) : inlX φ i j hij ≫ fstX φ j i hij = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_v_fst_v (p q : ℤ) (hpq : q + 1 = p) :
    (inl φ).v p q (by rw [← hpq, add_neg_cancel_right]) ≫
      (fst φ : Cochain (mappingCone φ) F 1).v q p hpq = 𝟙 _ := by
  simp [inl, fst]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.inl_v_snd_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainCompl
ex.mappingCone`。
形式化陈述：inl_v_snd_v (p q : Int) (hpq : p + (-1) = q) : (inl φ).v p q hpq ≫ (snd φ)
.v q q (add_zero q) = 0
参数：p q : Int；hpq : p + (-1) = q。
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
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHoms_v`：ofHoms_v (ψ : forall (p : In
t), F.X p ⟶ G.X p) (p : Int) : (ofHoms ψ).v p p (add_zero p) = ψ p
· 使用引理 `HomologicalComplex.homotopyCofiber.inlX_sndX`：inlX_sndX (i j : ι) (hij :
 c.Rel j i) : inlX φ i j hij ≫ sndX φ j = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_v_snd_v (p q : ℤ) (hpq : p + (-1) = q) :
    (inl φ).v p q hpq ≫ (snd φ).v q q (add_zero q) = 0 := by
  simp [inl, snd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.inr_f_fst_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainCompl
ex.mappingCone`。
形式化陈述：inr_f_fst_v (p q : Int) (hpq : p + 1 = q) : (inr φ).f p ≫ (fst φ).1.v p q 
hpq = 0
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HomologicalComplex.homotopyCofiber.inr_f`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] {ι : Ty
pe u_2}   {c : ComplexShape ι}…
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.mk_coe`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coch
ainComplex C ℤ} {n : ℤ} (z : C…
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_fstX`：inrX_fstX (i j : ι) (hij :
 c.Rel i j) : inrX φ i ≫ fstX φ i j hij = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_f_fst_v (p q : ℤ) (hpq : p + 1 = q) :
    (inr φ).f p ≫ (fst φ).1.v p q hpq = 0 := by
  simp [inr, fst]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.inr_f_snd_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainCompl
ex.mappingCone`。
形式化陈述：inr_f_snd_v (p : Int) : (inr φ).f p ≫ (snd φ).v p p (add_zero p) = 𝟙 _
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
· 使用定理 `HomologicalComplex.homotopyCofiber.inr_f`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] {ι : Ty
pe u_2}   {c : ComplexShape ι}…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHoms_v`：ofHoms_v (ψ : forall (p : In
t), F.X p ⟶ G.X p) (p : Int) : (ofHoms ψ).v p p (add_zero p) = ψ p
· 使用引理 `HomologicalComplex.homotopyCofiber.inrX_sndX`：inrX_sndX (i : ι) : inrX φ
 i ≫ sndX φ i = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_f_snd_v (p : ℤ) :
    (inr φ).f p ≫ (snd φ).v p p (add_zero p) = 𝟙 _ := by
  simp [inr, snd]

@[simp]
/-
**CochainComplex.mappingCone.inl_fst** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.m
appingCone`。
形式化陈述：inl_fst : (inl φ).comp (fst φ).1 (neg_add_cancel 1) = Cochain.ofHom (𝟙 F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.ext₀`：ext₀ (z₁ z₂ : Cochain F G 0) (h 
: forall (p : Int), z₁.v p p (add_zero p) = z₂.v p p (add_zero p)) : z₁ = z₂
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用引理 `CochainComplex.mappingCone.inl_v_fst_v`：inl_v_fst_v (p q : Int) (hpq : q
 + 1 = p) : (inl φ).v p q (by rw [← hpq, add_neg_cancel_right]) ≫ (fst φ : Cocha
in (mappingCone φ) F 1).v q …
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_fst :
    (inl φ).comp (fst φ).1 (neg_add_cancel 1) = Cochain.ofHom (𝟙 F) := by
  ext p
  simp [Cochain.comp_v _ _ (neg_add_cancel 1) p (p - 1) p rfl (by lia)]

@[simp]
/-
**CochainComplex.mappingCone.inl_snd** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.m
appingCone`。
形式化陈述：inl_snd : (inl φ).comp (snd φ) (add_zero (-1)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_zero_cochain_v`：comp_zero_cochain
_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (add_zero n)).v p q hpq = z₁.v p q…
· 使用引理 `CochainComplex.mappingCone.inl_v_snd_v`：inl_v_snd_v (p q : Int) (hpq : p
 + (-1) = q) : (inl φ).v p q hpq ≫ (snd φ).v q q (add_zero q) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_snd :
    (inl φ).comp (snd φ) (add_zero (-1)) = 0 := by
  ext
  simp

@[simp]
/-
**CochainComplex.mappingCone.inr_fst** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.m
appingCone`。
形式化陈述：inr_fst : (Cochain.ofHom (inr φ)).comp (fst φ).1 (zero_add 1) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
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
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用引理 `CochainComplex.mappingCone.inr_f_fst_v`：inr_f_fst_v (p q : Int) (hpq : p
 + 1 = q) : (inr φ).f p ≫ (fst φ).1.v p q hpq = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_fst :
    (Cochain.ofHom (inr φ)).comp (fst φ).1 (zero_add 1) = 0 := by
  ext
  simp

@[simp]
/-
**CochainComplex.mappingCone.inr_snd** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.m
appingCone`。
形式化陈述：inr_snd : (Cochain.ofHom (inr φ)).comp (snd φ) (zero_add 0) = Cochain.ofHo
m (𝟙 G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.ext₀`：ext₀ (z₁ z₂ : Cochain F G 0) (h 
: forall (p : Int), z₁.v p p (add_zero p) = z₂.v p p (add_zero p)) : z₁ = z₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_zero_cochain_v`：comp_zero_cochain
_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (add_zero n)).v p q hpq = z₁.v p q…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用引理 `CochainComplex.mappingCone.inr_f_snd_v`：inr_f_snd_v (p : Int) : (inr φ).
f p ≫ (snd φ).v p p (add_zero p) = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_snd :
    (Cochain.ofHom (inr φ)).comp (snd φ) (zero_add 0) = Cochain.ofHom (𝟙 G) := by cat_disch

/-! In order to obtain identities of cochains involving `inl`, `inr`, `fst` and `snd`,
it is often convenient to use an `ext` lemma, and use simp lemmas like `inl_v_f_fst_v`,
but it is sometimes possible to get identities of cochains by using rewrites of
identities of cochains like `inl_fst`. Then, similarly as in category theory,
if we associate the compositions of cochains to the right as much as possible,
it is also interesting to have `reassoc` variants of lemmas, like `inl_fst_assoc`. -/

@[simp]
/-
**CochainComplex.mappingCone.inl_fst_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex.mappingCone`。
形式化陈述：inl_fst_assoc {K : CochainComplex C Int} {d e : Int} (γ : Cochain F K d) (
he : 1 + d = e) : (inl φ).comp ((fst φ).1.comp γ he) (by rw [← he, neg_add_cance
l_left]) = γ
参数：γ : Cochain F K d；he : 1 + d = e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_assoc`：comp_assoc {n₁ n₂ n₃ n₁₂ n
₂₃ n₁₂₃ : Int} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (z₃ : Cochain K L n₃)
 (h₁₂ : n₁ + n₂ = n₁₂) (h₂₃ : n₂ +…
· 使用引理 `CochainComplex.mappingCone.inl_fst`：inl_fst : (inl φ).comp (fst φ).1 (ne
g_add_cancel 1) = Cochain.ofHom (𝟙 F)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CochainComplex.HomComplex.Cochain.id_comp`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} {n : ℤ} (z₂ : …

--- 原说明 ---
In order to obtain identities of cochains involving `inl`, `inr`, `fst` and `snd
`,
it is often convenient to use an `ext` lemma, and use simp lemmas like `inl_v_f_
fst_v`,
but it is sometimes possible to get identities of cochains by using rewrites of
identities of cochains like `inl_fst`. Then, similarly as in category theory,
if we associate the compositions of cochains to the right as much as possible,
it is also interesting to have `reassoc` variants of lemmas, like `inl_fst_assoc
`.
-/
lemma inl_fst_assoc {K : CochainComplex C ℤ} {d e : ℤ} (γ : Cochain F K d) (he : 1 + d = e) :
    (inl φ).comp ((fst φ).1.comp γ he) (by rw [← he, neg_add_cancel_left]) = γ := by
  rw [← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (by lia) (by lia), inl_fst,
    Cochain.id_comp]

@[simp]
/-
**CochainComplex.mappingCone.inl_snd_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex.mappingCone`。
形式化陈述：inl_snd_assoc {K : CochainComplex C Int} {d e f : Int} (γ : Cochain G K d)
 (he : 0 + d = e) (hf : -1 + e = f) : (inl φ).comp ((snd φ).comp γ he) hf = 0
参数：γ : Cochain G K d；he : 0 + d = e；hf : -1 + e = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain`：
comp_assoc_of_second_is_zero_cochain {n₁ n₃ n₁₃ : Int} (z₁ : Cochain F G n₁) (z₂
 : Cochain G K 0) (z₃ : Cochain K L n₃) (h₁₃ : n₁ + n₃ = n₁₃…
· 使用引理 `CochainComplex.mappingCone.inl_snd`：inl_snd : (inl φ).comp (snd φ) (add_
zero (-1)) = 0
· 使用定理 `CochainComplex.HomComplex.Cochain.zero_comp`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G K :
 CochainComplex C ℤ} {n₁ n₂ n₁₂ :…
-/
lemma inl_snd_assoc {K : CochainComplex C ℤ} {d e f : ℤ} (γ : Cochain G K d)
    (he : 0 + d = e) (hf : -1 + e = f) :
    (inl φ).comp ((snd φ).comp γ he) hf = 0 := by
  obtain rfl : e = d := by lia
  rw [← Cochain.comp_assoc_of_second_is_zero_cochain, inl_snd, Cochain.zero_comp]

@[simp]
/-
**CochainComplex.mappingCone.inr_fst_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex.mappingCone`。
形式化陈述：inr_fst_assoc {K : CochainComplex C Int} {d e f : Int} (γ : Cochain F K d)
 (he : 1 + d = e) (hf : 0 + e = f) : (Cochain.ofHom (inr φ)).comp ((fst φ).1.com
p γ he) hf = 0
参数：γ : Cochain F K d；he : 1 + d = e；hf : 0 + e = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain`：c
omp_assoc_of_first_is_zero_cochain {n₂ n₃ n₂₃ : Int} (z₁ : Cochain F G 0) (z₂ : 
Cochain G K n₂) (z₃ : Cochain K L n₃) (h₂₃ : n₂ + n₃ = n₂₃)…
· 使用引理 `CochainComplex.mappingCone.inr_fst`：inr_fst : (Cochain.ofHom (inr φ)).co
mp (fst φ).1 (zero_add 1) = 0
· 使用定理 `CochainComplex.HomComplex.Cochain.zero_comp`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G K :
 CochainComplex C ℤ} {n₁ n₂ n₁₂ :…
-/
lemma inr_fst_assoc {K : CochainComplex C ℤ} {d e f : ℤ} (γ : Cochain F K d)
    (he : 1 + d = e) (hf : 0 + e = f) :
    (Cochain.ofHom (inr φ)).comp ((fst φ).1.comp γ he) hf = 0 := by
  obtain rfl : e = f := by lia
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, inr_fst, Cochain.zero_comp]

@[simp]
/-
**CochainComplex.mappingCone.inr_snd_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex.mappingCone`。
形式化陈述：inr_snd_assoc {K : CochainComplex C Int} {d e : Int} (γ : Cochain G K d) (
he : 0 + d = e) : (Cochain.ofHom (inr φ)).comp ((snd φ).comp γ he) (by simp only
 [← he, zero_add]) = γ
参数：γ : Cochain G K d；he : 0 + d = e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain`：c
omp_assoc_of_first_is_zero_cochain {n₂ n₃ n₂₃ : Int} (z₁ : Cochain F G 0) (z₂ : 
Cochain G K n₂) (z₃ : Cochain K L n₃) (h₂₃ : n₂ + n₃ = n₂₃)…
· 使用引理 `CochainComplex.mappingCone.inr_snd`：inr_snd : (Cochain.ofHom (inr φ)).co
mp (snd φ) (zero_add 0) = Cochain.ofHom (𝟙 G)
· 使用定理 `CochainComplex.HomComplex.Cochain.id_comp`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} {n : ℤ} (z₂ : …
-/
lemma inr_snd_assoc {K : CochainComplex C ℤ} {d e : ℤ} (γ : Cochain G K d) (he : 0 + d = e) :
    (Cochain.ofHom (inr φ)).comp ((snd φ).comp γ he) (by simp only [← he, zero_add]) = γ := by
  obtain rfl : d = e := by lia
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, inr_snd, Cochain.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CochainComplex.mappingCone.ext_to** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.ma
ppingCone`。
形式化陈述：ext_to (i j : Int) (hij : i + 1 = j) {A : C} {f g : A ⟶ (mappingCone φ).X 
i} (h₁ : f ≫ (fst φ).1.v i j hij = g ≫ (fst φ).1.v i j hij) (h₂ : f ≫ (snd φ).v 
i i (add_zero i) = g ≫ (snd φ).v i i (add_zero i)) : f = g
参数：i j : Int；hij : i + 1 = j；mappingCone φ；h₁ : f ≫ (fst φ).1.v i j hij = g ≫ (f
st φ).1.v i j hij；h₂ : f ≫ (snd φ).v i i (add_zero i) = g ≫ (snd φ).v i i (add_z
ero i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `HomologicalComplex.homotopyCofiber.ext_to_X`：ext_to_X (i j : ι) (hij : c
.Rel i j) {A : C} {f g : A ⟶ X φ i} (h₁ : f ≫ fstX φ i j hij = g ≫ fstX φ i j hi
j) (h₂ : f ≫ sndX φ i = g ≫ sndX …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHoms_v`：ofHoms_v (ψ : forall (p : In
t), F.X p ⟶ G.X p) (p : Int) : (ofHoms ψ).v p p (add_zero p) = ψ p
-/
lemma ext_to (i j : ℤ) (hij : i + 1 = j) {A : C} {f g : A ⟶ (mappingCone φ).X i}
    (h₁ : f ≫ (fst φ).1.v i j hij = g ≫ (fst φ).1.v i j hij)
    (h₂ : f ≫ (snd φ).v i i (add_zero i) = g ≫ (snd φ).v i i (add_zero i)) :
    f = g :=
  homotopyCofiber.ext_to_X φ i j hij h₁ (by simpa [snd] using! h₂)
/-
**CochainComplex.mappingCone.ext_to_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainComple
x.mappingCone`。
形式化陈述：ext_to_iff (i j : Int) (hij : i + 1 = j) {A : C} (f g : A ⟶ (mappingCone φ
).X i) : f = g ↔ f ≫ (fst φ).1.v i j hij = g ≫ (fst φ).1.v i j hij ∧ f ≫ (snd φ)
.v i i (add_zero i) = g ≫ (snd φ).v i i (add_zero i)
参数：i j : Int；hij : i + 1 = j；f g : A ⟶ (mappingCone φ).X i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.mappingCone.ext_to`：ext_to (i j : Int) (hij : i + 1 = j) 
{A : C} {f g : A ⟶ (mappingCone φ).X i} (h₁ : f ≫ (fst φ).1.v i j hij = g ≫ (fst
 φ).1.v i j hij) (h₂ : …
-/
lemma ext_to_iff (i j : ℤ) (hij : i + 1 = j) {A : C} (f g : A ⟶ (mappingCone φ).X i) :
    f = g ↔ f ≫ (fst φ).1.v i j hij = g ≫ (fst φ).1.v i j hij ∧
      f ≫ (snd φ).v i i (add_zero i) = g ≫ (snd φ).v i i (add_zero i) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact ext_to φ i j hij h₁ h₂
/-
**CochainComplex.mappingCone.ext_from** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.
mappingCone`。
形式化陈述：ext_from (i j : Int) (hij : j + 1 = i) {A : C} {f g : (mappingCone φ).X j 
⟶ A} (h₁ : (inl φ).v i j (by lia) ≫ f = (inl φ).v i j (by lia) ≫ g) (h₂ : (inr φ
).f j ≫ f = (inr φ).f j ≫ g) : f = g
参数：i j : Int；hij : j + 1 = i；mappingCone φ；h₁ : (inl φ).v i j (by lia) ≫ f = (in
l φ).v i j (by lia) ≫ g；h₂ : (inr φ).f j ≫ f = (inr φ).f j ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.homotopyCofiber.ext_from_X`：ext_from_X (i j : ι) (hij
 : c.Rel j i) {A : C} {f g : X φ j ⟶ A} (h₁ : inlX φ i j hij ≫ f = inlX φ i j hi
j ≫ g) (h₂ : inrX φ j ≫ f = inrX φ …
-/
lemma ext_from (i j : ℤ) (hij : j + 1 = i) {A : C} {f g : (mappingCone φ).X j ⟶ A}
    (h₁ : (inl φ).v i j (by lia) ≫ f = (inl φ).v i j (by lia) ≫ g)
    (h₂ : (inr φ).f j ≫ f = (inr φ).f j ≫ g) :
    f = g :=
  homotopyCofiber.ext_from_X φ i j hij h₁ h₂
/-
**CochainComplex.mappingCone.ext_from_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex.mappingCone`。
形式化陈述：ext_from_iff (i j : Int) (hij : j + 1 = i) {A : C} (f g : (mappingCone φ).
X j ⟶ A) : f = g ↔ (inl φ).v i j (by lia) ≫ f = (inl φ).v i j (by lia) ≫ g ∧ (in
r φ).f j ≫ f = (inr φ).f j ≫ g
参数：i j : Int；hij : j + 1 = i；f g : (mappingCone φ).X j ⟶ A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.mappingCone.ext_from`：ext_from (i j : Int) (hij : j + 1 =
 i) {A : C} {f g : (mappingCone φ).X j ⟶ A} (h₁ : (inl φ).v i j (by lia) ≫ f = (
inl φ).v i j (by lia) ≫ g…
-/
lemma ext_from_iff (i j : ℤ) (hij : j + 1 = i) {A : C} (f g : (mappingCone φ).X j ⟶ A) :
    f = g ↔ (inl φ).v i j (by lia) ≫ f = (inl φ).v i j (by lia) ≫ g ∧
      (inr φ).f j ≫ f = (inr φ).f j ≫ g := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact ext_from φ i j hij h₁ h₂
/-
**CochainComplex.mappingCone.decomp_to** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex
.mappingCone`。
形式化陈述：decomp_to {i : Int} {A : C} (f : A ⟶ (mappingCone φ).X i) (j : Int) (hij :
 i + 1 = j) : exists (a : A ⟶ F.X j) (b : A ⟶ G.X i), f = a ≫ (inl φ).v j i (by 
lia) + b ≫ (inr φ).f i
参数：f : A ⟶ (mappingCone φ).X i；j : Int；hij : i + 1 = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.mappingCone.ext_to`：ext_to (i j : Int) (hij : i + 1 = j) 
{A : C} {f g : A ⟶ (mappingCone φ).X i} (h₁ : f ≫ (fst φ).1.v i j hij = g ≫ (fst
 φ).1.v i j hij) (h₂ : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用引理 `CochainComplex.mappingCone.inl_v_fst_v`：inl_v_fst_v (p q : Int) (hpq : q
 + 1 = p) : (inl φ).v p q (by rw [← hpq, add_neg_cancel_right]) ≫ (fst φ : Cocha
in (mappingCone φ) F 1).v q …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CochainComplex.mappingCone.inr_f_fst_v`：inr_f_fst_v (p q : Int) (hpq : p
 + 1 = q) : (inr φ).f p ≫ (fst φ).1.v p q hpq = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.mappingCone.inl_v_snd_v`：inl_v_snd_v (p q : Int) (hpq : p
 + (-1) = q) : (inl φ).v p q hpq ≫ (snd φ).v q q (add_zero q) = 0
· 使用引理 `CochainComplex.mappingCone.inr_f_snd_v`：inr_f_snd_v (p : Int) : (inr φ).
f p ≫ (snd φ).v p p (add_zero p) = 𝟙 _
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma decomp_to {i : ℤ} {A : C} (f : A ⟶ (mappingCone φ).X i) (j : ℤ) (hij : i + 1 = j) :
    ∃ (a : A ⟶ F.X j) (b : A ⟶ G.X i), f = a ≫ (inl φ).v j i (by lia) + b ≫ (inr φ).f i :=
  ⟨f ≫ (fst φ).1.v i j hij, f ≫ (snd φ).v i i (add_zero i),
    by apply ext_to φ i j hij <;> simp⟩
/-
**CochainComplex.mappingCone.decomp_from** 是 Mathlib 中的一个引理，位于命名空间 `CochainCompl
ex.mappingCone`。
形式化陈述：decomp_from {j : Int} {A : C} (f : (mappingCone φ).X j ⟶ A) (i : Int) (hij
 : j + 1 = i) : exists (a : F.X i ⟶ A) (b : G.X j ⟶ A), f = (fst φ).1.v j i hij 
≫ a + (snd φ).v j j (add_zero j) ≫ b
参数：f : (mappingCone φ).X j ⟶ A；i : Int；hij : j + 1 = i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.mappingCone.ext_from`：ext_from (i j : Int) (hij : j + 1 =
 i) {A : C} {f g : (mappingCone φ).X j ⟶ A} (h₁ : (inl φ).v i j (by lia) ≫ f = (
inl φ).v i j (by lia) ≫ g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CochainComplex.mappingCone.inl_v_fst_v_assoc`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F 
G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `CochainComplex.mappingCone.inl_v_snd_v_assoc`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F 
G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CochainComplex.mappingCone.inr_f_fst_v_assoc`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F 
G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `CochainComplex.mappingCone.inr_f_snd_v_assoc`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F 
G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma decomp_from {j : ℤ} {A : C} (f : (mappingCone φ).X j ⟶ A) (i : ℤ) (hij : j + 1 = i) :
    ∃ (a : F.X i ⟶ A) (b : G.X j ⟶ A),
      f = (fst φ).1.v j i hij ≫ a + (snd φ).v j j (add_zero j) ≫ b :=
  ⟨(inl φ).v i j (by lia) ≫ f, (inr φ).f j ≫ f,
    by apply ext_from φ i j hij <;> simp⟩
/-
**CochainComplex.mappingCone.ext_cochain_to_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cocha
inComplex.mappingCone`。
形式化陈述：ext_cochain_to_iff (i j : Int) (hij : i + 1 = j) {K : CochainComplex C Int
} {γ₁ γ₂ : Cochain K (mappingCone φ) i} : γ₁ = γ₂ ↔ γ₁.comp (fst φ).1 hij = γ₂.c
omp (fst φ).1 hij ∧ γ₁.comp (snd φ) (add_zero i) = γ₂.comp (snd φ) (add_zero i)
参数：i j : Int；hij : i + 1 = j；mappingCone φ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.mappingCone.ext_to_iff`：ext_to_iff (i j : Int) (hij : i +
 1 = j) {A : C} (f g : A ⟶ (mappingCone φ).X i) : f = g ↔ f ≫ (fst φ).1.v i j hi
j = g ≫ (fst φ).1.v i j hij…
· 使用引理 `CochainComplex.HomComplex.Cochain.congr_v`：congr_v {z₁ z₂ : Cochain F G 
n} (h : z₁ = z₂) (p q : Int) (hpq : p + n = q) : z₁.v p q hpq = z₂.v p q hpq
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_zero_cochain_v`：comp_zero_cochain
_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (add_zero n)).v p q hpq = z₁.v p q…
-/
lemma ext_cochain_to_iff (i j : ℤ) (hij : i + 1 = j)
    {K : CochainComplex C ℤ} {γ₁ γ₂ : Cochain K (mappingCone φ) i} :
    γ₁ = γ₂ ↔ γ₁.comp (fst φ).1 hij = γ₂.comp (fst φ).1 hij ∧
      γ₁.comp (snd φ) (add_zero i) = γ₂.comp (snd φ) (add_zero i) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    rw [ext_to_iff φ q (q + 1) rfl]
    replace h₁ := Cochain.congr_v h₁ p (q + 1) (by lia)
    replace h₂ := Cochain.congr_v h₂ p q hpq
    simp only [Cochain.comp_v _ _ _ p q (q + 1) hpq rfl] at h₁
    simp only [Cochain.comp_zero_cochain_v] at h₂
    exact ⟨h₁, h₂⟩
/-
**CochainComplex.mappingCone.ext_cochain_from_iff** 是 Mathlib 中的一个引理，位于命名空间 `Coc
hainComplex.mappingCone`。
形式化陈述：ext_cochain_from_iff (i j : Int) (hij : i + 1 = j) {K : CochainComplex C I
nt} {γ₁ γ₂ : Cochain (mappingCone φ) K j} : γ₁ = γ₂ ↔ (inl φ).comp γ₁ (show _ = 
i by lia) = (inl φ).comp γ₂ (by lia) ∧ (Cochain.ofHom (inr φ)).comp γ₁ (zero_add
 j) = (Cochain.ofHom (inr φ)).comp γ₂ (zero_add j)
参数：i j : Int；hij : i + 1 = j；mappingCone φ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.mappingCone.ext_from_iff`：ext_from_iff (i j : Int) (hij :
 j + 1 = i) {A : C} (f g : (mappingCone φ).X j ⟶ A) : f = g ↔ (inl φ).v i j (by 
lia) ≫ f = (inl φ).v i j (by …
· 使用引理 `CochainComplex.HomComplex.Cochain.congr_v`：congr_v {z₁ z₂ : Cochain F G 
n} (h : z₁ = z₂) (p q : Int) (hpq : p + n = q) : z₁.v p q hpq = z₂.v p q hpq
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.zero_cochain_comp_v`：zero_cochain_comp
_v (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (zero_add n)).v p q hpq = z₁.v p p…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
-/
lemma ext_cochain_from_iff (i j : ℤ) (hij : i + 1 = j)
    {K : CochainComplex C ℤ} {γ₁ γ₂ : Cochain (mappingCone φ) K j} :
    γ₁ = γ₂ ↔
      (inl φ).comp γ₁ (show _ = i by lia) = (inl φ).comp γ₂ (by lia) ∧
        (Cochain.ofHom (inr φ)).comp γ₁ (zero_add j) =
          (Cochain.ofHom (inr φ)).comp γ₂ (zero_add j) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    rw [ext_from_iff φ (p + 1) p rfl]
    replace h₁ := Cochain.congr_v h₁ (p + 1) q (by lia)
    replace h₂ := Cochain.congr_v h₂ p q (by lia)
    simp only [Cochain.comp_v (inl φ) _ _ (p + 1) p q (by lia) hpq] at h₁
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at h₂
    exact ⟨h₁, h₂⟩
/-
**CochainComplex.mappingCone.id** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.mappin
gCone`。
形式化陈述：id : (fst φ).1.comp (inl φ) (add_neg_cancel 1) + (snd φ).comp (Cochain.ofH
om (inr φ)) (add_zero 0) = Cochain.ofHom (𝟙 _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `CochainComplex.mappingCone.ext_cochain_from_iff`：ext_cochain_from_iff (i
 j : Int) (hij : i + 1 = j) {K : CochainComplex C Int} {γ₁ γ₂ : Cochain (mapping
Cone φ) K j} : γ₁ = γ₂ ↔ (inl φ).comp…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cochain.comp_add`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G K : 
CochainComplex C ℤ} {n₁ n₂ n₁₂ :…
· 使用引理 `CochainComplex.mappingCone.inl_fst_assoc`：inl_fst_assoc {K : CochainComp
lex C Int} {d e : Int} (γ : Cochain F K d) (he : 1 + d = e) : (inl φ).comp ((fst
 φ).1.comp γ he) (by rw [← he,…
· 使用引理 `CochainComplex.mappingCone.inl_snd_assoc`：inl_snd_assoc {K : CochainComp
lex C Int} {d e f : Int} (γ : Cochain G K d) (he : 0 + d = e) (hf : -1 + e = f) 
: (inl φ).comp ((snd φ).comp γ…
· 使用定理 `CochainComplex.HomComplex.Cochain.comp_id`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} {n : ℤ} (z₁ : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.mappingCone.inr_fst_assoc`：inr_fst_assoc {K : CochainComp
lex C Int} {d e f : Int} (γ : Cochain F K d) (he : 1 + d = e) (hf : 0 + e = f) :
 (Cochain.ofHom (inr φ)).comp …
· 使用引理 `CochainComplex.mappingCone.inr_snd_assoc`：inr_snd_assoc {K : CochainComp
lex C Int} {d e : Int} (γ : Cochain G K d) (he : 0 + d = e) : (Cochain.ofHom (in
r φ)).comp ((snd φ).comp γ he)…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma id :
    (fst φ).1.comp (inl φ) (add_neg_cancel 1) +
      (snd φ).comp (Cochain.ofHom (inr φ)) (add_zero 0) = Cochain.ofHom (𝟙 _) := by
  simp [ext_cochain_from_iff φ (-1) 0 (neg_add_cancel 1)]
/-
**CochainComplex.mappingCone.id_X** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.mapp
ingCone`。
形式化陈述：id_X (p q : Int) (hpq : p + 1 = q) : (fst φ).1.v p q hpq ≫ (inl φ).v q p (
by lia) + (snd φ).v p p (add_zero p) ≫ (inr φ).f p = 𝟙 ((mappingCone φ).X p)
参数：p q : Int；hpq : p + 1 = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_zero_cochain_v`：comp_zero_cochain
_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (add_zero n)).v p q hpq = z₁.v p q…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用引理 `CochainComplex.HomComplex.Cochain.congr_v`：congr_v {z₁ z₂ : Cochain F G 
n} (h : z₁ = z₂) (p q : Int) (hpq : p + n = q) : z₁.v p q hpq = z₂.v p q hpq
· 使用引理 `CochainComplex.mappingCone.id`：id : (fst φ).1.comp (inl φ) (add_neg_canc
el 1) + (snd φ).comp (Cochain.ofHom (inr φ)) (add_zero 0) = Cochain.ofHom (𝟙 _)
-/
lemma id_X (p q : ℤ) (hpq : p + 1 = q) :
    (fst φ).1.v p q hpq ≫ (inl φ).v q p (by lia) +
      (snd φ).v p p (add_zero p) ≫ (inr φ).f p = 𝟙 ((mappingCone φ).X p) := by
  simpa only [Cochain.add_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, id_f,
    Cochain.comp_v _ _ (add_neg_cancel 1) p q p hpq (by lia)]
    using Cochain.congr_v (id φ) p p (add_zero p)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CochainComplex.mappingCone.inl_v_d** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.m
appingCone`。
形式化陈述：inl_v_d (i j k : Int) (hij : i + (-1) = j) (hik : k + (-1) = i) : (inl φ).
v i j hij ≫ (mappingCone φ).d j i = φ.f i ≫ (inr φ).f i - F.d i k ≫ (inl φ).v _ 
_ hik
参数：i j k : Int；hij : i + (-1) = j；hik : k + (-1) = i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.homotopyCofiber.inlX_d`：inlX_d (i j k : ι) (hij : c.R
el i j) (hjk : c.Rel j k) : inlX φ j i hij ≫ d φ i j = -F.d j k ≫ inlX φ k j hjk
 + φ.f j ≫ inrX φ j
· 使用定理 `_private.Mathlib.Algebra.Homology.HomotopyCategory.MappingCone.0.Cochain
Complex.mappingCone.inl_v_d._abel_1_2`：∀ {C : Type u_2} [inst : CategoryTheory.C
ategory.{u_1, u_2} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : CochainCo
mplex C ℤ} (φ : F ⟶…
-/
lemma inl_v_d (i j k : ℤ) (hij : i + (-1) = j) (hik : k + (-1) = i) :
    (inl φ).v i j hij ≫ (mappingCone φ).d j i =
      φ.f i ≫ (inr φ).f i - F.d i k ≫ (inl φ).v _ _ hik := by
  dsimp [mappingCone, inl, inr]
  rw [homotopyCofiber.inlX_d φ j i k (by dsimp; lia) (by dsimp; lia)]
  abel

@[reassoc]
/-
**CochainComplex.mappingCone.inr_f_d** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.m
appingCone`。
形式化陈述：inr_f_d (n₁ n₂ : Int) : (inr φ).f n₁ ≫ (mappingCone φ).d n₁ n₂ = G.d n₁ n₂
 ≫ (inr φ).f n₂
参数：n₁ n₂ : Int。
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
· 使用定理 `HomologicalComplex.Hom.comm`：∀ {ι : Type u_1} {V : Type u} [inst : Categ
oryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
V] {c : ComplexSh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_f_d (n₁ n₂ : ℤ) :
    (inr φ).f n₁ ≫ (mappingCone φ).d n₁ n₂ = G.d n₁ n₂ ≫ (inr φ).f n₂ := by
  simp

@[reassoc]
/-
**CochainComplex.mappingCone.d_fst_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.m
appingCone`。
形式化陈述：d_fst_v (i j k : Int) (hij : i + 1 = j) (hjk : j + 1 = k) : (mappingCone φ
).d i j ≫ (fst φ).1.v j k hjk = -(fst φ).1.v i j hij ≫ F.d j k
参数：i j k : Int；hij : i + 1 = j；hjk : j + 1 = k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.homotopyCofiber.d_fstX`：d_fstX (i j k : ι) (hij : c.R
el i j) (hjk : c.Rel j k) : d φ i j ≫ fstX φ j k hjk = -fstX φ i j hij ≫ F.d j k
-/
lemma d_fst_v (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    (mappingCone φ).d i j ≫ (fst φ).1.v j k hjk =
      -(fst φ).1.v i j hij ≫ F.d j k := by
  apply homotopyCofiber.d_fstX

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.d_fst_v'** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.
mappingCone`。
形式化陈述：d_fst_v' (i j : Int) (hij : i + 1 = j) : (mappingCone φ).d (i - 1) i ≫ (fs
t φ).1.v i j hij = -(fst φ).1.v (i - 1) i (by lia) ≫ F.d i j
参数：i j : Int；hij : i + 1 = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.mappingCone.d_fst_v`：d_fst_v (i j k : Int) (hij : i + 1 =
 j) (hjk : j + 1 = k) : (mappingCone φ).d i j ≫ (fst φ).1.v j k hjk = -(fst φ).1
.v i j hij ≫ F.d j k
-/
lemma d_fst_v' (i j : ℤ) (hij : i + 1 = j) :
    (mappingCone φ).d (i - 1) i ≫ (fst φ).1.v i j hij =
      -(fst φ).1.v (i - 1) i (by lia) ≫ F.d i j :=
  d_fst_v φ (i - 1) i j (by lia) hij

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CochainComplex.mappingCone.d_snd_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.m
appingCone`。
形式化陈述：d_snd_v (i j : Int) (hij : i + 1 = j) : (mappingCone φ).d i j ≫ (snd φ).v 
j j (add_zero _) = (fst φ).1.v i j hij ≫ φ.f j + (snd φ).v i i (add_zero i) ≫ G.
d i j
参数：i j : Int；hij : i + 1 = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHoms_v`：ofHoms_v (ψ : forall (p : In
t), F.X p ⟶ G.X p) (p : Int) : (ofHoms ψ).v p p (add_zero p) = ψ p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `HomologicalComplex.homotopyCofiber.d_sndX`：d_sndX (i j : ι) (hij : c.Rel
 i j) : d φ i j ≫ sndX φ j = fstX φ i j hij ≫ φ.f j + sndX φ i ≫ G.d i j
-/
lemma d_snd_v (i j : ℤ) (hij : i + 1 = j) :
    (mappingCone φ).d i j ≫ (snd φ).v j j (add_zero _) =
      (fst φ).1.v i j hij ≫ φ.f j + (snd φ).v i i (add_zero i) ≫ G.d i j := by
  dsimp [mappingCone, snd, fst]
  simp only [Cochain.ofHoms_v]
  apply homotopyCofiber.d_sndX

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.d_snd_v'** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.
mappingCone`。
形式化陈述：d_snd_v' (n : Int) : (mappingCone φ).d (n - 1) n ≫ (snd φ).v n n (add_zero
 n) = (fst φ : Cochain (mappingCone φ) F 1).v (n - 1) n (by lia) ≫ φ.f n + (snd 
φ).v (n - 1) (n - 1) (add_zero _) ≫ G.d (n - 1) n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.mappingCone.d_snd_v`：d_snd_v (i j : Int) (hij : i + 1 = j
) : (mappingCone φ).d i j ≫ (snd φ).v j j (add_zero _) = (fst φ).1.v i j hij ≫ φ
.f j + (snd φ).v i i (ad…
-/
lemma d_snd_v' (n : ℤ) :
    (mappingCone φ).d (n - 1) n ≫ (snd φ).v n n (add_zero n) =
    (fst φ : Cochain (mappingCone φ) F 1).v (n - 1) n (by lia) ≫ φ.f n +
      (snd φ).v (n - 1) (n - 1) (add_zero _) ≫ G.d (n - 1) n := by
  apply d_snd_v

@[simp]
/-
**CochainComplex.mappingCone.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.mappingC
one`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_inl :
    δ (-1) 0 (inl φ) = Cochain.ofHom (φ ≫ inr φ) := by
  ext p
  simp [δ_v (-1) 0 (neg_add_cancel 1) (inl φ) p p (add_zero p) _ _ rfl rfl,
    inl_v_d φ p (p - 1) (p + 1) (by lia) (by lia)]

@[simp]
/-
**CochainComplex.mappingCone.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.mappingC
one`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_snd :
    δ 0 1 (snd φ) = -(fst φ).1.comp (Cochain.ofHom φ) (add_zero 1) := by
  ext p q hpq
  simp [d_snd_v φ p q hpq]

section

variable {K : CochainComplex C ℤ} {n m : ℤ}

/-- Given `φ : F ⟶ G`, this is the cochain in `Cochain (mappingCone φ) K n` that is
constructed from two cochains `α : Cochain F K m` (with `m + 1 = n`) and `β : Cochain F K n`. -/
/-
**CochainComplex.mappingCone.descCochain** 是 Mathlib 中的一个定义，位于命名空间 `CochainCompl
ex.mappingCone`。
形式化陈述：descCochain (α : Cochain F K m) (β : Cochain G K n) (h : m + 1 = n) : Coch
ain (mappingCone φ) K n
参数：α : Cochain F K m；β : Cochain G K n；h : m + 1 = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `φ : F ⟶ G`, this is the cochain in `Cochain (mappingCone φ) K n` that is
constructed from two cochains `α : Cochain F K m` (with `m + 1 = n`) and `β : Co
chain F K n`.
-/
noncomputable def descCochain (α : Cochain F K m) (β : Cochain G K n) (h : m + 1 = n) :
    Cochain (mappingCone φ) K n :=
  (fst φ).1.comp α (by rw [← h, add_comm]) + (snd φ).comp β (zero_add n)

variable (α : Cochain F K m) (β : Cochain G K n) (h : m + 1 = n)

@[simp]
/-
**CochainComplex.mappingCone.inl_descCochain** 是 Mathlib 中的一个引理，位于命名空间 `CochainC
omplex.mappingCone`。
形式化陈述：inl_descCochain : (inl φ).comp (descCochain φ α β h) (by lia) = α
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
· 使用定理 `CochainComplex.HomComplex.Cochain.comp_add`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G K : 
CochainComplex C ℤ} {n₁ n₂ n₁₂ :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CochainComplex.mappingCone.inl_fst_assoc`：inl_fst_assoc {K : CochainComp
lex C Int} {d e : Int} (γ : Cochain F K d) (he : 1 + d = e) : (inl φ).comp ((fst
 φ).1.comp γ he) (by rw [← he,…
· 使用引理 `CochainComplex.mappingCone.inl_snd_assoc`：inl_snd_assoc {K : CochainComp
lex C Int} {d e f : Int} (γ : Cochain G K d) (he : 0 + d = e) (hf : -1 + e = f) 
: (inl φ).comp ((snd φ).comp γ…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_descCochain :
    (inl φ).comp (descCochain φ α β h) (by lia) = α := by
  simp [descCochain]

@[simp]
/-
**CochainComplex.mappingCone.inr_descCochain** 是 Mathlib 中的一个引理，位于命名空间 `CochainC
omplex.mappingCone`。
形式化陈述：inr_descCochain : (Cochain.ofHom (inr φ)).comp (descCochain φ α β h) (zero
_add n) = β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cochain.comp_add`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G K : 
CochainComplex C ℤ} {n₁ n₂ n₁₂ :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CochainComplex.mappingCone.inr_fst_assoc`：inr_fst_assoc {K : CochainComp
lex C Int} {d e f : Int} (γ : Cochain F K d) (he : 1 + d = e) (hf : 0 + e = f) :
 (Cochain.ofHom (inr φ)).comp …
· 使用引理 `CochainComplex.mappingCone.inr_snd_assoc`：inr_snd_assoc {K : CochainComp
lex C Int} {d e : Int} (γ : Cochain G K d) (he : 0 + d = e) : (Cochain.ofHom (in
r φ)).comp ((snd φ).comp γ he)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_descCochain :
    (Cochain.ofHom (inr φ)).comp (descCochain φ α β h) (zero_add n) = β := by
  simp [descCochain]

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.inl_v_descCochain_v** 是 Mathlib 中的一个引理，位于命名空间 `Coch
ainComplex.mappingCone`。
形式化陈述：inl_v_descCochain_v (p₁ p₂ p₃ : Int) (h₁₂ : p₁ + (-1) = p₂) (h₂₃ : p₂ + n 
= p₃) : (inl φ).v p₁ p₂ h₁₂ ≫ (descCochain φ α β h).v p₂ p₃ h₂₃ = α.v p₁ p₃ (by 
rw [← h₂₃, ← h₁₂, ← h, add_comm m, add_assoc, neg_add_cancel_left])
参数：p₁ p₂ p₃ : Int；h₁₂ : p₁ + (-1) = p₂；h₂₃ : p₂ + n = p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用引理 `CochainComplex.HomComplex.Cochain.congr_v`：congr_v {z₁ z₂ : Cochain F G 
n} (h : z₁ = z₂) (p q : Int) (hpq : p + n = q) : z₁.v p q hpq = z₂.v p q hpq
· 使用引理 `CochainComplex.mappingCone.inl_descCochain`：inl_descCochain : (inl φ).co
mp (descCochain φ α β h) (by lia) = α
-/
lemma inl_v_descCochain_v (p₁ p₂ p₃ : ℤ) (h₁₂ : p₁ + (-1) = p₂) (h₂₃ : p₂ + n = p₃) :
    (inl φ).v p₁ p₂ h₁₂ ≫ (descCochain φ α β h).v p₂ p₃ h₂₃ =
        α.v p₁ p₃ (by rw [← h₂₃, ← h₁₂, ← h, add_comm m, add_assoc, neg_add_cancel_left]) := by
  simpa only [Cochain.comp_v _ _ (show -1 + n = m by lia) p₁ p₂ p₃
    (by lia) (by lia)] using
      Cochain.congr_v (inl_descCochain φ α β h) p₁ p₃ (by lia)

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.inr_f_descCochain_v** 是 Mathlib 中的一个引理，位于命名空间 `Coch
ainComplex.mappingCone`。
形式化陈述：inr_f_descCochain_v (p₁ p₂ : Int) (h₁₂ : p₁ + n = p₂) : (inr φ).f p₁ ≫ (de
scCochain φ α β h).v p₁ p₂ h₁₂ = β.v p₁ p₂ h₁₂
参数：p₁ p₂ : Int；h₁₂ : p₁ + n = p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用引理 `CochainComplex.HomComplex.Cochain.congr_v`：congr_v {z₁ z₂ : Cochain F G 
n} (h : z₁ = z₂) (p q : Int) (hpq : p + n = q) : z₁.v p q hpq = z₂.v p q hpq
· 使用引理 `CochainComplex.mappingCone.inr_descCochain`：inr_descCochain : (Cochain.o
fHom (inr φ)).comp (descCochain φ α β h) (zero_add n) = β
-/
lemma inr_f_descCochain_v (p₁ p₂ : ℤ) (h₁₂ : p₁ + n = p₂) :
    (inr φ).f p₁ ≫ (descCochain φ α β h).v p₁ p₂ h₁₂ = β.v p₁ p₂ h₁₂ := by
  simpa only [Cochain.comp_v _ _ (zero_add n) p₁ p₁ p₂ (add_zero p₁) h₁₂, Cochain.ofHom_v]
    using Cochain.congr_v (inr_descCochain φ α β h) p₁ p₂ (by lia)

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.mappingCone.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.mappingC
one`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_descCochain (n' : ℤ) (hn' : n + 1 = n') :
    δ n n' (descCochain φ α β h) =
      (fst φ).1.comp (δ m n α +
          n'.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (by lia) +
      (snd φ).comp (δ n n' β) (zero_add n') := by
  dsimp only [descCochain]
  simp only [δ_add, Cochain.comp_add, δ_comp (fst φ).1 α _ 2 n n' hn' (by lia) (by lia),
    Cocycle.δ_eq_zero, Cochain.zero_comp, smul_zero, add_zero,
    δ_comp (snd φ) β (zero_add n) 1 n' n' hn' (zero_add 1) hn', δ_snd, Cochain.neg_comp,
    smul_neg, Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.comp_units_smul, ← hn',
    Int.negOnePow_succ, Units.neg_smul, Cochain.comp_neg]
  abel

end

/-- Given `φ : F ⟶ G`, this is the cocycle in `Cocycle (mappingCone φ) K n` that is
constructed from `α : Cochain F K m` (with `m + 1 = n`) and `β : Cocycle F K n`,
when a suitable cocycle relation is satisfied. -/
@[simps!]
/-
**CochainComplex.mappingCone.descCocycle** 是 Mathlib 中的一个定义，位于命名空间 `CochainCompl
ex.mappingCone`。
形式化陈述：descCocycle {K : CochainComplex C Int} {n m : Int} (α : Cochain F K m) (β 
: Cocycle G K n) (h : m + 1 = n) (eq : δ m n α = n.negOnePow • (Cochain.ofHom φ)
.comp β.1 (zero_add n)) : Cocycle (mappingCone φ) K n
参数：α : Cochain F K m；β : Cocycle G K n；h : m + 1 = n；eq : δ m n α = n.negOnePow 
• (Cochain.ofHom φ).comp β.1 (zero_add n)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `φ : F ⟶ G`, this is the cocycle in `Cocycle (mappingCone φ) K n` that is
constructed from `α : Cochain F K m` (with `m + 1 = n`) and `β : Cocycle F K n`,
when a suitable cocycle relation is satisfied.
-/
noncomputable def descCocycle {K : CochainComplex C ℤ} {n m : ℤ}
    (α : Cochain F K m) (β : Cocycle G K n)
    (h : m + 1 = n) (eq : δ m n α = n.negOnePow • (Cochain.ofHom φ).comp β.1 (zero_add n)) :
    Cocycle (mappingCone φ) K n :=
  Cocycle.mk (descCochain φ α β.1 h) (n + 1) rfl
    (by simp [δ_descCochain _ _ _ _ _ rfl, eq, Int.negOnePow_succ])

section

variable {K : CochainComplex C ℤ}

/-- Given `φ : F ⟶ G`, this is the morphism `mappingCone φ ⟶ K` that is constructed
from a cochain `α : Cochain F K (-1)` and a morphism `β : G ⟶ K` such that
`δ (-1) 0 α = Cochain.ofHom (φ ≫ β)`. -/
/-
**CochainComplex.mappingCone.desc** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.mapp
ingCone`。
形式化陈述：desc (α : Cochain F K (-1)) (β : G ⟶ K) (eq : δ (-1) 0 α = Cochain.ofHom (
φ ≫ β)) : mappingCone φ ⟶ K
参数：α : Cochain F K (-1)；β : G ⟶ K；eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `φ : F ⟶ G`, this is the morphism `mappingCone φ ⟶ K` that is constructed
from a cochain `α : Cochain F K (-1)` and a morphism `β : G ⟶ K` such that
`δ (-1) 0 α = Cochain.ofHom (φ ≫ β)`.
-/
noncomputable def desc (α : Cochain F K (-1)) (β : G ⟶ K)
    (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β)) : mappingCone φ ⟶ K :=
  Cocycle.homOf (descCocycle φ α (Cocycle.ofHom β) (neg_add_cancel 1) (by simp [eq]))

variable (α : Cochain F K (-1)) (β : G ⟶ K) (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β))

@[simp]
/-
**CochainComplex.mappingCone.ofHom_desc** 是 Mathlib 中的一个引理，位于命名空间 `CochainComple
x.mappingCone`。
形式化陈述：ofHom_desc : Cochain.ofHom (desc φ α β eq) = descCochain φ α (Cochain.ofHo
m β) (neg_add_cancel 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cocycle.cochain_ofHom_homOf_eq_coe`：cochain_of
Hom_homOf_eq_coe (z : Cocycle F G 0) : Cochain.ofHom (homOf z) = (z : Cochain F 
G 0)
· 使用定理 `CochainComplex.mappingCone.descCocycle_coe`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `CochainComplex.HomComplex.Cocycle.ofHom_coe`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : C
ochainComplex C ℤ} (φ : F ⟶ G),  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofHom_desc :
    Cochain.ofHom (desc φ α β eq) = descCochain φ α (Cochain.ofHom β) (neg_add_cancel 1) := by
  simp [desc]

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.inl_v_desc_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex.mappingCone`。
形式化陈述：inl_v_desc_f (p q : Int) (h : p + (-1) = q) : (inl φ).v p q h ≫ (desc φ α 
β eq).f q = α.v p q h
参数：p q : Int；h : p + (-1) = q。
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
· 使用定理 `CochainComplex.mappingCone.descCocycle_coe`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `CochainComplex.HomComplex.Cocycle.ofHom_coe`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : C
ochainComplex C ℤ} (φ : F ⟶ G),  …
· 使用引理 `CochainComplex.mappingCone.inl_v_descCochain_v`：inl_v_descCochain_v (p₁ 
p₂ p₃ : Int) (h₁₂ : p₁ + (-1) = p₂) (h₂₃ : p₂ + n = p₃) : (inl φ).v p₁ p₂ h₁₂ ≫ 
(descCochain φ α β h).v p₂ p₃ h₂₃ = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_v_desc_f (p q : ℤ) (h : p + (-1) = q) :
    (inl φ).v p q h ≫ (desc φ α β eq).f q = α.v p q h := by
  simp [desc]
/-
**CochainComplex.mappingCone.inl_desc** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.
mappingCone`。
形式化陈述：inl_desc : (inl φ).comp (Cochain.ofHom (desc φ α β eq)) (add_zero _) = α
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
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用引理 `CochainComplex.mappingCone.ofHom_desc`：ofHom_desc : Cochain.ofHom (desc 
φ α β eq) = descCochain φ α (Cochain.ofHom β) (neg_add_cancel 1)
· 使用引理 `CochainComplex.mappingCone.inl_descCochain`：inl_descCochain : (inl φ).co
mp (descCochain φ α β h) (by lia) = α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_desc :
    (inl φ).comp (Cochain.ofHom (desc φ α β eq)) (add_zero _) = α := by
  simp

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.inr_f_desc_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex.mappingCone`。
形式化陈述：inr_f_desc_f (p : Int) : (inr φ).f p ≫ (desc φ α β eq).f p = β.f p
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
· 使用定理 `CochainComplex.mappingCone.descCocycle_coe`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `CochainComplex.HomComplex.Cocycle.ofHom_coe`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : C
ochainComplex C ℤ} (φ : F ⟶ G),  …
· 使用引理 `CochainComplex.mappingCone.inr_f_descCochain_v`：inr_f_descCochain_v (p₁ 
p₂ : Int) (h₁₂ : p₁ + n = p₂) : (inr φ).f p₁ ≫ (descCochain φ α β h).v p₁ p₂ h₁₂
 = β.v p₁ p₂ h₁₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_f_desc_f (p : ℤ) :
    (inr φ).f p ≫ (desc φ α β eq).f p = β.f p := by
  simp [desc]

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.inr_desc** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.
mappingCone`。
形式化陈述：inr_desc : inr φ ≫ desc φ α β eq = β
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
· 使用引理 `CochainComplex.mappingCone.inr_f_desc_f`：inr_f_desc_f (p : Int) : (inr φ
).f p ≫ (desc φ α β eq).f p = β.f p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_desc : inr φ ≫ desc φ α β eq = β := by cat_disch
/-
**CochainComplex.mappingCone.desc_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.ma
ppingCone`。
形式化陈述：desc_f (p q : Int) (hpq : p + 1 = q) : (desc φ α β eq).f p = (fst φ).1.v p
 q hpq ≫ α.v q p (by lia) + (snd φ).v p p (add_zero p) ≫ β.f p
参数：p q : Int；hpq : p + 1 = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CochainComplex.mappingCone.ext_from_iff`：ext_from_iff (i j : Int) (hij :
 j + 1 = i) {A : C} (f g : (mappingCone φ).X j ⟶ A) : f = g ↔ (inl φ).v i j (by 
lia) ≫ f = (inl φ).v i j (by …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.mappingCone.inl_v_desc_f`：inl_v_desc_f (p q : Int) (h : p
 + (-1) = q) : (inl φ).v p q h ≫ (desc φ α β eq).f q = α.v p q h
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CochainComplex.mappingCone.inl_v_fst_v_assoc`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F 
G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `CochainComplex.mappingCone.inl_v_snd_v_assoc`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F 
G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.mappingCone.inr_f_desc_f`：inr_f_desc_f (p : Int) : (inr φ
).f p ≫ (desc φ α β eq).f p = β.f p
· 使用定理 `CochainComplex.mappingCone.inr_f_fst_v_assoc`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F 
G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `CochainComplex.mappingCone.inr_f_snd_v_assoc`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F 
G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma desc_f (p q : ℤ) (hpq : p + 1 = q) :
    (desc φ α β eq).f p = (fst φ).1.v p q hpq ≫ α.v q p (by lia) +
      (snd φ).v p p (add_zero p) ≫ β.f p := by
  simp [ext_from_iff _ _ _ hpq]

end

/-- Constructor for homotopies between morphisms from a mapping cone. -/
/-
**CochainComplex.mappingCone.descHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `CochainComp
lex.mappingCone`。
形式化陈述：descHomotopy {K : CochainComplex C Int} (f₁ f₂ : mappingCone φ ⟶ K) (γ₁ : 
Cochain F K (-2)) (γ₂ : Cochain G K (-1)) (h₁ : (inl φ).comp (Cochain.ofHom f₁) 
(add_zero (-1)) = δ (-2) (-1) γ₁ + (Cochain.ofHom φ).comp γ₂ (zero_add (-1)) + (
inl φ).comp (Cochain.ofHom f₂) (add_zero (-1))) (h₂ : Cochain.ofHom (inr φ ≫ f₁)
 = δ (-1) 0 γ₂ + Cochain.ofHom (inr φ ≫ f₂)) : Homotopy f₁ f₂
参数：f₁ f₂ : mappingCone φ ⟶ K；γ₁ : Cochain F K (-2)；γ₂ : Cochain G K (-1)；h₁ : (i
nl φ).comp (Cochain.ofHom f₁) (add_zero (-1)) = δ (-2) (-1) γ₁ + (Cochain.ofHom 
φ).comp γ₂ (zero_add (-1)) + (inl φ).comp (Cochain.ofHom f₂) (add_zero (-1))；h₂ 
: Cochain.ofHom (inr φ ≫ f₁) = δ (-1) 0 γ₂ + Cochain.ofHom (inr φ ≫ f₂)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Constructor for homotopies between morphisms from a mapping cone.
-/
noncomputable def descHomotopy {K : CochainComplex C ℤ} (f₁ f₂ : mappingCone φ ⟶ K)
    (γ₁ : Cochain F K (-2)) (γ₂ : Cochain G K (-1))
    (h₁ : (inl φ).comp (Cochain.ofHom f₁) (add_zero (-1)) =
      δ (-2) (-1) γ₁ + (Cochain.ofHom φ).comp γ₂ (zero_add (-1)) +
      (inl φ).comp (Cochain.ofHom f₂) (add_zero (-1)))
    (h₂ : Cochain.ofHom (inr φ ≫ f₁) = δ (-1) 0 γ₂ + Cochain.ofHom (inr φ ≫ f₂)) :
    Homotopy f₁ f₂ :=
  (Cochain.equivHomotopy f₁ f₂).symm ⟨descCochain φ γ₁ γ₂ (by simp), by
    simp only [Cochain.ofHom_comp] at h₂
    simp [ext_cochain_from_iff _ _ _ (neg_add_cancel 1),
      δ_descCochain _ _ _ _ _ (neg_add_cancel 1), h₁, h₂]⟩

section

variable {K : CochainComplex C ℤ} {n m : ℤ}

/-- Given `φ : F ⟶ G`, this is the cochain in `Cochain (mappingCone φ) K n` that is
constructed from two cochains `α : Cochain F K m` (with `m + 1 = n`) and `β : Cochain F K n`. -/
/-
**CochainComplex.mappingCone.liftCochain** 是 Mathlib 中的一个定义，位于命名空间 `CochainCompl
ex.mappingCone`。
形式化陈述：liftCochain (α : Cochain K F m) (β : Cochain K G n) (h : n + 1 = m) : Coch
ain K (mappingCone φ) n
参数：α : Cochain K F m；β : Cochain K G n；h : n + 1 = m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `φ : F ⟶ G`, this is the cochain in `Cochain (mappingCone φ) K n` that is
constructed from two cochains `α : Cochain F K m` (with `m + 1 = n`) and `β : Co
chain F K n`.
-/
noncomputable def liftCochain (α : Cochain K F m) (β : Cochain K G n) (h : n + 1 = m) :
    Cochain K (mappingCone φ) n :=
  α.comp (inl φ) (by lia) + β.comp (Cochain.ofHom (inr φ)) (add_zero n)

variable (α : Cochain K F m) (β : Cochain K G n) (h : n + 1 = m)

@[simp]
/-
**CochainComplex.mappingCone.liftCochain_fst** 是 Mathlib 中的一个引理，位于命名空间 `CochainC
omplex.mappingCone`。
形式化陈述：liftCochain_fst : (liftCochain φ α β h).comp (fst φ).1 h = α
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
· 使用定理 `CochainComplex.HomComplex.Cochain.add_comp`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G K : 
CochainComplex C ℤ} {n₁ n₂ n₁₂ :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_assoc_of_second_degree_eq_neg_thi
rd_degree`：comp_assoc_of_second_degree_eq_neg_third_degree {n₁ n₂ n₁₂ : Int} (z₁
 : Cochain F G n₁) (z₂ : Cochain G K (-n₂)) (z₃ : Cochain K L n₂) (h₁₂ …
· 使用引理 `CochainComplex.mappingCone.inl_fst`：inl_fst : (inl φ).comp (fst φ).1 (ne
g_add_cancel 1) = Cochain.ofHom (𝟙 F)
· 使用定理 `CochainComplex.HomComplex.Cochain.comp_id`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} {n : ℤ} (z₁ : …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain`：
comp_assoc_of_second_is_zero_cochain {n₁ n₃ n₁₃ : Int} (z₁ : Cochain F G n₁) (z₂
 : Cochain G K 0) (z₃ : Cochain K L n₃) (h₁₃ : n₁ + n₃ = n₁₃…
· 使用引理 `CochainComplex.mappingCone.inr_fst`：inr_fst : (Cochain.ofHom (inr φ)).co
mp (fst φ).1 (zero_add 1) = 0
· 使用定理 `CochainComplex.HomComplex.Cochain.comp_zero`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G K :
 CochainComplex C ℤ} {n₁ n₂ n₁₂ :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftCochain_fst :
    (liftCochain φ α β h).comp (fst φ).1 h = α := by
  simp [liftCochain]

@[simp]
/-
**CochainComplex.mappingCone.liftCochain_snd** 是 Mathlib 中的一个引理，位于命名空间 `CochainC
omplex.mappingCone`。
形式化陈述：liftCochain_snd : (liftCochain φ α β h).comp (snd φ) (add_zero n) = β
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
· 使用定理 `CochainComplex.HomComplex.Cochain.add_comp`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G K : 
CochainComplex C ℤ} {n₁ n₂ n₁₂ :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_assoc_of_third_is_zero_cochain`：c
omp_assoc_of_third_is_zero_cochain {n₁ n₂ n₁₂ : Int} (z₁ : Cochain F G n₁) (z₂ :
 Cochain G K n₂) (z₃ : Cochain K L 0) (h₁₂ : n₁ + n₂ = n₁₂)…
· 使用引理 `CochainComplex.mappingCone.inl_snd`：inl_snd : (inl φ).comp (snd φ) (add_
zero (-1)) = 0
· 使用定理 `CochainComplex.HomComplex.Cochain.comp_zero`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G K :
 CochainComplex C ℤ} {n₁ n₂ n₁₂ :…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain`：
comp_assoc_of_second_is_zero_cochain {n₁ n₃ n₁₃ : Int} (z₁ : Cochain F G n₁) (z₂
 : Cochain G K 0) (z₃ : Cochain K L n₃) (h₁₃ : n₁ + n₃ = n₁₃…
· 使用引理 `CochainComplex.mappingCone.inr_snd`：inr_snd : (Cochain.ofHom (inr φ)).co
mp (snd φ) (zero_add 0) = Cochain.ofHom (𝟙 G)
· 使用定理 `CochainComplex.HomComplex.Cochain.comp_id`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} {n : ℤ} (z₁ : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftCochain_snd :
    (liftCochain φ α β h).comp (snd φ) (add_zero n) = β := by
  simp [liftCochain]

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.liftCochain_v_fst_v** 是 Mathlib 中的一个引理，位于命名空间 `Coch
ainComplex.mappingCone`。
形式化陈述：liftCochain_v_fst_v (p₁ p₂ p₃ : Int) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + 1 = p
₃) : (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (fst φ).1.v p₂ p₃ h₂₃ = α.v p₁ p₃ (by l
ia)
参数：p₁ p₂ p₃ : Int；h₁₂ : p₁ + n = p₂；h₂₃ : p₂ + 1 = p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用引理 `CochainComplex.HomComplex.Cochain.congr_v`：congr_v {z₁ z₂ : Cochain F G 
n} (h : z₁ = z₂) (p q : Int) (hpq : p + n = q) : z₁.v p q hpq = z₂.v p q hpq
· 使用引理 `CochainComplex.mappingCone.liftCochain_fst`：liftCochain_fst : (liftCocha
in φ α β h).comp (fst φ).1 h = α
-/
lemma liftCochain_v_fst_v (p₁ p₂ p₃ : ℤ) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + 1 = p₃) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (fst φ).1.v p₂ p₃ h₂₃ = α.v p₁ p₃ (by lia) := by
  simpa only [Cochain.comp_v _ _ h p₁ p₂ p₃ h₁₂ h₂₃]
    using Cochain.congr_v (liftCochain_fst φ α β h) p₁ p₃ (by lia)

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.liftCochain_v_snd_v** 是 Mathlib 中的一个引理，位于命名空间 `Coch
ainComplex.mappingCone`。
形式化陈述：liftCochain_v_snd_v (p₁ p₂ : Int) (h₁₂ : p₁ + n = p₂) : (liftCochain φ α β
 h).v p₁ p₂ h₁₂ ≫ (snd φ).v p₂ p₂ (add_zero p₂) = β.v p₁ p₂ h₁₂
参数：p₁ p₂ : Int；h₁₂ : p₁ + n = p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用引理 `CochainComplex.HomComplex.Cochain.congr_v`：congr_v {z₁ z₂ : Cochain F G 
n} (h : z₁ = z₂) (p q : Int) (hpq : p + n = q) : z₁.v p q hpq = z₂.v p q hpq
· 使用引理 `CochainComplex.mappingCone.liftCochain_snd`：liftCochain_snd : (liftCocha
in φ α β h).comp (snd φ) (add_zero n) = β
-/
lemma liftCochain_v_snd_v (p₁ p₂ : ℤ) (h₁₂ : p₁ + n = p₂) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (snd φ).v p₂ p₂ (add_zero p₂) = β.v p₁ p₂ h₁₂ := by
  simpa only [Cochain.comp_v _ _ (add_zero n) p₁ p₂ p₂ h₁₂ (add_zero p₂)]
    using Cochain.congr_v (liftCochain_snd φ α β h) p₁ p₂ (by lia)
/-
**CochainComplex.mappingCone.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.mappingC
one`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_liftCochain (m' : ℤ) (hm' : m + 1 = m') :
    δ n m (liftCochain φ α β h) = -(δ m m' α).comp (inl φ) (by lia) +
      (δ n m β + α.comp (Cochain.ofHom φ) (add_zero m)).comp
        (Cochain.ofHom (inr φ)) (add_zero m) := by
  dsimp only [liftCochain]
  simp only [δ_add, δ_comp α (inl φ) _ m' _ _ h hm' (neg_add_cancel 1),
    δ_comp_zero_cochain _ _ _ h, δ_inl, Cochain.ofHom_comp,
    Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    δ_ofHom, Cochain.comp_zero, zero_add, Cochain.add_comp,
    Cochain.comp_assoc_of_second_is_zero_cochain]
  abel

end

/-- Given `φ : F ⟶ G`, this is the cocycle in `Cocycle K (mappingCone φ) n` that is
constructed from `α : Cochain K F m` (with `n + 1 = m`) and `β : Cocycle K G n`,
when a suitable cocycle relation is satisfied. -/
@[simps!]
/-
**CochainComplex.mappingCone.liftCocycle** 是 Mathlib 中的一个定义，位于命名空间 `CochainCompl
ex.mappingCone`。
形式化陈述：liftCocycle {K : CochainComplex C Int} {n m : Int} (α : Cocycle K F m) (β 
: Cochain K G n) (h : n + 1 = m) (eq : δ n m β + α.1.comp (Cochain.ofHom φ) (add
_zero m) = 0) : Cocycle K (mappingCone φ) n
参数：α : Cocycle K F m；β : Cochain K G n；h : n + 1 = m；eq : δ n m β + α.1.comp (Co
chain.ofHom φ) (add_zero m) = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `φ : F ⟶ G`, this is the cocycle in `Cocycle K (mappingCone φ) n` that is
constructed from `α : Cochain K F m` (with `n + 1 = m`) and `β : Cocycle K G n`,
when a suitable cocycle relation is satisfied.
-/
noncomputable def liftCocycle {K : CochainComplex C ℤ} {n m : ℤ}
    (α : Cocycle K F m) (β : Cochain K G n) (h : n + 1 = m)
    (eq : δ n m β + α.1.comp (Cochain.ofHom φ) (add_zero m) = 0) :
    Cocycle K (mappingCone φ) n :=
  Cocycle.mk (liftCochain φ α β h) m h (by
    simp only [δ_liftCochain φ α β h (m + 1) rfl, eq,
      Cocycle.δ_eq_zero, Cochain.zero_comp, neg_zero, add_zero])

section

variable {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + α.1.comp (Cochain.ofHom φ) (add_zero 1) = 0)

/-- Given `φ : F ⟶ G`, this is the morphism `K ⟶ mappingCone φ` that is constructed
from a cocycle `α : Cochain K F 1` and a cochain `β : Cochain K G 0`
when a suitable cocycle relation is satisfied. -/
/-
**CochainComplex.mappingCone.lift** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.mapp
ingCone`。
形式化陈述：lift : K ⟶ mappingCone φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `φ : F ⟶ G`, this is the morphism `K ⟶ mappingCone φ` that is constructed
from a cocycle `α : Cochain K F 1` and a cochain `β : Cochain K G 0`
when a suitable cocycle relation is satisfied.
-/
noncomputable def lift :
    K ⟶ mappingCone φ :=
  Cocycle.homOf (liftCocycle φ α β (zero_add 1) eq)

@[simp]
/-
**CochainComplex.mappingCone.ofHom_lift** 是 Mathlib 中的一个引理，位于命名空间 `CochainComple
x.mappingCone`。
形式化陈述：ofHom_lift : Cochain.ofHom (lift φ α β eq) = liftCochain φ α β (zero_add 1
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cocycle.cochain_ofHom_homOf_eq_coe`：cochain_of
Hom_homOf_eq_coe (z : Cocycle F G 0) : Cochain.ofHom (homOf z) = (z : Cochain F 
G 0)
· 使用定理 `CochainComplex.mappingCone.liftCocycle_coe`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofHom_lift :
    Cochain.ofHom (lift φ α β eq) = liftCochain φ α β (zero_add 1) := by
  simp only [lift, Cocycle.cochain_ofHom_homOf_eq_coe, liftCocycle_coe]

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.lift_f_fst_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex.mappingCone`。
形式化陈述：lift_f_fst_v (p q : Int) (hpq : p + 1 = q) : (lift φ α β eq).f p ≫ (fst φ)
.1.v p q hpq = α.1.v p q hpq
参数：p q : Int；hpq : p + 1 = q。
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
· 使用定理 `CochainComplex.HomComplex.Cocycle.homOf_f`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} (z : CochainCo…
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.mappingCone.liftCocycle_coe`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} (φ : F ⟶ G…
· 使用引理 `CochainComplex.mappingCone.liftCochain_v_fst_v`：liftCochain_v_fst_v (p₁ 
p₂ p₃ : Int) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + 1 = p₃) : (liftCochain φ α β h).v p
₁ p₂ h₁₂ ≫ (fst φ).1.v p₂ p₃ h₂₃ = α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_f_fst_v (p q : ℤ) (hpq : p + 1 = q) :
    (lift φ α β eq).f p ≫ (fst φ).1.v p q hpq = α.1.v p q hpq := by
  simp [lift]
/-
**CochainComplex.mappingCone.lift_fst** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.
mappingCone`。
形式化陈述：lift_fst : (Cochain.ofHom (lift φ α β eq)).comp (fst φ).1 (zero_add 1) = α
.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.mappingCone.ofHom_lift`：ofHom_lift : Cochain.ofHom (lift 
φ α β eq) = liftCochain φ α β (zero_add 1)
· 使用引理 `CochainComplex.mappingCone.liftCochain_fst`：liftCochain_fst : (liftCocha
in φ α β h).comp (fst φ).1 h = α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_fst :
    (Cochain.ofHom (lift φ α β eq)).comp (fst φ).1 (zero_add 1) = α.1 := by simp

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.lift_f_snd_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex.mappingCone`。
形式化陈述：lift_f_snd_v (p q : Int) (hpq : p + 0 = q) : (lift φ α β eq).f p ≫ (snd φ)
.v p q hpq = β.v p q hpq
参数：p q : Int；hpq : p + 0 = q。
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
· 使用定理 `CochainComplex.HomComplex.Cocycle.homOf_f`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} (z : CochainCo…
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.mappingCone.liftCocycle_coe`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} (φ : F ⟶ G…
· 使用引理 `CochainComplex.mappingCone.liftCochain_v_snd_v`：liftCochain_v_snd_v (p₁ 
p₂ : Int) (h₁₂ : p₁ + n = p₂) : (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (snd φ).v p₂
 p₂ (add_zero p₂) = β.v p₁ p₂ h₁₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_f_snd_v (p q : ℤ) (hpq : p + 0 = q) :
    (lift φ α β eq).f p ≫ (snd φ).v p q hpq = β.v p q hpq := by
  obtain rfl : q = p := by lia
  simp [lift]
/-
**CochainComplex.mappingCone.lift_snd** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.
mappingCone`。
形式化陈述：lift_snd : (Cochain.ofHom (lift φ α β eq)).comp (snd φ) (zero_add 0) = β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.mappingCone.ofHom_lift`：ofHom_lift : Cochain.ofHom (lift 
φ α β eq) = liftCochain φ α β (zero_add 1)
· 使用引理 `CochainComplex.mappingCone.liftCochain_snd`：liftCochain_snd : (liftCocha
in φ α β h).comp (snd φ) (add_zero n) = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_snd :
    (Cochain.ofHom (lift φ α β eq)).comp (snd φ) (zero_add 0) = β := by simp
/-
**CochainComplex.mappingCone.lift_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.ma
ppingCone`。
形式化陈述：lift_f (p q : Int) (hpq : p + 1 = q) : (lift φ α β eq).f p = α.1.v p q hpq
 ≫ (inl φ).v q p (by omega) + β.v p p (add_zero p) ≫ (inr φ).f p
参数：p q : Int；hpq : p + 1 = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CochainComplex.mappingCone.ext_to_iff`：ext_to_iff (i j : Int) (hij : i +
 1 = j) {A : C} (f g : A ⟶ (mappingCone φ).X i) : f = g ↔ f ≫ (fst φ).1.v i j hi
j = g ≫ (fst φ).1.v i j hij…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.mappingCone.lift_f_fst_v`：lift_f_fst_v (p q : Int) (hpq :
 p + 1 = q) : (lift φ α β eq).f p ≫ (fst φ).1.v p q hpq = α.1.v p q hpq
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CochainComplex.mappingCone.inl_v_fst_v`：inl_v_fst_v (p q : Int) (hpq : q
 + 1 = p) : (inl φ).v p q (by rw [← hpq, add_neg_cancel_right]) ≫ (fst φ : Cocha
in (mappingCone φ) F 1).v q …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CochainComplex.mappingCone.inr_f_fst_v`：inr_f_fst_v (p q : Int) (hpq : p
 + 1 = q) : (inr φ).f p ≫ (fst φ).1.v p q hpq = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.mappingCone.lift_f_snd_v`：lift_f_snd_v (p q : Int) (hpq :
 p + 0 = q) : (lift φ α β eq).f p ≫ (snd φ).v p q hpq = β.v p q hpq
· 使用引理 `CochainComplex.mappingCone.inl_v_snd_v`：inl_v_snd_v (p q : Int) (hpq : p
 + (-1) = q) : (inl φ).v p q hpq ≫ (snd φ).v q q (add_zero q) = 0
· 使用引理 `CochainComplex.mappingCone.inr_f_snd_v`：inr_f_snd_v (p : Int) : (inr φ).
f p ≫ (snd φ).v p p (add_zero p) = 𝟙 _
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma lift_f (p q : ℤ) (hpq : p + 1 = q) :
    (lift φ α β eq).f p = α.1.v p q hpq ≫
      (inl φ).v q p (by omega) + β.v p p (add_zero p) ≫ (inr φ).f p := by
  simp [ext_to_iff _ _ _ hpq]

end

/-- Constructor for homotopies between morphisms to a mapping cone. -/
/-
**CochainComplex.mappingCone.liftHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `CochainComp
lex.mappingCone`。
形式化陈述：liftHomotopy {K : CochainComplex C Int} (f₁ f₂ : K ⟶ mappingCone φ) (α : C
ochain K F 0) (β : Cochain K G (-1)) (h₁ : (Cochain.ofHom f₁).comp (fst φ).1 (ze
ro_add 1) = -δ 0 1 α + (Cochain.ofHom f₂).comp (fst φ).1 (zero_add 1)) (h₂ : (Co
chain.ofHom f₁).comp (snd φ) (zero_add 0) = δ (-1) 0 β + α.comp (Cochain.ofHom φ
) (zero_add 0) + (Cochain.ofHom f₂).comp (snd φ) (zero_add 0)) : Homotopy f₁ f₂
参数：f₁ f₂ : K ⟶ mappingCone φ；α : Cochain K F 0；β : Cochain K G (-1)；h₁ : (Cochai
n.ofHom f₁).comp (fst φ).1 (zero_add 1) = -δ 0 1 α + (Cochain.ofHom f₂).comp (fs
t φ).1 (zero_add 1)；h₂ : (Cochain.ofHom f₁).comp (snd φ) (zero_add 0) = δ (-1) 0
 β + α.comp (Cochain.ofHom φ) (zero_add 0) + (Cochain.ofHom f₂).comp (snd φ) (ze
ro_add 0)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Constructor for homotopies between morphisms to a mapping cone.
-/
noncomputable def liftHomotopy {K : CochainComplex C ℤ} (f₁ f₂ : K ⟶ mappingCone φ)
    (α : Cochain K F 0) (β : Cochain K G (-1))
    (h₁ : (Cochain.ofHom f₁).comp (fst φ).1 (zero_add 1) =
      -δ 0 1 α + (Cochain.ofHom f₂).comp (fst φ).1 (zero_add 1))
    (h₂ : (Cochain.ofHom f₁).comp (snd φ) (zero_add 0) =
      δ (-1) 0 β + α.comp (Cochain.ofHom φ) (zero_add 0) +
        (Cochain.ofHom f₂).comp (snd φ) (zero_add 0)) :
    Homotopy f₁ f₂ :=
  (Cochain.equivHomotopy f₁ f₂).symm ⟨liftCochain φ α β (neg_add_cancel 1), by
    simp [δ_liftCochain _ _ _ _ _ (zero_add 1), ext_cochain_to_iff _ _ _ (zero_add 1), h₁, h₂]⟩

section

variable {K L : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain K F m) (β : Cochain K G n) {n' m' : ℤ} (α' : Cochain F L m') (β' : Cochain G L n')
  (h : n + 1 = m) (h' : m' + 1 = n') (p : ℤ) (hp : n + n' = p)

@[simp]
/-
**CochainComplex.mappingCone.liftCochain_descCochain** 是 Mathlib 中的一个引理，位于命名空间 `
CochainComplex.mappingCone`。
形式化陈述：liftCochain_descCochain : (liftCochain φ α β h).comp (descCochain φ α' β' 
h') hp = α.comp α' (by lia) + β.comp β' (by lia)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
（共 60 条，此处仅展示前 30 条）
-/
lemma liftCochain_descCochain :
    (liftCochain φ α β h).comp (descCochain φ α' β' h') hp =
      α.comp α' (by lia) + β.comp β' (by lia) := by
  simp [liftCochain, descCochain,
    Cochain.comp_assoc α (inl φ) _ _ (show -1 + n' = m' by lia) (by linarith)]
/-
**CochainComplex.mappingCone.liftCochain_v_descCochain_v** 是 Mathlib 中的一个引理，位于命名
空间 `CochainComplex.mappingCone`。
形式化陈述：liftCochain_v_descCochain_v (p₁ p₂ p₃ : Int) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂
 + n' = p₃) (q : Int) (hq : p₁ + m = q) : (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (d
escCochain φ α' β' h').v p₂ p₃ h₂₃ = α.v p₁ q hq ≫ α'.v q p₃ (by omega) + β.v p₁
 p₂ h₁₂ ≫ β'.v p₂ p₃ h₂₃
参数：p₁ p₂ p₃ : Int；h₁₂ : p₁ + n = p₂；h₂₃ : p₂ + n' = p₃；q : Int；hq : p₁ + m = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.congr_v`：congr_v {z₁ z₂ : Cochain F G 
n} (h : z₁ = z₂) (p q : Int) (hpq : p + n = q) : z₁.v p q hpq = z₂.v p q hpq
· 使用引理 `CochainComplex.mappingCone.liftCochain_descCochain`：liftCochain_descCoch
ain : (liftCochain φ α β h).comp (descCochain φ α' β' h') hp = α.comp α' (by lia
) + β.comp β' (by lia)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
-/
lemma liftCochain_v_descCochain_v (p₁ p₂ p₃ : ℤ) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + n' = p₃)
    (q : ℤ) (hq : p₁ + m = q) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (descCochain φ α' β' h').v p₂ p₃ h₂₃ =
      α.v p₁ q hq ≫ α'.v q p₃ (by omega) + β.v p₁ p₂ h₁₂ ≫ β'.v p₂ p₃ h₂₃ := by
  have eq := Cochain.congr_v (liftCochain_descCochain φ α β α' β' h h' p hp) p₁ p₃ (by lia)
  simpa only [Cochain.comp_v _ _ hp p₁ p₂ p₃ h₁₂ h₂₃, Cochain.add_v,
    Cochain.comp_v _ _ _ _ _ _ hq (show q + m' = p₃ by lia)] using eq

end

/-
**CochainComplex.mappingCone.lift_desc_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainCompl
ex.mappingCone`。
形式化陈述：lift_desc_f {K L : CochainComplex C Int} (α : Cocycle K F 1) (β : Cochain 
K G 0) (eq : δ 0 1 β + α.1.comp (Cochain.ofHom φ) (add_zero 1) = 0) (α' : Cochai
n F L (-1)) (β' : G ⟶ L) (eq' : δ (-1) 0 α' = Cochain.ofHom (φ ≫ β')) (n n' : In
t) (hnn' : n + 1 = n') : (lift φ α β eq).f n ≫ (desc φ α' β' eq').f n = α.1.v n 
n' hnn' ≫ α'.v n' n (by omega) + β.v n n (add_zero n) ≫ β'.f n
参数：α : Cocycle K F 1；β : Cochain K G 0；eq : δ 0 1 β + α.1.comp (Cochain.ofHom φ)
 (add_zero 1) = 0；α' : Cochain F L (-1)；β' : G ⟶ L；eq' : δ (-1) 0 α' = Cochain.o
fHom (φ ≫ β')；n n' : Int；hnn' : n + 1 = n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
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
· 使用定理 `CochainComplex.mappingCone.liftCocycle_coe`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `CochainComplex.mappingCone.descCocycle_coe`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `CochainComplex.HomComplex.Cocycle.ofHom_coe`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : C
ochainComplex C ℤ} (φ : F ⟶ G),  …
· 使用引理 `CochainComplex.mappingCone.liftCochain_v_descCochain_v`：liftCochain_v_de
scCochain_v (p₁ p₂ p₃ : Int) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + n' = p₃) (q : Int) 
(hq : p₁ + m = q) : (liftCochain φ α β h).v …
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_desc_f {K L : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + α.1.comp (Cochain.ofHom φ) (add_zero 1) = 0)
    (α' : Cochain F L (-1)) (β' : G ⟶ L)
    (eq' : δ (-1) 0 α' = Cochain.ofHom (φ ≫ β')) (n n' : ℤ) (hnn' : n + 1 = n') :
    (lift φ α β eq).f n ≫ (desc φ α' β' eq').f n =
    α.1.v n n' hnn' ≫ α'.v n' n (by omega) + β.v n n (add_zero n) ≫ β'.f n := by
  simp only [lift, desc, Cocycle.homOf_f, liftCocycle_coe, descCocycle_coe, Cocycle.ofHom_coe,
    liftCochain_v_descCochain_v φ α.1 β α' (Cochain.ofHom β') (zero_add 1) (neg_add_cancel 1) 0
    (add_zero 0) n n n (add_zero n) (add_zero n) n' hnn', Cochain.ofHom_v]


section

open Preadditive Category

variable (H : C ⥤ D) [H.Additive]
  [HasHomotopyCofiber ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `H : C ⥤ D` is an additive functor and `φ` is a morphism of cochain complexes
in `C`, this is the comparison isomorphism (in each degree `n`) between the image
by `H` of `mappingCone φ` and the mapping cone of the image by `H` of `φ`.
It is an auxiliary definition for `mapHomologicalComplexXIso` and
`mapHomologicalComplexIso`. This definition takes an extra
parameter `m : ℤ` such that `n + 1 = m` which may help getting better
definitional properties. See also the equational lemma `mapHomologicalComplexXIso_eq`. -/
@[simps]
/-
**CochainComplex.mappingCone.mapHomologicalComplexXIso'** 是 Mathlib 中的一个定义，位于命名空
间 `CochainComplex.mappingCone`。
形式化陈述：mapHomologicalComplexXIso' (n m : Int) (hnm : n + 1 = m) : ((H.mapHomologi
calComplex (ComplexShape.up Int)).obj (mappingCone φ)).X n ≅ (mappingCone ((H.ma
pHomologicalComplex (ComplexShape.up Int)).map φ)).X n where hom
参数：n m : Int；hnm : n + 1 = m。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
If `H : C ⥤ D` is an additive functor and `φ` is a morphism of cochain complexes
in `C`, this is the comparison isomorphism (in each degree `n`) between the imag
e
by `H` of `mappingCone φ` and the mapping cone of the image by `H` of `φ`.
It is an auxiliary definition for `mapHomologicalComplexXIso` and
`mapHomologicalComplexIso`. This definition takes an extra
parameter `m : ℤ` such that `n + 1 = m` which may help getting better
definitional properties. See also the equational lemma `mapHomologicalComplexXIs
o_eq`.
-/
noncomputable def mapHomologicalComplexXIso' (n m : ℤ) (hnm : n + 1 = m) :
    ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj (mappingCone φ)).X n ≅
      (mappingCone ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).X n where
  hom := H.map ((fst φ).1.v n m (by lia)) ≫
      (inl ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).v m n (by lia) +
      H.map ((snd φ).v n n (add_zero n)) ≫
        (inr ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).f n
  inv := (fst ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).1.v n m (by lia) ≫
      H.map ((inl φ).v m n (by lia)) +
      (snd ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).v n n (add_zero n) ≫
        H.map ((inr φ).f n)
  hom_inv_id := by
    simp only [Functor.mapHomologicalComplex_obj_X, comp_add, add_comp, assoc,
      inl_v_fst_v_assoc, inr_f_fst_v_assoc, zero_comp, comp_zero, add_zero,
      inl_v_snd_v_assoc, inr_f_snd_v_assoc, zero_add, ← Functor.map_comp, ← Functor.map_add]
    rw [← H.map_id]
    congr 1
    simp [ext_from_iff _ _ _ hnm]
  inv_hom_id := by
    simp only [Functor.mapHomologicalComplex_obj_X, comp_add, add_comp, assoc,
      ← H.map_comp_assoc, inl_v_fst_v, CategoryTheory.Functor.map_id, id_comp, inr_f_fst_v,
      inl_v_snd_v, inr_f_snd_v]
    simp [ext_from_iff _ _ _ hnm]

/-- If `H : C ⥤ D` is an additive functor and `φ` is a morphism of cochain complexes
in `C`, this is the comparison isomorphism (in each degree) between the image
by `H` of `mappingCone φ` and the mapping cone of the image by `H` of `φ`. -/
/-
**CochainComplex.mappingCone.mapHomologicalComplexXIso** 是 Mathlib 中的一个定义，位于命名空间
 `CochainComplex.mappingCone`。
形式化陈述：mapHomologicalComplexXIso (n : Int) : ((H.mapHomologicalComplex (ComplexSh
ape.up Int)).obj (mappingCone φ)).X n ≅ (mappingCone ((H.mapHomologicalComplex (
ComplexShape.up Int)).map φ)).X n
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
If `H : C ⥤ D` is an additive functor and `φ` is a morphism of cochain complexes
in `C`, this is the comparison isomorphism (in each degree) between the image
by `H` of `mappingCone φ` and the mapping cone of the image by `H` of `φ`.
-/
noncomputable def mapHomologicalComplexXIso (n : ℤ) :
    ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj (mappingCone φ)).X n ≅
      (mappingCone ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).X n :=
  mapHomologicalComplexXIso' φ H n (n + 1) rfl
/-
**CochainComplex.mappingCone.mapHomologicalComplexXIso_eq** 是 Mathlib 中的一个引理，位于命
名空间 `CochainComplex.mappingCone`。
形式化陈述：mapHomologicalComplexXIso_eq (n m : Int) (hnm : n + 1 = m) : mapHomologica
lComplexXIso φ H n = mapHomologicalComplexXIso' φ H n m hnm
参数：n m : Int；hnm : n + 1 = m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma mapHomologicalComplexXIso_eq (n m : ℤ) (hnm : n + 1 = m) :
    mapHomologicalComplexXIso φ H n = mapHomologicalComplexXIso' φ H n m hnm := by
  subst hnm
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `H : C ⥤ D` is an additive functor and `φ` is a morphism of cochain complexes
in `C`, this is the comparison isomorphism between the image by `H`
of `mappingCone φ` and the mapping cone of the image by `H` of `φ`. -/
/-
**CochainComplex.mappingCone.mapHomologicalComplexIso** 是 Mathlib 中的一个定义，位于命名空间 
`CochainComplex.mappingCone`。
形式化陈述：mapHomologicalComplexIso : (H.mapHomologicalComplex _).obj (mappingCone φ)
 ≅ mappingCone ((H.mapHomologicalComplex _).map φ)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
If `H : C ⥤ D` is an additive functor and `φ` is a morphism of cochain complexes
in `C`, this is the comparison isomorphism between the image by `H`
of `mappingCone φ` and the mapping cone of the image by `H` of `φ`.
-/
noncomputable def mapHomologicalComplexIso :
    (H.mapHomologicalComplex _).obj (mappingCone φ) ≅
      mappingCone ((H.mapHomologicalComplex _).map φ) :=
  HomologicalComplex.Hom.isoOfComponents (mapHomologicalComplexXIso φ H) (by
    rintro n _ rfl
    rw [ext_to_iff _ _ (n + 2) (by lia), assoc, assoc, d_fst_v _ _ _ _ rfl,
      assoc, assoc, d_snd_v _ _ _ rfl]
    simp only [mapHomologicalComplexXIso_eq φ H n (n + 1) rfl,
      mapHomologicalComplexXIso_eq φ H (n + 1) (n + 2) (by lia),
      mapHomologicalComplexXIso'_hom, mapHomologicalComplexXIso'_hom]
    constructor
    · dsimp
      simp only [Functor.mapHomologicalComplex_obj_X, comp_neg, add_comp, assoc, inl_v_fst_v_assoc,
        inr_f_fst_v_assoc, zero_comp, comp_zero, add_zero, inl_v_fst_v, comp_id, inr_f_fst_v,
        ← H.map_comp, d_fst_v φ n (n + 1) (n + 2) rfl (by lia), Functor.map_neg]
    · dsimp
      simp only [comp_add, add_comp, assoc, inl_v_fst_v_assoc, inr_f_fst_v_assoc,
        Functor.mapHomologicalComplex_obj_X, zero_comp, comp_zero, add_zero, inl_v_snd_v_assoc,
        inr_f_snd_v_assoc, zero_add, inl_v_snd_v, inr_f_snd_v, comp_id, ← H.map_comp,
        d_snd_v φ n (n + 1) rfl, Functor.map_add])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.mappingCone.map_inr** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.m
appingCone`。
形式化陈述：map_inr : (H.mapHomologicalComplex (ComplexShape.up Int)).map (inr φ) ≫ (m
apHomologicalComplexIso φ H).hom = inr ((Functor.mapHomologicalComplex H (Comple
xShape.up Int)).map φ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.mappingCone.mapHomologicalComplexXIso_eq`：mapHomologicalC
omplexXIso_eq (n m : Int) (hnm : n + 1 = m) : mapHomologicalComplexXIso φ H n = 
mapHomologicalComplexXIso' φ H n m hnm
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用引理 `CochainComplex.mappingCone.ext_to_iff`：ext_to_iff (i j : Int) (hij : i +
 1 = j) {A : C} (f g : A ⟶ (mappingCone φ).X i) : f = g ↔ f ≫ (fst φ).1.v i j hi
j = g ≫ (fst φ).1.v i j hij…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CochainComplex.mappingCone.inl_v_fst_v`：inl_v_fst_v (p q : Int) (hpq : q
 + 1 = p) : (inl φ).v p q (by rw [← hpq, add_neg_cancel_right]) ≫ (fst φ : Cocha
in (mappingCone φ) F 1).v q …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CochainComplex.mappingCone.inr_f_fst_v`：inr_f_fst_v (p q : Int) (hpq : p
 + 1 = q) : (inr φ).f p ≫ (fst φ).1.v p q hpq = 0
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.mappingCone.inl_v_snd_v`：inl_v_snd_v (p q : Int) (hpq : p
 + (-1) = q) : (inl φ).v p q hpq ≫ (snd φ).v q q (add_zero q) = 0
· 使用引理 `CochainComplex.mappingCone.inr_f_snd_v`：inr_f_snd_v (p : Int) : (inr φ).
f p ≫ (snd φ).v p p (add_zero p) = 𝟙 _
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
（共 31 条，此处仅展示前 30 条）
-/
lemma map_inr :
    (H.mapHomologicalComplex (ComplexShape.up ℤ)).map (inr φ) ≫
      (mapHomologicalComplexIso φ H).hom =
    inr ((Functor.mapHomologicalComplex H (ComplexShape.up ℤ)).map φ) := by
  ext n
  dsimp [mapHomologicalComplexIso]
  simp only [mapHomologicalComplexXIso_eq φ H n (n + 1) rfl, mappingCone.ext_to_iff _ _ _ rfl,
    Functor.mapHomologicalComplex_obj_X, mapHomologicalComplexXIso'_hom, comp_add,
    add_comp, assoc, inl_v_fst_v, comp_id, inr_f_fst_v, comp_zero, add_zero, inl_v_snd_v,
    inr_f_snd_v, zero_add, ← H.map_comp, H.map_zero, H.map_id, and_self]

end

end mappingCone

end CochainComplex

