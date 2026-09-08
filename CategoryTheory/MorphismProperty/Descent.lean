/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer

/-!
# Descent of morphism properties

Given morphism properties `P` and `Q` we say that `P` descends along `Q` (`P.DescendsAlong Q`),
if whenever `Q` holds for `X ⟶ Z`, `P` holds for `X ×[Z] Y ⟶ X` implies `P` holds for `Y ⟶ Z`.
Dually, we define `P.CodescendsAlong Q`.
-/

public section

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type*} [Category* C]

variable {P Q W : MorphismProperty C}

/-- `P` descends along `Q` if whenever `Q` holds for `X ⟶ Z`,
`P` holds for `X ×[Z] Y ⟶ X` implies `P` holds for `Y ⟶ Z`. -/
/-
**CategoryTheory.MorphismProperty.DescendsAlong** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.MorphismProperty C → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P` descends along `Q` if whenever `Q` holds for `X ⟶ Z`,
`P` holds for `X ×[Z] Y ⟶ X` implies `P` holds for `Y ⟶ Z`.
-/
class DescendsAlong (P Q : MorphismProperty C) : Prop where
  of_isPullback {A X Y Z : C} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} :
    IsPullback fst snd f g → Q f → P fst → P g

section DescendsAlong

variable {A X Y Z : C} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-
**CategoryTheory.MorphismProperty.of_isPullback_of_descendsAlong** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：of_isPullback_of_descendsAlong [P.DescendsAlong Q] (h : IsPullback fst snd
 f g) (hf : Q f) (hfst : P fst) : P g
参数：h : IsPullback fst snd f g；hf : Q f；hfst : P fst。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.DescendsAlong.of_isPullback`：∀ {C : Type
 u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P Q : CategoryTheory.Morphi
smProperty C}   [self : P.DescendsAlong Q] {A X Y…
-/
lemma of_isPullback_of_descendsAlong [P.DescendsAlong Q] (h : IsPullback fst snd f g)
    (hf : Q f) (hfst : P fst) : P g :=
  DescendsAlong.of_isPullback h hf hfst
/-
**CategoryTheory.MorphismProperty.iff_of_isPullback** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：iff_of_isPullback [P.IsStableUnderBaseChange] [P.DescendsAlong Q] (h : IsP
ullback fst snd f g) (hf : Q f) : P fst ↔ P g
参数：h : IsPullback fst snd f g；hf : Q f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_isPullback_of_descendsAlong`：of_isPul
lback_of_descendsAlong [P.DescendsAlong Q] (h : IsPullback fst snd f g) (hf : Q 
f) (hfst : P fst) : P g
· 使用定理 `CategoryTheory.MorphismProperty.of_isPullback`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self 
: P.IsStableUnderBaseChange] {X Y Y…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
-/
lemma iff_of_isPullback [P.IsStableUnderBaseChange] [P.DescendsAlong Q] (h : IsPullback fst snd f g)
    (hf : Q f) : P fst ↔ P g :=
  ⟨fun hfst ↦ of_isPullback_of_descendsAlong h hf hfst, fun hf ↦ P.of_isPullback h.flip hf⟩
/-
**CategoryTheory.MorphismProperty.of_pullback_fst_of_descendsAlong** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：of_pullback_fst_of_descendsAlong [P.DescendsAlong Q] [HasPullback f g] (hf
 : Q f) (hfst : P (pullback.fst f g)) : P g
参数：hf : Q f；hfst : P (pullback.fst f g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_isPullback_of_descendsAlong`：of_isPul
lback_of_descendsAlong [P.DescendsAlong Q] (h : IsPullback fst snd f g) (hf : Q 
f) (hfst : P fst) : P g
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
lemma of_pullback_fst_of_descendsAlong [P.DescendsAlong Q] [HasPullback f g] (hf : Q f)
    (hfst : P (pullback.fst f g)) : P g :=
  of_isPullback_of_descendsAlong (.of_hasPullback f g) hf hfst
/-
**CategoryTheory.MorphismProperty.pullback_fst_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：pullback_fst_iff [P.IsStableUnderBaseChange] [P.DescendsAlong Q] [HasPullb
ack f g] (hf : Q f) : P (pullback.fst f g) ↔ P g
参数：hf : Q f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.iff_of_isPullback`：iff_of_isPullback [P.
IsStableUnderBaseChange] [P.DescendsAlong Q] (h : IsPullback fst snd f g) (hf : 
Q f) : P fst ↔ P g
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
lemma pullback_fst_iff [P.IsStableUnderBaseChange] [P.DescendsAlong Q] [HasPullback f g]
    (hf : Q f) : P (pullback.fst f g) ↔ P g :=
  iff_of_isPullback (.of_hasPullback f g) hf
/-
**CategoryTheory.MorphismProperty.of_pullback_snd_of_descendsAlong** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：of_pullback_snd_of_descendsAlong [P.DescendsAlong Q] [HasPullback f g] (hg
 : Q g) (hsnd : P (pullback.snd f g)) : P f
参数：hg : Q g；hsnd : P (pullback.snd f g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_isPullback_of_descendsAlong`：of_isPul
lback_of_descendsAlong [P.DescendsAlong Q] (h : IsPullback fst snd f g) (hf : Q 
f) (hfst : P fst) : P g
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
lemma of_pullback_snd_of_descendsAlong [P.DescendsAlong Q] [HasPullback f g] (hg : Q g)
    (hsnd : P (pullback.snd f g)) : P f :=
  of_isPullback_of_descendsAlong (IsPullback.of_hasPullback f g).flip hg hsnd
/-
**CategoryTheory.MorphismProperty.pullback_snd_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：pullback_snd_iff [P.IsStableUnderBaseChange] [P.DescendsAlong Q] [HasPullb
ack f g] (hg : Q g) : P (pullback.snd f g) ↔ P f
参数：hg : Q g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.iff_of_isPullback`：iff_of_isPullback [P.
IsStableUnderBaseChange] [P.DescendsAlong Q] (h : IsPullback fst snd f g) (hf : 
Q f) : P fst ↔ P g
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
lemma pullback_snd_iff [P.IsStableUnderBaseChange] [P.DescendsAlong Q] [HasPullback f g]
    (hg : Q g) : P (pullback.snd f g) ↔ P f :=
  iff_of_isPullback (IsPullback.of_hasPullback f g).flip hg
/-
**CategoryTheory.MorphismProperty.DescendsAlong.top** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MorphismProperty.DescendsAlong`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {Q : Catego
ryTheory.MorphismProperty C},   ⊤.DescendsAlong Q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
instance DescendsAlong.top : (⊤ : MorphismProperty C).DescendsAlong Q where
  of_isPullback _ _ _ := trivial
/-
**CategoryTheory.MorphismProperty.DescendsAlong.inf** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MorphismProperty.DescendsAlong`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P Q W : Ca
tegoryTheory.MorphismProperty C}   [P.DescendsAlong Q] [W.DescendsAlong Q], (P ⊓
 W).DescendsAlong Q
参数：P ⊓ W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.DescendsAlong.of_isPullback`：∀ {C : Type
 u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P Q : CategoryTheory.Morphi
smProperty C}   [self : P.DescendsAlong Q] {A X Y…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance DescendsAlong.inf [P.DescendsAlong Q] [W.DescendsAlong Q] : (P ⊓ W).DescendsAlong Q where
  of_isPullback h hg hfst :=
    ⟨DescendsAlong.of_isPullback h hg hfst.1, DescendsAlong.of_isPullback h hg hfst.2⟩
/-
**CategoryTheory.MorphismProperty.DescendsAlong.of_le** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MorphismProperty.DescendsAlong`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P Q W : Ca
tegoryTheory.MorphismProperty C}   [P.DescendsAlong Q], W ≤ Q → P.DescendsAlong 
W
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.DescendsAlong.of_isPullback`：∀ {C : Type
 u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P Q : CategoryTheory.Morphi
smProperty C}   [self : P.DescendsAlong Q] {A X Y…
-/
lemma DescendsAlong.of_le [P.DescendsAlong Q] (hle : W ≤ Q) : P.DescendsAlong W where
  of_isPullback h hg hfst := DescendsAlong.of_isPullback h (hle _ hg) hfst

/-- Alternative constructor for `CodescendsAlong` using `HasPullback`. -/
/-
**CategoryTheory.MorphismProperty.DescendsAlong.mk'** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MorphismProperty.DescendsAlong`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P Q : Cate
goryTheory.MorphismProperty C}   [P.RespectsIso],   (∀ {X Y Z : C} {f : X ⟶ Z} {
g : Y ⟶ Z} [inst_2 : CategoryTheory.Limits.HasPullback f g],       Q f → P (Cate
goryTheory.Limits.pullback.fst f g) → P g) →     P.DescendsAlong Q
参数：∀ {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [inst_2 : CategoryTheory.Limits.HasPull
back f g],       Q f → P (CategoryTheory.Limits.pullback.fst f g) → P g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.hasPullback`：hasPullback (h : IsPullback fst s
nd f g) : HasPullback f g where exists_limit
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_fst`：isoPullback_hom_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.fst _ _
 = fst

--- 原说明 ---
Alternative constructor for `CodescendsAlong` using `HasPullback`.
-/
lemma DescendsAlong.mk' [P.RespectsIso]
    (H : ∀ {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g],
      Q f → P (pullback.fst f g) → P g) :
    P.DescendsAlong Q where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    have : HasPullback f g := h.hasPullback
    apply H hf
    rwa [← P.cancel_left_of_respectsIso h.isoPullback.hom, h.isoPullback_hom_fst]
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Q.IsStableUnderBaseChange] [P.HasOfPrecompProperty Q] [P.RespectsRight Q] :
    P.DescendsAlong Q where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    apply P.of_precomp (W' := Q) _ _ (Q.of_isPullback h hf)
    rw [← h.1.1]
    exact RespectsRight.postcomp _ hf _ hfst

set_option backward.isDefEq.respectTransparency false in
/-- If `P` descends along `Q`, then `P.diagonal` descends along `Q`. -/
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` descends along `Q`, then `P.diagonal` descends along `Q`.
-/
instance [HasPullbacks C] (P Q : MorphismProperty C) [P.DescendsAlong Q] [P.RespectsIso]
    [Q.IsStableUnderBaseChange] :
    DescendsAlong (diagonal P) Q := by
  apply DescendsAlong.mk'
  introv hf hfst
  have heq : pullback.fst (pullback.fst (pullback.snd g g ≫ g) f) (pullback.diagonal g) =
      (pullbackSymmetry _ _).hom ≫
      (pullbackRightPullbackFstIso _ _ _).hom ≫
      (pullback.congrHom (by simp) rfl).hom ≫
      (pullbackSymmetry _ _).hom ≫
      pullback.diagonal (pullback.fst f g) ≫
      (diagonalObjPullbackFstIso f g).hom := by
    apply pullback.hom_ext
    apply pullback.hom_ext <;> simp [pullback.condition]
    simp [pullback.condition]
  rw [diagonal_iff]
  apply MorphismProperty.of_pullback_fst_of_descendsAlong (P := P) (Q := Q)
      (f := pullback.fst (pullback.snd g g ≫ g) f)
  · exact MorphismProperty.pullback_fst _ _ hf
  · rw [heq]
    iterate 4 rw [cancel_left_of_respectsIso (P := P)]
    rwa [cancel_right_of_respectsIso (P := P)]
/-
**CategoryTheory.MorphismProperty.eq_of_isomorphisms_descendsAlong** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：eq_of_isomorphisms_descendsAlong [(MorphismProperty.isomorphisms C).Descen
dsAlong P] [P.IsStableUnderBaseChange] [HasEqualizers C] [HasPullbacks C] {X Y S
 T : C} {f g : X ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S} (hf : f ≫ t = s) (hg : g ≫ t = s) 
(v : T ⟶ S) (hv : P v) (H : pullback.map s v t v f (𝟙 T) (𝟙 S) (by simp [hf]) (b
y simp) = pullback.map s v t v g (𝟙 T) (𝟙 S) (by simp [hg]) (by simp)) : f = g
参数：MorphismProperty.isomorphisms C；hf : f ≫ t = s；hg : g ≫ t = s；v : T ⟶ S；hv : 
P v；H : pullback.map s v t v f (𝟙 T) (𝟙 S) (by simp [hf]) (by simp) = pullback.m
ap s v t v g (𝟙 T) (𝟙 S) (by simp [hg]) (by simp)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.MorphismProperty.of_isPullback_of_descendsAlong`：of_isPul
lback_of_descendsAlong [P.DescendsAlong Q] (h : IsPullback fst snd f g) (hf : Q 
f) (hfst : P fst) : P g
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `CategoryTheory.MorphismProperty.pullback_fst`：pullback_fst {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong f] (H :
 P g) : P (pullback.fst f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Limits.equalizerPullbackMapIso_inv_ι_fst`：equalizerPullba
ckMapIso_inv_ι_fst : (equalizerPullbackMapIso hf hg v).inv ≫ equalizer.ι _ _ ≫ p
ullback.fst _ _ = pullback.fst _ _ ≫ equalize…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Limits.equalizerPullbackMapIso_inv_ι_snd`：equalizerPullba
ckMapIso_inv_ι_snd : (equalizerPullbackMapIso hf hg v).inv ≫ equalizer.ι _ _ ≫ p
ullback.snd _ _ = pullback.snd _ _ ≫ pullback…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.equalizer.ι_of_eq`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g],   f = …
· 使用定理 `CategoryTheory.Limits.eq_of_epi_equalizer`：eq_of_epi_equalizer [HasEqual
izer f g] [Epi (equalizer.ι f g)] : f = g
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
-/
lemma eq_of_isomorphisms_descendsAlong [(MorphismProperty.isomorphisms C).DescendsAlong P]
    [P.IsStableUnderBaseChange] [HasEqualizers C]
    [HasPullbacks C] {X Y S T : C} {f g : X ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S} (hf : f ≫ t = s)
    (hg : g ≫ t = s) (v : T ⟶ S) (hv : P v)
    (H :
      pullback.map s v t v f (𝟙 T) (𝟙 S) (by simp [hf]) (by simp) =
        pullback.map s v t v g (𝟙 T) (𝟙 S) (by simp [hg]) (by simp)) :
    f = g := by
  suffices IsIso (equalizer.ι f g) from Limits.eq_of_epi_equalizer
  change MorphismProperty.isomorphisms C _
  apply (MorphismProperty.isomorphisms C).of_isPullback_of_descendsAlong
    (IsPullback.of_hasPullback _ _).flip (P.pullback_fst s v hv)
  have : pullback.snd (equalizer.ι f g) (pullback.fst s v) =
      (equalizerPullbackMapIso hf hg _).inv ≫ equalizer.ι _ _ := by
    ext <;> simp [pullback.condition]
  simpa [this] using equalizer.ι_of_eq H

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.faithful_overPullback_of_isomorphisms_descendA
long** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：faithful_overPullback_of_isomorphisms_descendAlong [(MorphismProperty.isom
orphisms C).DescendsAlong P] [P.IsStableUnderBaseChange] [HasPullbacks C] [HasEq
ualizers C] {S T : C} {f : T ⟶ S} (hf : P f) : (Over.pullback f).Faithful
参数：MorphismProperty.isomorphisms C；hf : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用引理 `CategoryTheory.MorphismProperty.eq_of_isomorphisms_descendsAlong`：eq_of_
isomorphisms_descendsAlong [(MorphismProperty.isomorphisms C).DescendsAlong P] [
P.IsStableUnderBaseChange] [HasEqualizers C] [HasPullb…
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Over.pullback_map_left`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.
HasPullbacksAlong f] (g : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma faithful_overPullback_of_isomorphisms_descendAlong
    [(MorphismProperty.isomorphisms C).DescendsAlong P] [P.IsStableUnderBaseChange]
    [HasPullbacks C] [HasEqualizers C] {S T : C} {f : T ⟶ S} (hf : P f) :
    (Over.pullback f).Faithful := by
  refine ⟨fun {X} Y a b hab ↦ ?_⟩
  ext
  apply P.eq_of_isomorphisms_descendsAlong (Over.w a) (Over.w b) f hf
  convert! congr($(hab).left) <;> ext <;> simp

end DescendsAlong

/-- `P` codescends along `Q` if whenever `Q` holds for `Z ⟶ X`,
`P` holds for `X ⟶ X ∐[Z] Y` implies `P` holds for `Z ⟶ Y`. -/
/-
**CategoryTheory.MorphismProperty.CodescendsAlong** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.MorphismProperty C → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P` codescends along `Q` if whenever `Q` holds for `Z ⟶ X`,
`P` holds for `X ⟶ X ∐[Z] Y` implies `P` holds for `Z ⟶ Y`.
-/
class CodescendsAlong (P Q : MorphismProperty C) : Prop where
  of_isPushout {Z X Y A : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ A} {inr : Y ⟶ A} :
    IsPushout f g inl inr → Q f → P inl → P g

section CodescendsAlong

variable {Z X Y A : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ A} {inr : Y ⟶ A}

/-
**CategoryTheory.MorphismProperty.of_isPushout_of_codescendsAlong** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：of_isPushout_of_codescendsAlong [P.CodescendsAlong Q] (h : IsPushout f g i
nl inr) (hf : Q f) (hinl : P inl) : P g
参数：h : IsPushout f g inl inr；hf : Q f；hinl : P inl。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.CodescendsAlong.of_isPushout`：∀ {C : Typ
e u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P Q : CategoryTheory.Morph
ismProperty C}   [self : P.CodescendsAlong Q] {Z X…
-/
lemma of_isPushout_of_codescendsAlong [P.CodescendsAlong Q] (h : IsPushout f g inl inr)
    (hf : Q f) (hinl : P inl) : P g :=
  CodescendsAlong.of_isPushout h hf hinl
/-
**CategoryTheory.MorphismProperty.iff_of_isPushout** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：iff_of_isPushout [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q] (h : 
IsPushout f g inl inr) (hg : Q f) : P inl ↔ P g
参数：h : IsPushout f g inl inr；hg : Q f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_isPushout_of_codescendsAlong`：of_isPu
shout_of_codescendsAlong [P.CodescendsAlong Q] (h : IsPushout f g inl inr) (hf :
 Q f) (hinl : P inl) : P g
· 使用定理 `CategoryTheory.MorphismProperty.of_isPushout`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self :
 P.IsStableUnderCobaseChange] {A A…
-/
lemma iff_of_isPushout [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q]
    (h : IsPushout f g inl inr) (hg : Q f) : P inl ↔ P g :=
  ⟨fun hinl ↦ of_isPushout_of_codescendsAlong h hg hinl, fun hf ↦ P.of_isPushout h hf⟩
/-
**CategoryTheory.MorphismProperty.of_pushout_inl_of_codescendsAlong** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：of_pushout_inl_of_codescendsAlong [P.CodescendsAlong Q] [HasPushout f g] (
hf : Q f) (hinl : P (pushout.inl f g)) : P g
参数：hf : Q f；hinl : P (pushout.inl f g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_isPushout_of_codescendsAlong`：of_isPu
shout_of_codescendsAlong [P.CodescendsAlong Q] (h : IsPushout f g inl inr) (hf :
 Q f) (hinl : P inl) : P g
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
-/
lemma of_pushout_inl_of_codescendsAlong [P.CodescendsAlong Q] [HasPushout f g] (hf : Q f)
    (hinl : P (pushout.inl f g)) : P g :=
  of_isPushout_of_codescendsAlong (.of_hasPushout f g) hf hinl
/-
**CategoryTheory.MorphismProperty.pushout_inl_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：pushout_inl_iff [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q] [HasPu
shout f g] (hf : Q f) : P (pushout.inl f g) ↔ P g
参数：hf : Q f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.iff_of_isPushout`：iff_of_isPushout [P.Is
StableUnderCobaseChange] [P.CodescendsAlong Q] (h : IsPushout f g inl inr) (hg :
 Q f) : P inl ↔ P g
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
-/
lemma pushout_inl_iff [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q] [HasPushout f g]
    (hf : Q f) : P (pushout.inl f g) ↔ P g :=
  iff_of_isPushout (.of_hasPushout f g) hf
/-
**CategoryTheory.MorphismProperty.of_pushout_inr_of_descendsAlong** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：of_pushout_inr_of_descendsAlong [P.CodescendsAlong Q] [HasPushout f g] (hg
 : Q g) (hinr : P (pushout.inr f g)) : P f
参数：hg : Q g；hinr : P (pushout.inr f g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_isPushout_of_codescendsAlong`：of_isPu
shout_of_codescendsAlong [P.CodescendsAlong Q] (h : IsPushout f g inl inr) (hf :
 Q f) (hinl : P inl) : P g
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
-/
lemma of_pushout_inr_of_descendsAlong [P.CodescendsAlong Q] [HasPushout f g] (hg : Q g)
    (hinr : P (pushout.inr f g)) : P f :=
  of_isPushout_of_codescendsAlong (IsPushout.of_hasPushout f g).flip hg hinr
/-
**CategoryTheory.MorphismProperty.pushout_inr_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：pushout_inr_iff [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q] [HasPu
shout f g] (hg : Q g) : P (pushout.inr f g) ↔ P f
参数：hg : Q g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.iff_of_isPushout`：iff_of_isPushout [P.Is
StableUnderCobaseChange] [P.CodescendsAlong Q] (h : IsPushout f g inl inr) (hg :
 Q f) : P inl ↔ P g
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
-/
lemma pushout_inr_iff [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q] [HasPushout f g]
    (hg : Q g) : P (pushout.inr f g) ↔ P f :=
  iff_of_isPushout (IsPushout.of_hasPushout f g).flip hg
/-
**CategoryTheory.MorphismProperty.CodescendsAlong.of_le** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.MorphismProperty.CodescendsAlong`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P Q W : Ca
tegoryTheory.MorphismProperty C}   [P.CodescendsAlong Q], W ≤ Q → P.CodescendsAl
ong W
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.CodescendsAlong.of_isPushout`：∀ {C : Typ
e u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P Q : CategoryTheory.Morph
ismProperty C}   [self : P.CodescendsAlong Q] {Z X…
-/
lemma CodescendsAlong.of_le [P.CodescendsAlong Q] (hle : W ≤ Q) : P.CodescendsAlong W where
  of_isPushout h hg hinl := CodescendsAlong.of_isPushout h (hle _ hg) hinl
/-
**CategoryTheory.MorphismProperty.CodescendsAlong.top** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MorphismProperty.CodescendsAlong`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {Q : Catego
ryTheory.MorphismProperty C},   ⊤.CodescendsAlong Q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
instance CodescendsAlong.top : (⊤ : MorphismProperty C).CodescendsAlong Q where
  of_isPushout _ _ _ := trivial
/-
**CategoryTheory.MorphismProperty.CodescendsAlong.inf** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MorphismProperty.CodescendsAlong`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P Q W : Ca
tegoryTheory.MorphismProperty C}   [P.CodescendsAlong Q] [W.CodescendsAlong Q], 
(P ⊓ W).CodescendsAlong Q
参数：P ⊓ W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.CodescendsAlong.of_isPushout`：∀ {C : Typ
e u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {P Q : CategoryTheory.Morph
ismProperty C}   [self : P.CodescendsAlong Q] {Z X…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance CodescendsAlong.inf [P.CodescendsAlong Q] [W.CodescendsAlong Q] :
    (P ⊓ W).CodescendsAlong Q where
  of_isPushout h hg hfst :=
    ⟨CodescendsAlong.of_isPushout h hg hfst.1, CodescendsAlong.of_isPushout h hg hfst.2⟩

/-- Alternative constructor for `CodescendsAlong` using `HasPushout`. -/
/-
**CategoryTheory.MorphismProperty.CodescendsAlong.mk'** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MorphismProperty.CodescendsAlong`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P Q : Cate
goryTheory.MorphismProperty C}   [P.RespectsIso],   (∀ {X Y Z : C} {f : Z ⟶ X} {
g : Z ⟶ Y} [inst_2 : CategoryTheory.Limits.HasPushout f g],       Q f → P (Categ
oryTheory.Limits.pushout.inl f g) → P g) →     P.CodescendsAlong Q
参数：∀ {X Y Z : C} {f : Z ⟶ X} {g : Z ⟶ Y} [inst_2 : CategoryTheory.Limits.HasPush
out f g],       Q f → P (CategoryTheory.Limits.pushout.inl f g) → P g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.hasPushout`：hasPushout (h : IsPushout f g inl i
nr) : HasPushout f g where exists_colimit
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.IsPushout.inl_isoPushout_inv`：inl_isoPushout_inv (h : IsP
ushout f g inl inr) [HasPushout f g] : pushout.inl _ _ ≫ h.isoPushout.inv = inl

--- 原说明 ---
Alternative constructor for `CodescendsAlong` using `HasPushout`.
-/
lemma CodescendsAlong.mk' [P.RespectsIso]
    (H : ∀ {X Y Z : C} {f : Z ⟶ X} {g : Z ⟶ Y} [HasPushout f g], Q f → P (pushout.inl f g) → P g) :
    P.CodescendsAlong Q where
  of_isPushout {A X Y Z f g inl inr} h hf hfst := by
    have : HasPushout f g := h.hasPushout
    apply H hf
    rwa [← P.cancel_right_of_respectsIso _ h.isoPushout.inv, h.inl_isoPushout_inv]
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Q.IsStableUnderCobaseChange] [P.HasOfPostcompProperty Q] [P.RespectsLeft Q] :
    P.CodescendsAlong Q where
  of_isPushout {X Y Z A f g inl inr} h hf hinl := by
    apply P.of_postcomp (W' := Q) g inr (Q.of_isPushout h.flip hf)
    rw [← h.1.1]
    exact RespectsLeft.precomp _ hf _ hinl

end CodescendsAlong

end CategoryTheory.MorphismProperty

