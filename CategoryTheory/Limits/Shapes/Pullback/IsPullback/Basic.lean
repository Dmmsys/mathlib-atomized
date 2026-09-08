/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Pullback and pushout squares

We restate some results about pullbacks/pushouts in the language of `IsPullback` and `IsPushout`,
among which the pasting lemmas
-/

@[expose] public section

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

namespace IsPullback

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `c` is a limiting binary product cone, and we have a terminal object,
then we have `IsPullback c.fst c.snd 0 0`
(where each `0` is the unique morphism to the terminal object). -/
/-
**CategoryTheory.IsPullback.of_is_product** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.IsPullback`。
形式化陈述：of_is_product {c : BinaryFan X Y} (h : Limits.IsLimit c) (t : IsTerminal Z
) : IsPullback c.fst c.snd (t.from _) (t.from _)
参数：h : Limits.IsLimit c；t : IsTerminal Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_isLimit`：of_isLimit {c : PullbackCone f g} 
(h : Limits.IsLimit c) : IsPullback c.fst c.snd f g
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `c` is a limiting binary product cone, and we have a terminal object,
then we have `IsPullback c.fst c.snd 0 0`
(where each `0` is the unique morphism to the terminal object).
-/
theorem of_is_product {c : BinaryFan X Y} (h : Limits.IsLimit c) (t : IsTerminal Z) :
    IsPullback c.fst c.snd (t.from _) (t.from _) :=
  of_isLimit
    (isPullbackOfIsTerminalIsProduct _ _ _ _ t
      (IsLimit.ofIsoLimit h
        (Limits.Cone.ext (Iso.refl c.pt)
          (by
            rintro ⟨⟨⟩⟩ <;> simp))))

/-- A variant of `of_is_product` that is more useful with `apply`. -/
/-
**CategoryTheory.IsPullback.of_is_product'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.IsPullback`。
形式化陈述：of_is_product' (h : Limits.IsLimit (BinaryFan.mk fst snd)) (t : IsTerminal
 Z) : IsPullback fst snd (t.from _) (t.from _)
参数：h : Limits.IsLimit (BinaryFan.mk fst snd)；t : IsTerminal Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_is_product`：of_is_product {c : BinaryFan X 
Y} (h : Limits.IsLimit c) (t : IsTerminal Z) : IsPullback c.fst c.snd (t.from _)
 (t.from _)

--- 原说明 ---
A variant of `of_is_product` that is more useful with `apply`.
-/
theorem of_is_product' (h : Limits.IsLimit (BinaryFan.mk fst snd)) (t : IsTerminal Z) :
    IsPullback fst snd (t.from _) (t.from _) :=
  of_is_product h t

variable (X Y) in
/-
**CategoryTheory.IsPullback.of_hasBinaryProduct'** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.IsPullback`。
形式化陈述：of_hasBinaryProduct' [HasBinaryProduct X Y] [HasTerminal C] : IsPullback L
imits.prod.fst Limits.prod.snd (terminal.from X) (terminal.from Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_is_product`：of_is_product {c : BinaryFan X 
Y} (h : Limits.IsLimit c) (t : IsTerminal Z) : IsPullback c.fst c.snd (t.from _)
 (t.from _)
-/
theorem of_hasBinaryProduct' [HasBinaryProduct X Y] [HasTerminal C] :
    IsPullback Limits.prod.fst Limits.prod.snd (terminal.from X) (terminal.from Y) :=
  of_is_product (limit.isLimit _) terminalIsTerminal
/-
**CategoryTheory.IsPullback.of_iso_pullback** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.IsPullback`。
形式化陈述：of_iso_pullback (h : CommSq fst snd f g) [HasPullback f g] (i : P ≅ pullba
ck f g) (w₁ : i.hom ≫ pullback.fst _ _ = fst) (w₂ : i.hom ≫ pullback.snd _ _ = s
nd) : IsPullback fst snd f g
参数：h : CommSq fst snd f g；i : P ≅ pullback f g；w₁ : i.hom ≫ pullback.fst _ _ = f
st；w₂ : i.hom ≫ pullback.snd _ _ = snd。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_isLimit'`：of_isLimit' (w : CommSq fst snd f
 g) (h : Limits.IsLimit w.cone) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem of_iso_pullback (h : CommSq fst snd f g) [HasPullback f g] (i : P ≅ pullback f g)
    (w₁ : i.hom ≫ pullback.fst _ _ = fst) (w₂ : i.hom ≫ pullback.snd _ _ = snd) :
      IsPullback fst snd f g :=
  of_isLimit' h
    (Limits.IsLimit.ofIsoLimit (limit.isLimit _)
      (@PullbackCone.ext _ _ _ _ _ _ _ (PullbackCone.mk _ _ _) _ i w₁.symm w₂.symm).symm)
/-
**CategoryTheory.IsPullback.of_horiz_isIso_mono** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.IsPullback`。
形式化陈述：of_horiz_isIso_mono [IsIso fst] [Mono g] (sq : CommSq fst snd f g) : IsPul
lback fst snd f g
参数：sq : CommSq fst snd f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_isLimit'`：of_isLimit' (w : CommSq fst snd f
 g) (h : Limits.IsLimit w.cone) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
-/
theorem of_horiz_isIso_mono [IsIso fst] [Mono g] (sq : CommSq fst snd f g) :
    IsPullback fst snd f g :=
  of_isLimit' sq
    (by
      refine
        PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ inv fst) (by simp)
          (fun s => ?_) (by cat_disch)
      simp only [← cancel_mono g, Category.assoc, ← sq.w, IsIso.inv_hom_id_assoc, s.condition])
/-
**CategoryTheory.IsPullback.of_horiz_isIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.IsPullback`。
形式化陈述：of_horiz_isIso [IsIso fst] [IsIso g] (sq : CommSq fst snd f g) : IsPullbac
k fst snd f g
参数：sq : CommSq fst snd f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_horiz_isIso_mono`：of_horiz_isIso_mono [IsIs
o fst] [Mono g] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
-/
theorem of_horiz_isIso [IsIso fst] [IsIso g] (sq : CommSq fst snd f g) :
    IsPullback fst snd f g :=
  of_horiz_isIso_mono sq
/-
**CategoryTheory.IsPullback.of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsP
ullback`。
形式化陈述：of_iso (h : IsPullback fst snd f g) {P' X' Y' Z' : C} {fst' : P' ⟶ X'} {sn
d' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} (e₁ : P ≅ P') (e₂ : X ≅ X') (e₃ : Y 
≅ Y') (e₄ : Z ≅ Z') (commfst : fst ≫ e₂.hom = e₁.hom ≫ fst') (commsnd : snd ≫ e₃
.hom = e₁.hom ≫ snd') (commf : f ≫ e₄.hom = e₂.hom ≫ f') (commg : g ≫ e₄.hom = e
₃.hom ≫ g') : IsPullback fst' snd' f' g' where w
参数：h : IsPullback fst snd f g；e₁ : P ≅ P'；e₂ : X ≅ X'；e₃ : Y ≅ Y'；e₄ : Z ≅ Z'；co
mmfst : fst ≫ e₂.hom = e₁.hom ≫ fst'；commsnd : snd ≫ e₃.hom = e₁.hom ≫ snd'；comm
f : f ≫ e₄.hom = e₂.hom ≫ f'；commg : g ≫ e₄.hom = e₃.hom ≫ g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.CommSq.w_assoc`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y
 ⟶ Z},   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma of_iso (h : IsPullback fst snd f g)
    {P' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (e₁ : P ≅ P') (e₂ : X ≅ X') (e₃ : Y ≅ Y') (e₄ : Z ≅ Z')
    (commfst : fst ≫ e₂.hom = e₁.hom ≫ fst')
    (commsnd : snd ≫ e₃.hom = e₁.hom ≫ snd')
    (commf : f ≫ e₄.hom = e₂.hom ≫ f')
    (commg : g ≫ e₄.hom = e₃.hom ≫ g') :
    IsPullback fst' snd' f' g' where
  w := by
    rw [← cancel_epi e₁.hom, ← reassoc_of% commfst, ← commf,
      ← reassoc_of% commsnd, ← commg, h.w_assoc]
  isLimit' :=
    ⟨(IsLimit.postcomposeInvEquiv
        (cospanExt e₂ e₃ e₄ commf.symm commg.symm) _).1
          (IsLimit.ofIsoLimit h.isLimit (by
            refine PullbackCone.ext e₁ ?_ ?_
            · change fst = e₁.hom ≫ fst' ≫ e₂.inv
              rw [← reassoc_of% commfst, e₂.hom_inv_id, Category.comp_id]
            · change snd = e₁.hom ≫ snd' ≫ e₃.inv
              rw [← reassoc_of% commsnd, e₃.hom_inv_id, Category.comp_id]))⟩

/-- Same as `IsPullback.of_iso`, but using the data and compatibilities involving
the inverse isomorphisms instead. -/
/-
**CategoryTheory.IsPullback.of_iso'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Is
Pullback`。
形式化陈述：of_iso' (h : IsPullback fst snd f g) {P' X' Y' Z' : C} {fst' : P' ⟶ X'} {s
nd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} (e₁ : P' ≅ P) (e₂ : X' ≅ X) (e₃ : Y
' ≅ Y) (e₄ : Z' ≅ Z) (commfst : e₁.hom ≫ fst = fst' ≫ e₂.hom) (commsnd : e₁.hom 
≫ snd = snd' ≫ e₃.hom) (commf : e₂.hom ≫ f = f' ≫ e₄.hom) (commg : e₃.hom ≫ g = 
g' ≫ e₄.hom) : IsPullback fst' snd' f' g'
参数：h : IsPullback fst snd f g；e₁ : P' ≅ P；e₂ : X' ≅ X；e₃ : Y' ≅ Y；e₄ : Z' ≅ Z；co
mmfst : e₁.hom ≫ fst = fst' ≫ e₂.hom；commsnd : e₁.hom ≫ snd = snd' ≫ e₃.hom；comm
f : e₂.hom ≫ f = f' ≫ e₄.hom；commg : e₃.hom ≫ g = g' ≫ e₄.hom。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.of_iso`：of_iso (h : IsPullback fst snd f g) {P
' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} 
(e₁ : P ≅ P') (e₂ : X …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Same as `IsPullback.of_iso`, but using the data and compatibilities involving
the inverse isomorphisms instead.
-/
lemma of_iso' (h : IsPullback fst snd f g)
    {P' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (e₁ : P' ≅ P) (e₂ : X' ≅ X) (e₃ : Y' ≅ Y) (e₄ : Z' ≅ Z)
    (commfst : e₁.hom ≫ fst = fst' ≫ e₂.hom)
    (commsnd : e₁.hom ≫ snd = snd' ≫ e₃.hom)
    (commf : e₂.hom ≫ f = f' ≫ e₄.hom)
    (commg : e₃.hom ≫ g = g' ≫ e₄.hom) :
    IsPullback fst' snd' f' g' := by
  apply h.of_iso e₁.symm e₂.symm e₃.symm e₄.symm
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commfst, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commsnd, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commf, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commg, Iso.inv_hom_id_assoc]

section

variable {P X Y : C} {fst : P ⟶ X} {snd : P ⟶ X} {f : X ⟶ Y}

/-
**CategoryTheory.IsPullback.isIso_fst_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.IsPullback`。
形式化陈述：isIso_fst_of_mono (h : IsPullback fst snd f f) (inst : Mono f
参数：h : IsPullback fst snd f f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.isIso_fst_of_mono_of_isLimit`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [Categor
yTheory.Mono f]   {t : CategoryTheory.Limits.Pullback…
-/
lemma isIso_fst_of_mono (h : IsPullback fst snd f f) (inst : Mono f := by infer_instance) :
    IsIso fst := h.cone.isIso_fst_of_mono_of_isLimit h.isLimit
/-
**CategoryTheory.IsPullback.isIso_snd_iso_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.IsPullback`。
形式化陈述：isIso_snd_iso_of_mono (h : IsPullback fst snd f f) (inst : Mono f
参数：h : IsPullback fst snd f f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.isIso_snd_of_mono_of_isLimit`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [Categor
yTheory.Mono f]   {t : CategoryTheory.Limits.Pullback…
-/
lemma isIso_snd_iso_of_mono (h : IsPullback fst snd f f) (inst : Mono f := by infer_instance) :
    IsIso snd := h.cone.isIso_snd_of_mono_of_isLimit h.isLimit

end

section

/-
**CategoryTheory.IsPullback.mono_fst_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.IsPullback`。
形式化陈述：mono_fst_of_mono (h : IsPullback fst snd f g) (inst : Mono g
参数：h : IsPullback fst snd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.hom_ext`：hom_ext (hP : IsPullback fst snd f g)
 {W : C} {k l : W ⟶ P} (h₀ : k ≫ fst = l ≫ fst) (h₁ : k ≫ snd = l ≫ snd) : k = l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mono_fst_of_mono (h : IsPullback fst snd f g) (inst : Mono g := by infer_instance) :
    Mono fst := by
  constructor
  intro W fst' snd' heq
  exact h.hom_ext heq (by simp [← cancel_mono g, ← h.w, reassoc_of% heq])
/-
**CategoryTheory.IsPullback.mono_snd_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.IsPullback`。
形式化陈述：mono_snd_of_mono (h : IsPullback fst snd f g) (inst : Mono f
参数：h : IsPullback fst snd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.mono_fst_of_mono`：mono_fst_of_mono (h : IsPull
back fst snd f g) (inst : Mono g
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
-/
lemma mono_snd_of_mono (h : IsPullback fst snd f g) (inst : Mono f := by infer_instance) :
    Mono snd :=
  h.flip.mono_fst_of_mono
/-
**CategoryTheory.IsPullback.isIso_fst_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.IsPullback`。
形式化陈述：isIso_fst_of_isIso (h : IsPullback fst snd f g) (inst : IsIso g
参数：h : IsPullback fst snd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.hasPullback`：hasPullback (h : IsPullback fst s
nd f g) : HasPullback f g where exists_limit
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_fst`：isoPullback_hom_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.fst _ _
 = fst
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma isIso_fst_of_isIso (h : IsPullback fst snd f g) (inst : IsIso g := by infer_instance) :
    IsIso fst := by
  have := h.hasPullback
  rw [← h.isoPullback_hom_fst]
  infer_instance
/-
**CategoryTheory.IsPullback.isIso_snd_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.IsPullback`。
形式化陈述：isIso_snd_of_isIso (h : IsPullback fst snd f g) (inst : IsIso f
参数：h : IsPullback fst snd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.isIso_fst_of_isIso`：isIso_fst_of_isIso (h : Is
Pullback fst snd f g) (inst : IsIso g
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
-/
lemma isIso_snd_of_isIso (h : IsPullback fst snd f g) (inst : IsIso f := by infer_instance) :
    IsIso snd :=
  h.flip.isIso_fst_of_isIso

end

section
-- Objects here are arranged in a 3x2 grid, and indexed by their xy coordinates.
-- Morphisms are named `hᵢⱼ` for a horizontal morphism starting at `(i,j)`,
-- and `vᵢⱼ` for a vertical morphism starting at `(i,j)`.
/-- Paste two pullback squares "vertically" to obtain another pullback square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
/-
**CategoryTheory.IsPullback.paste_vert** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.IsPullback`。
形式化陈述：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂
₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ 
: X₂₂ ⟶ X₃₂} (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) :
 IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁
参数：s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁；t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_isLimit`：of_isLimit {c : PullbackCone f g} 
(h : Limits.IsLimit c) : IsPullback c.fst c.snd f g

--- 原说明 ---
Paste two pullback squares "vertically" to obtain another pullback square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
theorem paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) :
    IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
  of_isLimit (pasteHorizIsPullback rfl t.isLimit s.isLimit)

/-- Paste two pullback squares "horizontally" to obtain another pullback square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
/-
**CategoryTheory.IsPullback.paste_horiz** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.IsPullback`。
形式化陈述：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X
₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃
 : X₁₃ ⟶ X₂₃} (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) 
: IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)
参数：s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁；t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…

--- 原说明 ---
Paste two pullback squares "horizontally" to obtain another pullback square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
theorem paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
  (paste_vert s.flip t.flip).flip

/-- Given a pullback square assembled from a commuting square on the top and
a pullback square on the bottom, the top square is a pullback square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
/-
**CategoryTheory.IsPullback.of_bot** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsP
ullback`。
形式化陈述：of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {
h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂
₂ ⟶ X₃₂} (s : IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫
 h₂₁) (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) : IsPullback h₁₁ v₁₁ v₁₂ h₂₁
参数：s : IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁；p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁；t : 
IsPullback h₂₁ v₂₁ v₂₂ h₃₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_isLimit`：of_isLimit {c : PullbackCone f g} 
(h : Limits.IsLimit c) : IsPullback c.fst c.snd f g

--- 原说明 ---
Given a pullback square assembled from a commuting square on the top and
a pullback square on the bottom, the top square is a pullback square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
theorem of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁)
    (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) : IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  of_isLimit (leftSquareIsPullback (PullbackCone.mk h₁₁ _ p) rfl t.isLimit s.isLimit)

/-- Given a pullback square assembled from a commuting square on the left and
a pullback square on the right, the left square is a pullback square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
/-
**CategoryTheory.IsPullback.of_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.I
sPullback`。
形式化陈述：of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
 {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : 
X₁₃ ⟶ X₂₃} (s : IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₁ ≫ v₁₂ = v₁₁
 ≫ h₂₁) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) : IsPullback h₁₁ v₁₁ v₁₂ h₂₁
参数：s : IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)；p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁；t : 
IsPullback h₁₂ v₁₂ v₁₃ h₂₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.of_bot`：of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {
h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁
₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given a pullback square assembled from a commuting square on the left and
a pullback square on the right, the left square is a pullback square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
theorem of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁)
    (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) : IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  (of_bot s.flip p.symm t.flip).flip
/-
**CategoryTheory.IsPullback.paste_vert_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.IsPullback`。
形式化陈述：paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ 
⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {
v₂₂ : X₂₂ ⟶ X₃₂} (s : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) (e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) : 
IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ ↔ IsPullback h₁₁ v₁₁ v₁₂ h₂₁
参数：s : IsPullback h₂₁ v₂₁ v₂₂ h₃₁；e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_bot`：of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {
h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁
₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ …
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
-/
theorem paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) (e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) :
    IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ ↔ IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  ⟨fun h => h.of_bot e s, fun h => h.paste_vert s⟩
/-
**CategoryTheory.IsPullback.paste_horiz_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.IsPullback`。
形式化陈述：paste_horiz_iff {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂
 ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} 
{v₁₃ : X₁₃ ⟶ X₂₃} (s : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) (e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) :
 IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) ↔ IsPullback h₁₁ v₁₁ v₁₂ h₂₁
参数：s : IsPullback h₁₂ v₁₂ v₁₃ h₂₂；e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_right`：of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : 
C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ 
: X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ …
· 使用定理 `CategoryTheory.IsPullback.paste_horiz`：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ 
X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
 {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X…
-/
theorem paste_horiz_iff {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) (e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) :
    IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) ↔ IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  ⟨fun h => h.of_right e s, fun h => h.paste_horiz s⟩

/-- Variant of `IsPullback.of_right` where `h₁₁` is induced from a morphism `h₁₃ : X₁₁ ⟶ X₁₃`, and
the universal property of the right square.

The objects fit in the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
/-
**CategoryTheory.IsPullback.of_right'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
IsPullback`。
形式化陈述：of_right' {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂
} {h₂₂ : X₂₂ ⟶ X₂₃} {h₁₃ : X₁₁ ⟶ X₁₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ :
 X₁₃ ⟶ X₂₃} (s : IsPullback h₁₃ v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (t : IsPullback h₁₂ v₁₂ v₁₃
 h₂₂) : IsPullback (t.lift h₁₃ (v₁₁ ≫ h₂₁) (by rw [s.w, Category.assoc])) v₁₁ v₁
₂ h₂₁
参数：s : IsPullback h₁₃ v₁₁ v₁₃ (h₂₁ ≫ h₂₂)；t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_right`：of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : 
C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ 
: X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.IsPullback.lift_fst`：lift_fst (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ fst = h
· 使用引理 `CategoryTheory.IsPullback.lift_snd`：lift_snd (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ snd = k

--- 原说明 ---
Variant of `IsPullback.of_right` where `h₁₁` is induced from a morphism `h₁₃ : X
₁₁ ⟶ X₁₃`, and
the universal property of the right square.

The objects fit in the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
theorem of_right' {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {h₁₃ : X₁₁ ⟶ X₁₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback h₁₃ v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPullback (t.lift h₁₃ (v₁₁ ≫ h₂₁) (by rw [s.w, Category.assoc])) v₁₁ v₁₂ h₂₁ :=
  of_right ((t.lift_fst _ _ _) ▸ s) (t.lift_snd _ _ _) t

/-- Variant of `IsPullback.of_bot`, where `v₁₁` is induced from a morphism `v₃₁ : X₁₁ ⟶ X₃₁`, and
the universal property of the bottom square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
/-
**CategoryTheory.IsPullback.of_bot'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
Pullback`。
形式化陈述：of_bot' {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} 
{h₃₁ : X₃₁ ⟶ X₃₂} {v₃₁ : X₁₁ ⟶ X₃₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X
₂₂ ⟶ X₃₂} (s : IsPullback h₁₁ v₃₁ (v₁₂ ≫ v₂₂) h₃₁) (t : IsPullback h₂₁ v₂₁ v₂₂ h
₃₁) : IsPullback h₁₁ (t.lift (h₁₁ ≫ v₁₂) v₃₁ (by rw [Category.assoc, s.w])) v₁₂ 
h₂₁
参数：s : IsPullback h₁₁ v₃₁ (v₁₂ ≫ v₂₂) h₃₁；t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_bot`：of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {
h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁
₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.IsPullback.lift_snd`：lift_snd (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ snd = k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.IsPullback.lift_fst`：lift_fst (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ fst = h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Variant of `IsPullback.of_bot`, where `v₁₁` is induced from a morphism `v₃₁ : X₁
₁ ⟶ X₃₁`, and
the universal property of the bottom square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
theorem of_bot' {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₃₁ : X₁₁ ⟶ X₃₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₁₁ v₃₁ (v₁₂ ≫ v₂₂) h₃₁) (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) :
    IsPullback h₁₁ (t.lift (h₁₁ ≫ v₁₂) v₃₁ (by rw [Category.assoc, s.w])) v₁₂ h₂₁ :=
  of_bot ((t.lift_snd _ _ _) ▸ s) (by simp only [lift_fst]) t
/-
**CategoryTheory.IsPullback.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsPullbac
k`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasPullbacksAlong f] (h : P ⟶ Y) : HasPullback h (pullback.fst g f) :=
  IsPullback.hasPullback (IsPullback.of_bot' (IsPullback.of_hasPullback (h ≫ g) f)
    (IsPullback.of_hasPullback g f))
/-
**CategoryTheory.IsPullback.of_vert_isIso_mono** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.IsPullback`。
形式化陈述：of_vert_isIso_mono [IsIso snd] [Mono f] (sq : CommSq fst snd f g) : IsPull
back fst snd f g
参数：sq : CommSq fst snd f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.of_horiz_isIso_mono`：of_horiz_isIso_mono [IsIs
o fst] [Mono g] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.CommSq.flip`：flip (p : CommSq f g h i) : CommSq g f i h
-/
theorem of_vert_isIso_mono [IsIso snd] [Mono f] (sq : CommSq fst snd f g) :
    IsPullback fst snd f g :=
  IsPullback.flip (of_horiz_isIso_mono sq.flip)
/-
**CategoryTheory.IsPullback.of_vert_isIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.IsPullback`。
形式化陈述：of_vert_isIso [IsIso snd] [IsIso f] (sq : CommSq fst snd f g) : IsPullback
 fst snd f g
参数：sq : CommSq fst snd f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso_mono`：of_vert_isIso_mono [IsIso 
snd] [Mono f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
-/
theorem of_vert_isIso [IsIso snd] [IsIso f] (sq : CommSq fst snd f g) :
    IsPullback fst snd f g :=
  of_vert_isIso_mono sq
/-
**CategoryTheory.IsPullback.of_id_fst** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
IsPullback`。
形式化陈述：of_id_fst : IsPullback (𝟙 _) f f (𝟙 _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_horiz_isIso`：of_horiz_isIso [IsIso fst] [Is
Iso g] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma of_id_fst : IsPullback (𝟙 _) f f (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
/-
**CategoryTheory.IsPullback.of_id_snd** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
IsPullback`。
形式化陈述：of_id_snd : IsPullback f (𝟙 _) (𝟙 _) f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso`：of_vert_isIso [IsIso snd] [IsIs
o f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma of_id_snd : IsPullback f (𝟙 _) (𝟙 _) f := IsPullback.of_vert_isIso ⟨by simp⟩

/-- The following diagram is a pullback
```
X --f--> Z
|        |
id       id
v        v
X --f--> Z
```
-/
/-
**CategoryTheory.IsPullback.id_vert** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Is
Pullback`。
形式化陈述：id_vert (f : X ⟶ Z) : IsPullback f (𝟙 X) (𝟙 Z) f
参数：f : X ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso`：of_vert_isIso [IsIso snd] [IsIs
o f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The following diagram is a pullback
```
X --f--> Z
|        |
id       id
v        v
X --f--> Z
```
-/
lemma id_vert (f : X ⟶ Z) : IsPullback f (𝟙 X) (𝟙 Z) f :=
  of_vert_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

/-- The following diagram is a pullback
```
X --id--> X
|         |
f         f
v         v
Z --id--> Z
```
-/
/-
**CategoryTheory.IsPullback.id_horiz** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.I
sPullback`。
形式化陈述：id_horiz (f : X ⟶ Z) : IsPullback (𝟙 X) f f (𝟙 Z)
参数：f : X ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_horiz_isIso`：of_horiz_isIso [IsIso fst] [Is
Iso g] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The following diagram is a pullback
```
X --id--> X
|         |
f         f
v         v
Z --id--> Z
```
-/
lemma id_horiz (f : X ⟶ Z) : IsPullback (𝟙 X) f f (𝟙 Z) :=
  of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
In a category, given a morphism `f : A ⟶ B` and an object `X`,
this is the obvious pullback diagram:
```
A ⨯ X ⟶ A
  |     |
  v     v
B ⨯ X ⟶ B
```
-/
/-
**CategoryTheory.IsPullback.of_prod_fst_with_id** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.IsPullback`。
形式化陈述：of_prod_fst_with_id {A B : C} (f : A ⟶ B) (X : C) [HasBinaryProduct A X] [
HasBinaryProduct B X] : IsPullback prod.fst (prod.map f (𝟙 X)) f prod.fst where 
isLimit'
参数：f : A ⟶ B；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…

--- 原说明 ---
In a category, given a morphism `f : A ⟶ B` and an object `X`,
this is the obvious pullback diagram:
```
A ⨯ X ⟶ A
  |     |
  v     v
B ⨯ X ⟶ B
```
-/
lemma of_prod_fst_with_id {A B : C} (f : A ⟶ B) (X : C) [HasBinaryProduct A X]
    [HasBinaryProduct B X] :
    IsPullback prod.fst (prod.map f (𝟙 X)) f prod.fst where
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    refine ⟨prod.lift s.fst (s.snd ≫ prod.snd), ?_, ?_, ?_⟩
    · simp
    · ext
      · simp [PullbackCone.condition]
      · simp
    · intro m h₁ h₂
      dsimp at m h₁ h₂ ⊢
      ext
      · simpa using h₁
      · simp [← h₂])⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsPullback.of_isLimit_binaryFan_of_isTerminal** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.IsPullback`。
形式化陈述：of_isLimit_binaryFan_of_isTerminal {X Y : C} {c : BinaryFan X Y} (hc : IsL
imit c) {T : C} (hT : IsTerminal T) : IsPullback c.fst c.snd (hT.from _) (hT.fro
m _) where isLimit'
参数：hc : IsLimit c；hT : IsTerminal T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsTerminal.comp_from`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {Z : C} (t : CategoryTheory.Limits.IsTerminal Z)
 {X Y : C}   (f : X ⟶ Y), Catego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.BinaryFan.IsLimit.lift_fst`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X Y W : C} {s : CategoryTheory.Limits.Binary
Fan X Y}   (h : CategoryTheory.Limits.…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.Limits.BinaryFan.IsLimit.lift_snd`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X Y W : C} {s : CategoryTheory.Limits.Binary
Fan X Y}   (h : CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Limits.BinaryFan.IsLimit.hom_ext`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.BinaryF
an X Y}   (h : CategoryTheory.Limits.…
-/
lemma of_isLimit_binaryFan_of_isTerminal
    {X Y : C} {c : BinaryFan X Y} (hc : IsLimit c)
    {T : C} (hT : IsTerminal T) :
    IsPullback c.fst c.snd (hT.from _) (hT.from _) where
  isLimit' := ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ BinaryFan.IsLimit.lift hc s.fst s.snd) (by simp) (by simp)
    (fun s m h₁ h₂ ↦ by apply BinaryFan.IsLimit.hom_ext hc <;> cat_disch)⟩
end

/-
**CategoryTheory.IsPullback.mk'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsPull
back`。
形式化陈述：mk' {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (w :
 fst ≫ f = snd ≫ g) (hom_ext : forall ⦃T : C⦄ ⦃φ φ' : T ⟶ P⦄ (_ : φ ≫ fst = φ' ≫
 fst) (_ : φ ≫ snd = φ' ≫ snd), φ = φ') (exists_lift : forall ⦃T : C⦄ (a : T ⟶ X
) (b : T ⟶ Y) (_ : a ≫ f = b ≫ g), exists (l : T ⟶ P), l ≫ fst = a ∧ l ≫ snd = b
) : IsPullback fst snd f g where w
参数：w : fst ≫ f = snd ≫ g；hom_ext : forall ⦃T : C⦄ ⦃φ φ' : T ⟶ P⦄ (_ : φ ≫ fst = 
φ' ≫ fst) (_ : φ ≫ snd = φ' ≫ snd), φ = φ'；exists_lift : forall ⦃T : C⦄ (a : T ⟶
 X) (b : T ⟶ Y) (_ : a ≫ f = b ≫ g), exists (l : T ⟶ P), l ≫ fst = a ∧ l ≫ snd =
 b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mk' {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (w : fst ≫ f = snd ≫ g)
    (hom_ext : ∀ ⦃T : C⦄ ⦃φ φ' : T ⟶ P⦄ (_ : φ ≫ fst = φ' ≫ fst)
      (_ : φ ≫ snd = φ' ≫ snd), φ = φ')
    (exists_lift : ∀ ⦃T : C⦄ (a : T ⟶ X) (b : T ⟶ Y)
      (_ : a ≫ f = b ≫ g), ∃ (l : T ⟶ P), l ≫ fst = a ∧ l ≫ snd = b) :
    IsPullback fst snd f g where
  w := w
  isLimit' := by
    let l (s : PullbackCone f g) := exists_lift _ _ s.condition
    exact ⟨PullbackCone.IsLimit.mk _
      (fun s ↦ (l s).choose)
      (fun s ↦ (l s).choose_spec.1)
      (fun s ↦ (l s).choose_spec.2)
      (fun s m h₁ h₂ ↦ hom_ext
        (h₁.trans (l s).choose_spec.1.symm)
        (h₂.trans (l s).choose_spec.2.symm))⟩

/--
The main objects in this lemma fit in the following commutative diagram:
```
Pfg -------> X <------- Pfi
 |           |           |
 |           f           |
 ↓           ↓           ↓
 Y --- g --> S <-- i --- Z
  \                     /
    --              --
       \          /
         --  R --
```
Suppose the two squares are cartesian, then `Pfg ×[Y] R` is the pullback of
`Pfi ⟶ Z` and `R ⟶ Z`.
-/
/-
**CategoryTheory.IsPullback.paste_twist_right** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.IsPullback`。
形式化陈述：paste_twist_right {X Y Z S : C} {f : X ⟶ S} {g : Y ⟶ S} {i : Z ⟶ S} {Pfg :
 C} {fstfg : Pfg ⟶ X} {sndfg : Pfg ⟶ Y} (hfg : IsPullback fstfg sndfg f g) {Pfi 
: C} {fstfi : Pfi ⟶ X} {sndfi : Pfi ⟶ Z} (hfi : IsPullback fstfi sndfi f i) {R :
 C} (rY : R ⟶ Y) (rZ : R ⟶ Z) (hrw : rY ≫ g = rZ ≫ i) {Psndfgr : C} (fstsndfgr :
 Psndfgr ⟶ Pfg) (sndsndfgr : Psndfgr ⟶ R) (hsndfgr : IsPullback fstsndfgr sndsnd
fgr sndfg rY) {t : Psndfgr ⟶ Pfi} (ht₁ : t ≫ fstfi = fstsndfgr ≫ fstfg) (ht₂ : t
 ≫ sndfi = sndsndfgr ≫ rZ)
参数：hfg : IsPullback fstfg sndfg f g；hfi : IsPullback fstfi sndfi f i；rY : R ⟶ Y；
rZ : R ⟶ Z；hrw : rY ≫ g = rZ ≫ i；fstsndfgr : Psndfgr ⟶ Pfg；sndsndfgr : Psndfgr ⟶
 R；hsndfgr : IsPullback fstsndfgr sndsndfgr sndfg rY；ht₁ : t ≫ fstfi = fstsndfgr
 ≫ fstfg；ht₂ : t ≫ sndfi = sndsndfgr ≫ rZ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_right`：of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : 
C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ 
: X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPullback.paste_horiz`：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ 
X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
 {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X…

--- 原说明 ---
The main objects in this lemma fit in the following commutative diagram:
```
Pfg -------> X <------- Pfi
 |           |           |
 |           f           |
 ↓           ↓           ↓
 Y --- g --> S <-- i --- Z
  \                     /
    --              --
       \          /
         --  R --
```
Suppose the two squares are cartesian, then `Pfg ×[Y] R` is the pullback of
`Pfi ⟶ Z` and `R ⟶ Z`.
-/
lemma paste_twist_right {X Y Z S : C} {f : X ⟶ S} {g : Y ⟶ S} {i : Z ⟶ S}
    {Pfg : C} {fstfg : Pfg ⟶ X} {sndfg : Pfg ⟶ Y} (hfg : IsPullback fstfg sndfg f g)
    {Pfi : C} {fstfi : Pfi ⟶ X} {sndfi : Pfi ⟶ Z} (hfi : IsPullback fstfi sndfi f i)
    {R : C} (rY : R ⟶ Y) (rZ : R ⟶ Z) (hrw : rY ≫ g = rZ ≫ i)
    {Psndfgr : C} (fstsndfgr : Psndfgr ⟶ Pfg) (sndsndfgr : Psndfgr ⟶ R)
    (hsndfgr : IsPullback fstsndfgr sndsndfgr sndfg rY)
    {t : Psndfgr ⟶ Pfi} (ht₁ : t ≫ fstfi = fstsndfgr ≫ fstfg) (ht₂ : t ≫ sndfi = sndsndfgr ≫ rZ) :
    IsPullback t sndsndfgr sndfi rZ := by
  refine .of_right ?_ ht₂ hfi
  rw [← hrw, ht₁]
  exact .paste_horiz hsndfgr hfg

set_option backward.isDefEq.respectTransparency false in
/-- This is a `HasPullback` variant of `CategoryTheory.IsPullback.paste_twist_right` -/
/-
**CategoryTheory.IsPullback.map_fst_comp_fst_snd_comp_fst** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.IsPullback`。
形式化陈述：map_fst_comp_fst_snd_comp_fst {X Y Z U S : C} (f : X ⟶ S) (g : Y ⟶ S) (i :
 Z ⟶ S) [HasPullback i g] (h : U ⟶ pullback i g) [HasPullback f g] [HasPullback 
(pullback.snd f g) (h ≫ pullback.snd i g)] [HasPullback f i] : IsPullback (pullb
ack.map (pullback.snd f g) (h ≫ pullback.snd i g) f i (pullback.fst f g) (h ≫ pu
llback.fst i g) g pullback.condition.symm (by simp [pullback.condition])) (pullb
ack.snd (pullback.snd f g) (h ≫ pullback.snd i g)) (pullback.snd f i) (h ≫ pullb
ack.fst i g)
参数：f : X ⟶ S；g : Y ⟶ S；i : Z ⟶ S；h : U ⟶ pullback i g；pullback.snd f g；h ≫ pullb
ack.snd i g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.paste_twist_right`：paste_twist_right {X Y Z S 
: C} {f : X ⟶ S} {g : Y ⟶ S} {i : Z ⟶ S} {Pfg : C} {fstfg : Pfg ⟶ X} {sndfg : Pf
g ⟶ Y} (hfg : IsPullback fstfg sn…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …

--- 原说明 ---
This is a `HasPullback` variant of `CategoryTheory.IsPullback.paste_twist_right`
-/
lemma map_fst_comp_fst_snd_comp_fst {X Y Z U S : C} (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ S)
    [HasPullback i g] (h : U ⟶ pullback i g) [HasPullback f g] [HasPullback (pullback.snd f g)
    (h ≫ pullback.snd i g)] [HasPullback f i] :
    IsPullback
      (pullback.map (pullback.snd f g) (h ≫ pullback.snd i g) f i (pullback.fst f g)
        (h ≫ pullback.fst i g) g
        pullback.condition.symm (by simp [pullback.condition]))
      (pullback.snd (pullback.snd f g) (h ≫ pullback.snd i g))
      (pullback.snd f i)
      (h ≫ pullback.fst i g) :=
  paste_twist_right (.of_hasPullback f g) (.of_hasPullback f i) (h ≫ pullback.snd _ _)
    (h ≫ pullback.fst _ _) (by simp [pullback.condition]) _ _ (.of_hasPullback _ _) (by simp)
    (by simp)

end IsPullback
namespace IsPushout

variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `c` is a colimiting binary coproduct cocone, and we have an initial object,
then we have `IsPushout 0 0 c.inl c.inr`
(where each `0` is the unique morphism from the initial object). -/
/-
**CategoryTheory.IsPushout.of_is_coproduct** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.IsPushout`。
形式化陈述：of_is_coproduct {c : BinaryCofan X Y} (h : Limits.IsColimit c) (t : IsInit
ial Z) : IsPushout (t.to _) (t.to _) c.inl c.inr
参数：h : Limits.IsColimit c；t : IsInitial Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_isColimit`：of_isColimit {c : PushoutCocone f
 g} (h : Limits.IsColimit c) : IsPushout f g c.inl c.inr
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `c` is a colimiting binary coproduct cocone, and we have an initial object,
then we have `IsPushout 0 0 c.inl c.inr`
(where each `0` is the unique morphism from the initial object).
-/
theorem of_is_coproduct {c : BinaryCofan X Y} (h : Limits.IsColimit c) (t : IsInitial Z) :
    IsPushout (t.to _) (t.to _) c.inl c.inr :=
  of_isColimit
    (isPushoutOfIsInitialIsCoproduct _ _ _ _ t
      (IsColimit.ofIsoColimit h
        (Limits.Cocone.ext (Iso.refl c.pt)
          (by
            rintro ⟨⟨⟩⟩ <;> simp))))

/-- A variant of `of_is_coproduct` that is more useful with `apply`. -/
/-
**CategoryTheory.IsPushout.of_is_coproduct'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.IsPushout`。
形式化陈述：of_is_coproduct' (h : Limits.IsColimit (BinaryCofan.mk inl inr)) (t : IsIn
itial Z) : IsPushout (t.to _) (t.to _) inl inr
参数：h : Limits.IsColimit (BinaryCofan.mk inl inr)；t : IsInitial Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_is_coproduct`：of_is_coproduct {c : BinaryCof
an X Y} (h : Limits.IsColimit c) (t : IsInitial Z) : IsPushout (t.to _) (t.to _)
 c.inl c.inr

--- 原说明 ---
A variant of `of_is_coproduct` that is more useful with `apply`.
-/
theorem of_is_coproduct' (h : Limits.IsColimit (BinaryCofan.mk inl inr)) (t : IsInitial Z) :
    IsPushout (t.to _) (t.to _) inl inr :=
  of_is_coproduct h t

variable (X Y) in
/-
**CategoryTheory.IsPushout.of_hasBinaryCoproduct'** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.IsPushout`。
形式化陈述：of_hasBinaryCoproduct' [HasBinaryCoproduct X Y] [HasInitial C] : IsPushout
 (initial.to _) (initial.to _) (coprod.inl : X ⟶ _) (coprod.inr : Y ⟶ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_is_coproduct`：of_is_coproduct {c : BinaryCof
an X Y} (h : Limits.IsColimit c) (t : IsInitial Z) : IsPushout (t.to _) (t.to _)
 c.inl c.inr
-/
theorem of_hasBinaryCoproduct' [HasBinaryCoproduct X Y] [HasInitial C] :
    IsPushout (initial.to _) (initial.to _) (coprod.inl : X ⟶ _) (coprod.inr : Y ⟶ _) :=
  of_is_coproduct (colimit.isColimit _) initialIsInitial
/-
**CategoryTheory.IsPushout.of_iso_pushout** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.IsPushout`。
形式化陈述：of_iso_pushout (h : CommSq f g inl inr) [HasPushout f g] (i : P ≅ pushout 
f g) (w₁ : inl ≫ i.hom = pushout.inl _ _) (w₂ : inr ≫ i.hom = pushout.inr _ _) :
 IsPushout f g inl inr
参数：h : CommSq f g inl inr；i : P ≅ pushout f g；w₁ : inl ≫ i.hom = pushout.inl _ _
；w₂ : inr ≫ i.hom = pushout.inr _ _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_isColimit'`：of_isColimit' (w : CommSq f g in
l inr) (h : Limits.IsColimit w.cocone) : IsPushout f g inl inr
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
-/
theorem of_iso_pushout (h : CommSq f g inl inr) [HasPushout f g] (i : P ≅ pushout f g)
    (w₁ : inl ≫ i.hom = pushout.inl _ _) (w₂ : inr ≫ i.hom = pushout.inr _ _) :
      IsPushout f g inl inr :=
  of_isColimit' h
    (Limits.IsColimit.ofIsoColimit (colimit.isColimit _)
      (PushoutCocone.ext (s := PushoutCocone.mk ..) i w₁ w₂).symm)
/-
**CategoryTheory.IsPushout.of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsPu
shout`。
形式化陈述：of_iso (h : IsPushout f g inl inr) {Z' X' Y' P' : C} {f' : Z' ⟶ X'} {g' : 
Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'} (e₁ : Z ≅ Z') (e₂ : X ≅ X') (e₃ : Y ≅
 Y') (e₄ : P ≅ P') (commf : f ≫ e₂.hom = e₁.hom ≫ f') (commg : g ≫ e₃.hom = e₁.h
om ≫ g') (comminl : inl ≫ e₄.hom = e₂.hom ≫ inl') (comminr : inr ≫ e₄.hom = e₃.h
om ≫ inr') : IsPushout f' g' inl' inr' where w
参数：h : IsPushout f g inl inr；e₁ : Z ≅ Z'；e₂ : X ≅ X'；e₃ : Y ≅ Y'；e₄ : P ≅ P'；com
mf : f ≫ e₂.hom = e₁.hom ≫ f'；commg : g ≫ e₃.hom = e₁.hom ≫ g'；comminl : inl ≫ e
₄.hom = e₂.hom ≫ inl'；comminr : inr ≫ e₄.hom = e₃.hom ≫ inr'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.CommSq.w_assoc`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y
 ⟶ Z},   CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
-/
lemma of_iso (h : IsPushout f g inl inr)
    {Z' X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'}
    (e₁ : Z ≅ Z') (e₂ : X ≅ X') (e₃ : Y ≅ Y') (e₄ : P ≅ P')
    (commf : f ≫ e₂.hom = e₁.hom ≫ f')
    (commg : g ≫ e₃.hom = e₁.hom ≫ g')
    (comminl : inl ≫ e₄.hom = e₂.hom ≫ inl')
    (comminr : inr ≫ e₄.hom = e₃.hom ≫ inr') :
    IsPushout f' g' inl' inr' where
  w := by
    rw [← cancel_epi e₁.hom, ← reassoc_of% commf, ← comminl,
      ← reassoc_of% commg, ← comminr, h.w_assoc]
  isColimit' :=
    ⟨(IsColimit.precomposeHomEquiv
        (spanExt e₁ e₂ e₃ commf.symm commg.symm) _).1
          (IsColimit.ofIsoColimit h.isColimit
            (PushoutCocone.ext e₄ comminl comminr))⟩

/-- Same as `IsPushout.of_iso`, but using the data and compatibilities involving
the inverse isomorphisms instead. -/
/-
**CategoryTheory.IsPushout.of_iso'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsP
ushout`。
形式化陈述：of_iso' {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} 
(h : IsPushout f g inl inr) {Z' X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl
' : X' ⟶ P'} {inr' : Y' ⟶ P'} (e₁ : Z' ≅ Z) (e₂ : X' ≅ X) (e₃ : Y' ≅ Y) (e₄ : P'
 ≅ P) (commf : e₁.hom ≫ f = f' ≫ e₂.hom) (commg : e₁.hom ≫ g = g' ≫ e₃.hom) (com
minl : e₂.hom ≫ inl = inl' ≫ e₄.hom) (comminr : e₃.hom ≫ inr = inr' ≫ e₄.hom) : 
IsPushout f' g' inl' inr'
参数：h : IsPushout f g inl inr；e₁ : Z' ≅ Z；e₂ : X' ≅ X；e₃ : Y' ≅ Y；e₄ : P' ≅ P；com
mf : e₁.hom ≫ f = f' ≫ e₂.hom；commg : e₁.hom ≫ g = g' ≫ e₃.hom；comminl : e₂.hom 
≫ inl = inl' ≫ e₄.hom；comminr : e₃.hom ≫ inr = inr' ≫ e₄.hom。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.of_iso`：of_iso (h : IsPushout f g inl inr) {Z' 
X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'} (e
₁ : Z ≅ Z') (e₂ : X ≅…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Same as `IsPushout.of_iso`, but using the data and compatibilities involving
the inverse isomorphisms instead.
-/
lemma of_iso' {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (h : IsPushout f g inl inr)
    {Z' X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'}
    (e₁ : Z' ≅ Z) (e₂ : X' ≅ X) (e₃ : Y' ≅ Y) (e₄ : P' ≅ P)
    (commf : e₁.hom ≫ f = f' ≫ e₂.hom)
    (commg : e₁.hom ≫ g = g' ≫ e₃.hom)
    (comminl : e₂.hom ≫ inl = inl' ≫ e₄.hom)
    (comminr : e₃.hom ≫ inr = inr' ≫ e₄.hom) :
    IsPushout f' g' inl' inr' := by
  apply h.of_iso e₁.symm e₂.symm e₃.symm e₄.symm
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commf, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commg, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← comminl, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← comminr, Iso.inv_hom_id_assoc]

section

variable {P X Y : C} {inl : X ⟶ P} {inr : X ⟶ P} {f : Y ⟶ X}

/-
**CategoryTheory.IsPushout.isIso_inl_iso_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.IsPushout`。
形式化陈述：isIso_inl_iso_of_epi (h : IsPushout f f inl inr) (inst : Epi f
参数：h : IsPushout f f inl inr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.isIso_inl_of_epi_of_isColimit`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [Categ
oryTheory.Epi f]   {t : CategoryTheory.Limits.PushoutCo…
-/
lemma isIso_inl_iso_of_epi (h : IsPushout f f inl inr) (inst : Epi f := by infer_instance) :
    IsIso inl := h.cocone.isIso_inl_of_epi_of_isColimit h.isColimit
/-
**CategoryTheory.IsPushout.isIso_inr_iso_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.IsPushout`。
形式化陈述：isIso_inr_iso_of_epi (h : IsPushout f f inl inr) (inst : Epi f
参数：h : IsPushout f f inl inr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.isIso_inr_of_epi_of_isColimit`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [Categ
oryTheory.Epi f]   {t : CategoryTheory.Limits.PushoutCo…
-/
lemma isIso_inr_iso_of_epi (h : IsPushout f f inl inr) (inst : Epi f := by infer_instance) :
    IsIso inr := h.cocone.isIso_inr_of_epi_of_isColimit h.isColimit

end

section

/-
**CategoryTheory.IsPushout.epi_inl_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.IsPushout`。
形式化陈述：epi_inl_of_epi (h : IsPushout f g inl inr) (inst : Epi g
参数：h : IsPushout f g inl inr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.hom_ext`：hom_ext (hP : IsPushout f g inl inr) {
W : C} {k l : P ⟶ W} (h₀ : inl ≫ k = inl ≫ l) (h₁ : inr ≫ k = inr ≫ l) : k = l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.w_assoc`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y
 ⟶ Z},   CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma epi_inl_of_epi (h : IsPushout f g inl inr) (inst : Epi g := by infer_instance) :
    Epi inl := by
  constructor
  intro W fst' snd' heq
  exact h.hom_ext heq (by simp [← cancel_epi g, ← h.w_assoc, heq])
/-
**CategoryTheory.IsPushout.epi_inr_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.IsPushout`。
形式化陈述：epi_inr_of_epi (h : IsPushout f g inl inr) (inst : Epi f
参数：h : IsPushout f g inl inr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.epi_inl_of_epi`：epi_inl_of_epi (h : IsPushout f
 g inl inr) (inst : Epi g
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
-/
lemma epi_inr_of_epi (h : IsPushout f g inl inr) (inst : Epi f := by infer_instance) :
    Epi inr := h.flip.epi_inl_of_epi
/-
**CategoryTheory.IsPushout.isIso_inl_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.IsPushout`。
形式化陈述：isIso_inl_of_isIso (h : IsPushout f g inl inr) (inst : IsIso g
参数：h : IsPushout f g inl inr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.hasPushout`：hasPushout (h : IsPushout f g inl i
nr) : HasPushout f g where exists_colimit
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPushout.inl_isoPushout_inv`：inl_isoPushout_inv (h : IsP
ushout f g inl inr) [HasPushout f g] : pushout.inl _ _ ≫ h.isoPushout.inv = inl
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma isIso_inl_of_isIso (h : IsPushout f g inl inr) (inst : IsIso g := by infer_instance) :
    IsIso inl := by
  have := h.hasPushout
  rw [← h.inl_isoPushout_inv]
  infer_instance
/-
**CategoryTheory.IsPushout.isIso_inr_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.IsPushout`。
形式化陈述：isIso_inr_of_isIso (h : IsPushout f g inl inr) (inst : IsIso f
参数：h : IsPushout f g inl inr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.isIso_inl_of_isIso`：isIso_inl_of_isIso (h : IsP
ushout f g inl inr) (inst : IsIso g
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
-/
lemma isIso_inr_of_isIso (h : IsPushout f g inl inr) (inst : IsIso f := by infer_instance) :
    IsIso inr := h.flip.isIso_inl_of_isIso

end

-- Objects here are arranged in a 3x2 grid, and indexed by their xy coordinates.
-- Morphisms are named `hᵢⱼ` for a horizontal morphism starting at `(i,j)`,
-- and `vᵢⱼ` for a vertical morphism starting at `(i,j)`.
/-- Paste two pushout squares "vertically" to obtain another pushout square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
/-
**CategoryTheory.IsPushout.paste_vert** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
IsPushout`。
形式化陈述：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂
₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ 
: X₂₂ ⟶ X₃₂} (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPushout h₂₁ v₂₁ v₂₂ h₃₁) : I
sPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁
参数：s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁；t : IsPushout h₂₁ v₂₁ v₂₂ h₃₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_isColimit`：of_isColimit {c : PushoutCocone f
 g} (h : Limits.IsColimit c) : IsPushout f g c.inl c.inr

--- 原说明 ---
Paste two pushout squares "vertically" to obtain another pushout square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
theorem paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPushout h₂₁ v₂₁ v₂₂ h₃₁) :
    IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
  of_isColimit (pasteHorizIsPushout rfl s.isColimit t.isColimit)

/-- Paste two pushout squares "horizontally" to obtain another pushout square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
/-
**CategoryTheory.IsPushout.paste_horiz** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.IsPushout`。
形式化陈述：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X
₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃
 : X₁₃ ⟶ X₂₃} (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPushout h₁₂ v₁₂ v₁₃ h₂₂) : 
IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)
参数：s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁；t : IsPushout h₁₂ v₁₂ v₁₃ h₂₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `CategoryTheory.IsPushout.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂
 : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v
₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…

--- 原说明 ---
Paste two pushout squares "horizontally" to obtain another pushout square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
theorem paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPushout h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
  (paste_vert s.flip t.flip).flip

/-- Given a pushout square assembled from a pushout square on the top and
a commuting square on the bottom, the bottom square is a pushout square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
/-
**CategoryTheory.IsPushout.of_top** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsPu
shout`。
形式化陈述：of_top {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {
h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂
₂ ⟶ X₃₂} (s : IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₂₁ ≫ v₂₂ = v₂₁ ≫ 
h₃₁) (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) : IsPushout h₂₁ v₂₁ v₂₂ h₃₁
参数：s : IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁；p : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁；t : I
sPushout h₁₁ v₁₁ v₁₂ h₂₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_isColimit`：of_isColimit {c : PushoutCocone f
 g} (h : Limits.IsColimit c) : IsPushout f g c.inl c.inr
· 使用定理 `CategoryTheory.IsPushout.cocone_inr`：cocone_inr (h : IsPushout f g inl i
nr) : h.cocone.inr = inr

--- 原说明 ---
Given a pushout square assembled from a pushout square on the top and
a commuting square on the bottom, the bottom square is a pushout square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
theorem of_top {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁)
    (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) : IsPushout h₂₁ v₂₁ v₂₂ h₃₁ :=
  of_isColimit <| rightSquareIsPushout
    (PushoutCocone.mk _ _ p) (cocone_inr _) t.isColimit s.isColimit

/-- Given a pushout square assembled from a pushout square on the left and
a commuting square on the right, the right square is a pushout square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
/-
**CategoryTheory.IsPushout.of_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsP
ushout`。
形式化陈述：of_left {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} 
{h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X
₁₃ ⟶ X₂₃} (s : IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₂ ≫ v₁₃ = v₁₂ ≫
 h₂₂) (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) : IsPushout h₁₂ v₁₂ v₁₃ h₂₂
参数：s : IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)；p : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂；t : I
sPushout h₁₁ v₁₁ v₁₂ h₂₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `CategoryTheory.IsPushout.of_top`：of_top {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h
₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂
 ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given a pushout square assembled from a pushout square on the left and
a commuting square on the right, the right square is a pushout square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
theorem of_left {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂)
    (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) : IsPushout h₁₂ v₁₂ v₁₃ h₂₂ :=
  (of_top s.flip p.symm t.flip).flip
/-
**CategoryTheory.IsPushout.paste_vert_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.IsPushout`。
形式化陈述：paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ 
⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {
v₂₂ : X₂₂ ⟶ X₃₂} (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (e : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁) : I
sPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ ↔ IsPushout h₂₁ v₂₁ v₂₂ h₃₁
参数：s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁；e : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_top`：of_top {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h
₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂
 ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ …
· 使用定理 `CategoryTheory.IsPushout.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂
 : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v
₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
-/
theorem paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (e : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁) :
    IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ ↔ IsPushout h₂₁ v₂₁ v₂₂ h₃₁ :=
  ⟨fun h => h.of_top e s, s.paste_vert⟩
/-
**CategoryTheory.IsPushout.paste_horiz_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.IsPushout`。
形式化陈述：paste_horiz_iff {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂
 ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} 
{v₁₃ : X₁₃ ⟶ X₂₃} (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (e : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂) : 
IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) ↔ IsPushout h₁₂ v₁₂ v₁₃ h₂₂
参数：s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁；e : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_left`：of_left {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} 
{h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X
₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶…
· 使用定理 `CategoryTheory.IsPushout.paste_horiz`：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X
₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} 
{v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X…
-/
theorem paste_horiz_iff {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (e : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂) :
    IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) ↔ IsPushout h₁₂ v₁₂ v₁₃ h₂₂ :=
  ⟨fun h => h.of_left e s, s.paste_horiz⟩

/-- Variant of `IsPushout.of_top` where `v₂₂` is induced from a morphism `v₁₃ : X₁₂ ⟶ X₃₂`, and
the universal property of the top square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
/-
**CategoryTheory.IsPushout.of_top'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsP
ushout`。
形式化陈述：of_top' {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} 
{h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₂ ⟶ X₃₂} {v₂₁ : X
₂₁ ⟶ X₃₁} (s : IsPushout h₁₁ (v₁₁ ≫ v₂₁) v₁₃ h₃₁) (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁
) : IsPushout h₂₁ v₂₁ (t.desc v₁₃ (v₂₁ ≫ h₃₁) (by rw [s.w, Category.assoc])) h₃₁
参数：s : IsPushout h₁₁ (v₁₁ ≫ v₂₁) v₁₃ h₃₁；t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_top`：of_top {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h
₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂
 ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.IsPushout.inl_desc`：inl_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h
· 使用引理 `CategoryTheory.IsPushout.inr_desc`：inr_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inr ≫ hP.desc h k w = k

--- 原说明 ---
Variant of `IsPushout.of_top` where `v₂₂` is induced from a morphism `v₁₃ : X₁₂ 
⟶ X₃₂`, and
the universal property of the top square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
theorem of_top' {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₂ ⟶ X₃₂} {v₂₁ : X₂₁ ⟶ X₃₁}
    (s : IsPushout h₁₁ (v₁₁ ≫ v₂₁) v₁₃ h₃₁) (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) :
      IsPushout h₂₁ v₂₁ (t.desc v₁₃ (v₂₁ ≫ h₃₁) (by rw [s.w, Category.assoc])) h₃₁ :=
  of_top ((t.inl_desc _ _ _).symm ▸ s) (t.inr_desc _ _ _) t

/-- Variant of `IsPushout.of_right` where `h₂₂` is induced from a morphism `h₂₃ : X₂₁ ⟶ X₂₃`, and
the universal property of the left square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
/-
**CategoryTheory.IsPushout.of_left'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
Pushout`。
形式化陈述：of_left' {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
 {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₃ : X₂₁ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : 
X₁₃ ⟶ X₂₃} (s : IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ h₂₃) (t : IsPushout h₁₁ v₁₁ v₁₂ h₂
₁) : IsPushout h₁₂ v₁₂ v₁₃ (t.desc (h₁₂ ≫ v₁₃) h₂₃ (by rw [← Category.assoc, s.w
]))
参数：s : IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ h₂₃；t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_left`：of_left {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} 
{h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X
₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.IsPushout.inr_desc`：inr_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inr ≫ hP.desc h k w = k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.IsPushout.inl_desc`：inl_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Variant of `IsPushout.of_right` where `h₂₂` is induced from a morphism `h₂₃ : X₂
₁ ⟶ X₂₃`, and
the universal property of the left square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
theorem of_left' {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₃ : X₂₁ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ h₂₃) (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) :
    IsPushout h₁₂ v₁₂ v₁₃ (t.desc (h₁₂ ≫ v₁₃) h₂₃ (by rw [← Category.assoc, s.w])) :=
  of_left ((t.inr_desc _ _ _).symm ▸ s) (by simp only [inl_desc]) t
/-
**CategoryTheory.IsPushout.of_horiz_isIso_epi** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.IsPushout`。
形式化陈述：of_horiz_isIso_epi [Epi f] [IsIso inr] (sq : CommSq f g inl inr) : IsPusho
ut f g inl inr
参数：sq : CommSq f g inl inr。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_isColimit'`：of_isColimit' (w : CommSq f g in
l inr) (h : Limits.IsColimit w.cocone) : IsPushout f g inl inr
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.w_assoc`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y
 ⟶ Z},   CategoryTh…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition`：condition (t : PushoutCoc
one f g) : f ≫ inl t = g ≫ inr t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem of_horiz_isIso_epi [Epi f] [IsIso inr] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  of_isColimit' sq
    (by
      refine
        PushoutCocone.IsColimit.mk _ (fun s => inv inr ≫ s.inr) (fun s => ?_)
          (by simp) (by simp)
      simp only [← cancel_epi f, s.condition, sq.w_assoc, IsIso.hom_inv_id_assoc])
/-
**CategoryTheory.IsPushout.of_horiz_isIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.IsPushout`。
形式化陈述：of_horiz_isIso [IsIso f] [IsIso inr] (sq : CommSq f g inl inr) : IsPushout
 f g inl inr
参数：sq : CommSq f g inl inr。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_horiz_isIso_epi`：of_horiz_isIso_epi [Epi f] 
[IsIso inr] (sq : CommSq f g inl inr) : IsPushout f g inl inr
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
-/
theorem of_horiz_isIso [IsIso f] [IsIso inr] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  of_horiz_isIso_epi sq
/-
**CategoryTheory.IsPushout.of_vert_isIso_epi** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.IsPushout`。
形式化陈述：of_vert_isIso_epi [Epi g] [IsIso inl] (sq : CommSq f g inl inr) : IsPushou
t f g inl inr
参数：sq : CommSq f g inl inr。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `CategoryTheory.IsPushout.of_horiz_isIso_epi`：of_horiz_isIso_epi [Epi f] 
[IsIso inr] (sq : CommSq f g inl inr) : IsPushout f g inl inr
· 使用定理 `CategoryTheory.CommSq.flip`：flip (p : CommSq f g h i) : CommSq g f i h
-/
theorem of_vert_isIso_epi [Epi g] [IsIso inl] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  (of_horiz_isIso_epi sq.flip).flip
/-
**CategoryTheory.IsPushout.of_vert_isIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.IsPushout`。
形式化陈述：of_vert_isIso [IsIso g] [IsIso inl] (sq : CommSq f g inl inr) : IsPushout 
f g inl inr
参数：sq : CommSq f g inl inr。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_vert_isIso_epi`：of_vert_isIso_epi [Epi g] [I
sIso inl] (sq : CommSq f g inl inr) : IsPushout f g inl inr
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
-/
theorem of_vert_isIso [IsIso g] [IsIso inl] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  of_vert_isIso_epi sq
/-
**CategoryTheory.IsPushout.of_id_fst** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.I
sPushout`。
形式化陈述：of_id_fst : IsPushout (𝟙 _) f f (𝟙 _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_horiz_isIso`：of_horiz_isIso [IsIso f] [IsIso
 inr] (sq : CommSq f g inl inr) : IsPushout f g inl inr
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma of_id_fst : IsPushout (𝟙 _) f f (𝟙 _) := IsPushout.of_horiz_isIso ⟨by simp⟩
/-
**CategoryTheory.IsPushout.of_id_snd** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.I
sPushout`。
形式化陈述：of_id_snd : IsPushout f (𝟙 _) (𝟙 _) f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_vert_isIso`：of_vert_isIso [IsIso g] [IsIso i
nl] (sq : CommSq f g inl inr) : IsPushout f g inl inr
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma of_id_snd : IsPushout f (𝟙 _) (𝟙 _) f := IsPushout.of_vert_isIso ⟨by simp⟩

/-- The following diagram is a pullback
```
X --f--> Z
|        |
id       id
v        v
X --f--> Z
```
-/
/-
**CategoryTheory.IsPushout.id_vert** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsP
ushout`。
形式化陈述：id_vert (f : X ⟶ Z) : IsPushout f (𝟙 X) (𝟙 Z) f
参数：f : X ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_vert_isIso`：of_vert_isIso [IsIso g] [IsIso i
nl] (sq : CommSq f g inl inr) : IsPushout f g inl inr
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The following diagram is a pullback
```
X --f--> Z
|        |
id       id
v        v
X --f--> Z
```
-/
lemma id_vert (f : X ⟶ Z) : IsPushout f (𝟙 X) (𝟙 Z) f :=
  of_vert_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

/-- The following diagram is a pullback
```
X --id--> X
|         |
f         f
v         v
Z --id--> Z
```
-/
/-
**CategoryTheory.IsPushout.id_horiz** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Is
Pushout`。
形式化陈述：id_horiz (f : X ⟶ Z) : IsPushout (𝟙 X) f f (𝟙 Z)
参数：f : X ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_horiz_isIso`：of_horiz_isIso [IsIso f] [IsIso
 inr] (sq : CommSq f g inl inr) : IsPushout f g inl inr
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The following diagram is a pullback
```
X --id--> X
|         |
f         f
v         v
Z --id--> Z
```
-/
lemma id_horiz (f : X ⟶ Z) : IsPushout (𝟙 X) f f (𝟙 Z) :=
  of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
In a category, given a morphism `f : A ⟶ B` and an object `X`,
this is the obvious pushout diagram:
```
A ⟶ A ⨿ X
|     |
v     v
B ⟶ B ⨿ X
```
-/
/-
**CategoryTheory.IsPushout.of_coprod_inl_with_id** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.IsPushout`。
形式化陈述：of_coprod_inl_with_id {A B : C} (f : A ⟶ B) (X : C) [HasBinaryCoproduct A 
X] [HasBinaryCoproduct B X] : IsPushout coprod.inl f (coprod.map f (𝟙 X)) coprod
.inl where w
参数：f : A ⟶ B；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.inl_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.coprod.map_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {S T U V W : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct U W] [inst_2 :…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition`：condition (t : PushoutCoc
one f g) : f ≫ inl t = g ≫ inr t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.coprod.inr_map_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Has
BinaryCoproduct W X] [inst_2 : C…

--- 原说明 ---
In a category, given a morphism `f : A ⟶ B` and an object `X`,
this is the obvious pushout diagram:
```
A ⟶ A ⨿ X
|     |
v     v
B ⟶ B ⨿ X
```
-/
lemma of_coprod_inl_with_id {A B : C} (f : A ⟶ B) (X : C) [HasBinaryCoproduct A X]
    [HasBinaryCoproduct B X] :
    IsPushout coprod.inl f (coprod.map f (𝟙 X)) coprod.inl where
  w := by simp
  isColimit' := ⟨PushoutCocone.isColimitAux' _ (fun s ↦ by
    refine ⟨coprod.desc s.inr (coprod.inr ≫ s.inl), ?_, ?_, ?_⟩
    · ext
      · simp [PushoutCocone.condition]
      · simp
    · simp
    · intro m h₁ h₂
      dsimp at m h₁ h₂ ⊢
      ext
      · simpa using h₂
      · simp [← h₁])⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsPushout.of_isColimit_binaryCofan_of_isInitial** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.IsPushout`。
形式化陈述：of_isColimit_binaryCofan_of_isInitial {X Y : C} {c : BinaryCofan X Y} (hc 
: IsColimit c) {I : C} (hI : IsInitial I) : IsPushout (hI.to _) (hI.to _) c.inr 
c.inl where w
参数：hc : IsColimit c；hI : IsInitial I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.BinaryCofan.IsColimit.inr_desc`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {X Y W : C} {s : CategoryTheory.Limits.Bi
naryCofan X Y}   (h : CategoryTheory.Limit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.Limits.BinaryCofan.IsColimit.inl_desc`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {X Y W : C} {s : CategoryTheory.Limits.Bi
naryCofan X Y}   (h : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.BinaryCofan.IsColimit.hom_ext`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.Bin
aryCofan X Y}   (h : CategoryTheory.Limit…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma of_isColimit_binaryCofan_of_isInitial
    {X Y : C} {c : BinaryCofan X Y} (hc : IsColimit c)
    {I : C} (hI : IsInitial I) :
    IsPushout (hI.to _) (hI.to _) c.inr c.inl where
  w := hI.hom_ext _ _
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s ↦ BinaryCofan.IsColimit.desc hc s.inr s.inl) (by simp) (by simp)
    (fun s m h₁ h₂ ↦ by apply BinaryCofan.IsColimit.hom_ext hc <;> cat_disch)⟩
/-
**CategoryTheory.IsPushout.mk'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsPusho
ut`。
形式化陈述：mk' {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} (w :
 f ≫ inl = g ≫ inr) (hom_ext : forall ⦃T : C⦄ ⦃φ φ' : P ⟶ T⦄ (_ : inl ≫ φ = inl 
≫ φ') (_ : inr ≫ φ = inr ≫ φ'), φ = φ') (exists_desc : forall ⦃T : C⦄ (a : X ⟶ T
) (b : Y ⟶ T) (_ : f ≫ a = g ≫ b), exists (l : P ⟶ T), inl ≫ l = a ∧ inr ≫ l = b
) : IsPushout f g inl inr where w
参数：w : f ≫ inl = g ≫ inr；hom_ext : forall ⦃T : C⦄ ⦃φ φ' : P ⟶ T⦄ (_ : inl ≫ φ = 
inl ≫ φ') (_ : inr ≫ φ = inr ≫ φ'), φ = φ'；exists_desc : forall ⦃T : C⦄ (a : X ⟶
 T) (b : Y ⟶ T) (_ : f ≫ a = g ≫ b), exists (l : P ⟶ T), inl ≫ l = a ∧ inr ≫ l =
 b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition`：condition (t : PushoutCoc
one f g) : f ≫ inl t = g ≫ inr t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mk' {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (w : f ≫ inl = g ≫ inr)
    (hom_ext : ∀ ⦃T : C⦄ ⦃φ φ' : P ⟶ T⦄ (_ : inl ≫ φ = inl ≫ φ')
      (_ : inr ≫ φ = inr ≫ φ'), φ = φ')
    (exists_desc : ∀ ⦃T : C⦄ (a : X ⟶ T) (b : Y ⟶ T)
      (_ : f ≫ a = g ≫ b), ∃ (l : P ⟶ T), inl ≫ l = a ∧ inr ≫ l = b) :
    IsPushout f g inl inr where
  w := w
  isColimit' := by
    let l (s : PushoutCocone f g) := exists_desc _ _ s.condition
    exact ⟨PushoutCocone.IsColimit.mk _
      (fun s ↦ (l s).choose)
      (fun s ↦ (l s).choose_spec.1)
      (fun s ↦ (l s).choose_spec.2)
      (fun s m h₁ h₂ ↦ hom_ext
        (h₁.trans (l s).choose_spec.1.symm)
        (h₂.trans (l s).choose_spec.2.symm))⟩

end IsPushout

section Equalizer

variable {X Y Z : C} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}

/-- If `f : X ⟶ Y`, `g g' : Y ⟶ Z` forms a pullback square, then `f` is the equalizer of
`g` and `g'`. -/
/-
**CategoryTheory.IsPullback.isLimitFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.IsPullback`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y Z
 : C} →       {f : X ⟶ Y} →         {g g' : Y ⟶ Z} →           (H : CategoryTheo
ry.IsPullback f f g g') → CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.F
ork.ofι f ⋯)
参数：H : CategoryTheory.IsPullback f f g g'；CategoryTheory.Limits.Fork.ofι f ⋯。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Fork.condition`：∀ {C : Type u} {X Y : C} [inst : C
ategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Fork f
 g),   CategoryTheory.Cate…

--- 原说明 ---
If `f : X ⟶ Y`, `g g' : Y ⟶ Z` forms a pullback square, then `f` is the equalize
r of
`g` and `g'`.
-/
noncomputable def IsPullback.isLimitFork (H : IsPullback f f g g') : IsLimit (Fork.ofι f H.w) := by
  fapply Fork.IsLimit.mk
  · exact fun s => H.isLimit.lift (PullbackCone.mk s.ι s.ι s.condition)
  · exact fun s => H.isLimit.fac _ WalkingCospan.left
  · intro s m e
    apply PullbackCone.IsLimit.hom_ext H.isLimit <;> refine e.trans ?_ <;> symm <;>
      exact H.isLimit.fac _ _

/-- If `f f' : X ⟶ Y`, `g : Y ⟶ Z` forms a pushout square, then `g` is the coequalizer of
`f` and `f'`. -/
/-
**CategoryTheory.IsPushout.isLimitFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.IsPushout`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y Z
 : C} →       {f f' : X ⟶ Y} →         {g : Y ⟶ Z} →           (H : CategoryTheo
ry.IsPushout f f' g g) →             CategoryTheory.Limits.IsColimit (CategoryTh
eory.Limits.Cofork.ofπ g ⋯)
参数：H : CategoryTheory.IsPushout f f' g g；CategoryTheory.Limits.Cofork.ofπ g ⋯。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofork.condition`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Cofo
rk f g),   CategoryTheory.Ca…

--- 原说明 ---
If `f f' : X ⟶ Y`, `g : Y ⟶ Z` forms a pushout square, then `g` is the coequaliz
er of
`f` and `f'`.
-/
noncomputable def IsPushout.isLimitFork (H : IsPushout f f' g g) :
    IsColimit (Cofork.ofπ g H.w) := by
  fapply Cofork.IsColimit.mk
  · exact fun s => H.isColimit.desc (PushoutCocone.mk s.π s.π s.condition)
  · exact fun s => H.isColimit.fac _ WalkingSpan.left
  · intro s m e
    apply PushoutCocone.IsColimit.hom_ext H.isColimit <;> refine e.trans ?_ <;> symm <;>
      exact H.isColimit.fac _ _

end Equalizer

section Functor

variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.map_isPullback** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory
.Limits.PreservesLimit (CategoryTheory.Limits.cospan h i) F],   CategoryTheory.I
sPullback f g h i → CategoryTheory.IsPullback (F.map f) (F.map g) (F.map h) (F.m
ap i)
参数：F : CategoryTheory.Functor C D；CategoryTheory.Limits.cospan h i；F.map f；F.map
 g；F.map h；F.map i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_isLimit'`：of_isLimit' (w : CommSq fst snd f
 g) (h : Limits.IsLimit w.cone) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.Functor.map_commSq`：map_commSq (s : CommSq f g h i) : Com
mSq (F.map f) (F.map g) (F.map h) (F.map i)
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Functor.map_isPullback [PreservesLimit (cospan h i) F] (s : IsPullback f g h i) :
    IsPullback (F.map f) (F.map g) (F.map h) (F.map i) := by
  refine
    IsPullback.of_isLimit' (F.map_commSq s.toCommSq)
      (IsLimit.equivOfNatIsoOfIso (cospanCompIso F h i) _ _ (WalkingCospan.ext ?_ ?_ ?_)
        (isLimitOfPreserves F s.isLimit))
  · rfl
  · simp
  · simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.map_isPushout** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory
.Limits.PreservesColimit (CategoryTheory.Limits.span f g) F],   CategoryTheory.I
sPushout f g h i → CategoryTheory.IsPushout (F.map f) (F.map g) (F.map h) (F.map
 i)
参数：F : CategoryTheory.Functor C D；CategoryTheory.Limits.span f g；F.map f；F.map g
；F.map h；F.map i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_isColimit'`：of_isColimit' (w : CommSq f g in
l inr) (h : Limits.IsColimit w.cocone) : IsPushout f g inl inr
· 使用定理 `CategoryTheory.Functor.map_commSq`：map_commSq (s : CommSq f g h i) : Com
mSq (F.map f) (F.map g) (F.map h) (F.map i)
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Functor.map_isPushout [PreservesColimit (span f g) F] (s : IsPushout f g h i) :
    IsPushout (F.map f) (F.map g) (F.map h) (F.map i) := by
  refine
    IsPushout.of_isColimit' (F.map_commSq s.toCommSq)
      (IsColimit.equivOfNatIsoOfIso (spanCompIso F f g) _ _ (WalkingSpan.ext ?_ ?_ ?_)
        (isColimitOfPreserves F s.isColimit))
  · rfl
  · simp
  · simp

alias IsPullback.map := Functor.map_isPullback

alias IsPushout.map := Functor.map_isPushout
/-
**CategoryTheory.IsPullback.of_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsP
ullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory
.Limits.ReflectsLimit (CategoryTheory.Limits.cospan h i) F],   CategoryTheory.Ca
tegoryStruct.comp f h = CategoryTheory.CategoryStruct.comp g i →     CategoryThe
ory.IsPullback (F.map f) (F.map g) (F.map h) (F.map i) → CategoryTheory.IsPullba
ck f g h i
参数：F : CategoryTheory.Functor C D；CategoryTheory.Limits.cospan h i；F.map f；F.map
 g；F.map h；F.map i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem IsPullback.of_map [ReflectsLimit (cospan h i) F] (e : f ≫ h = g ≫ i)
    (H : IsPullback (F.map f) (F.map g) (F.map h) (F.map i)) : IsPullback f g h i := by
  refine ⟨⟨e⟩, ⟨isLimitOfReflects F <| ?_⟩⟩
  refine
    (IsLimit.equivOfNatIsoOfIso (cospanCompIso F h i) _ _ (WalkingCospan.ext ?_ ?_ ?_)).symm
      H.isLimit
  exacts [Iso.refl _, (Category.comp_id _).trans (Category.id_comp _).symm,
    (Category.comp_id _).trans (Category.id_comp _).symm]
/-
**CategoryTheory.IsPullback.of_map_of_faithful** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.IsPullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory
.Limits.ReflectsLimit (CategoryTheory.Limits.cospan h i) F] [F.Faithful],   Cate
goryTheory.IsPullback (F.map f) (F.map g) (F.map h) (F.map i) → CategoryTheory.I
sPullback f g h i
参数：F : CategoryTheory.Functor C D；CategoryTheory.Limits.cospan h i；F.map f；F.map
 g；F.map h；F.map i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_map`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
-/
theorem IsPullback.of_map_of_faithful [ReflectsLimit (cospan h i) F] [F.Faithful]
    (H : IsPullback (F.map f) (F.map g) (F.map h) (F.map i)) : IsPullback f g h i :=
  H.of_map F (F.map_injective <| by simpa only [F.map_comp] using H.w)
/-
**CategoryTheory.IsPullback.map_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
Pullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {W X Y Z : C} 
{f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z} {D : Type u_1} [inst_1 : Categ
oryTheory.Category.{v_1, u_1} D] (F : CategoryTheory.Functor C D)   [CategoryThe
ory.Limits.PreservesLimit (CategoryTheory.Limits.cospan h i) F]   [CategoryTheor
y.Limits.ReflectsLimit (CategoryTheory.Limits.cospan h i) F],   CategoryTheory.C
ategoryStruct.comp f h = CategoryTheory.CategoryStruct.comp g i →     (CategoryT
heory.IsPullback (F.map f) (F.map g) (F.map h) (F.map i) ↔ CategoryTheory.IsPull
back f g h i)
参数：F : CategoryTheory.Functor C D；CategoryTheory.Limits.cospan h i；CategoryTheor
y.Limits.cospan h i；CategoryTheory.IsPullback (F.map f) (F.map g) (F.map h) (F.m
ap i) ↔ CategoryTheory.IsPullback f g h i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_map`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsPullback.map`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (F : CategoryTheor…
-/
theorem IsPullback.map_iff {D : Type*} [Category* D] (F : C ⥤ D) [PreservesLimit (cospan h i) F]
    [ReflectsLimit (cospan h i) F] (e : f ≫ h = g ≫ i) :
    IsPullback (F.map f) (F.map g) (F.map h) (F.map i) ↔ IsPullback f g h i :=
  ⟨fun h => h.of_map F e, fun h => h.map F⟩
/-
**CategoryTheory.IsPushout.of_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsPu
shout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory
.Limits.ReflectsColimit (CategoryTheory.Limits.span f g) F],   CategoryTheory.Ca
tegoryStruct.comp f h = CategoryTheory.CategoryStruct.comp g i →     CategoryThe
ory.IsPushout (F.map f) (F.map g) (F.map h) (F.map i) → CategoryTheory.IsPushout
 f g h i
参数：F : CategoryTheory.Functor C D；CategoryTheory.Limits.span f g；F.map f；F.map g
；F.map h；F.map i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem IsPushout.of_map [ReflectsColimit (span f g) F] (e : f ≫ h = g ≫ i)
    (H : IsPushout (F.map f) (F.map g) (F.map h) (F.map i)) : IsPushout f g h i := by
  refine ⟨⟨e⟩, ⟨isColimitOfReflects F <| ?_⟩⟩
  refine
    (IsColimit.equivOfNatIsoOfIso (spanCompIso F f g) _ _ (WalkingSpan.ext ?_ ?_ ?_)).symm
      H.isColimit
  exacts [Iso.refl _, (Category.comp_id _).trans (Category.id_comp _),
    (Category.comp_id _).trans (Category.id_comp _)]
/-
**CategoryTheory.IsPushout.of_map_of_faithful** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.IsPushout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory
.Limits.ReflectsColimit (CategoryTheory.Limits.span f g) F] [F.Faithful],   Cate
goryTheory.IsPushout (F.map f) (F.map g) (F.map h) (F.map i) → CategoryTheory.Is
Pushout f g h i
参数：F : CategoryTheory.Functor C D；CategoryTheory.Limits.span f g；F.map f；F.map g
；F.map h；F.map i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_map`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
-/
theorem IsPushout.of_map_of_faithful [ReflectsColimit (span f g) F] [F.Faithful]
    (H : IsPushout (F.map f) (F.map g) (F.map h) (F.map i)) : IsPushout f g h i :=
  H.of_map F (F.map_injective <| by simpa only [F.map_comp] using H.w)
/-
**CategoryTheory.IsPushout.map_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsP
ushout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {W X Y Z : C} 
{f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z} {D : Type u_1} [inst_1 : Categ
oryTheory.Category.{v_1, u_1} D] (F : CategoryTheory.Functor C D)   [CategoryThe
ory.Limits.PreservesColimit (CategoryTheory.Limits.span f g) F]   [CategoryTheor
y.Limits.ReflectsColimit (CategoryTheory.Limits.span f g) F],   CategoryTheory.C
ategoryStruct.comp f h = CategoryTheory.CategoryStruct.comp g i →     (CategoryT
heory.IsPushout (F.map f) (F.map g) (F.map h) (F.map i) ↔ CategoryTheory.IsPusho
ut f g h i)
参数：F : CategoryTheory.Functor C D；CategoryTheory.Limits.span f g；CategoryTheory.
Limits.span f g；CategoryTheory.IsPushout (F.map f) (F.map g) (F.map h) (F.map i)
 ↔ CategoryTheory.IsPushout f g h i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_map`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsPushout.map`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   
(F : CategoryTheor…
-/
theorem IsPushout.map_iff {D : Type*} [Category* D] (F : C ⥤ D) [PreservesColimit (span f g) F]
    [ReflectsColimit (span f g) F] (e : f ≫ h = g ≫ i) :
    IsPushout (F.map f) (F.map g) (F.map h) (F.map i) ↔ IsPushout f g h i :=
  ⟨fun h => h.of_map F e, fun h => h.map F⟩

variable {F} in
/-
**CategoryTheory.IsPullback.preservesLimit_cospan_iff** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.IsPullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z},   CategoryTh
eory.IsPullback fst snd f g →     (CategoryTheory.Limits.PreservesLimit (Categor
yTheory.Limits.cospan f g) F ↔       CategoryTheory.IsPullback (F.map fst) (F.ma
p snd) (F.map f) (F.map g))
参数：CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.cospan f g) F ↔  
     CategoryTheory.IsPullback (F.map fst) (F.map snd) (F.map f) (F.map g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.map`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (F : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma IsPullback.preservesLimit_cospan_iff {P X Y Z : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) :
    PreservesLimit (cospan f g) F ↔ IsPullback (F.map fst) (F.map snd) (F.map f) (F.map g) := by
  refine ⟨fun _ ↦ h.map _, fun hF ↦ ?_⟩
  apply preservesLimit_of_preserves_limit_cone h.isLimit
  exact (PullbackCone.isLimitMapConeEquiv _ _).symm hF.isLimit

variable {F} in
/-
**CategoryTheory.IsPushout.preservesColimit_span_iff** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.IsPushout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {P X Y Z : C} {inl : X ⟶ P} {inr : Y ⟶ P} {f : Z ⟶ X} {g : Z ⟶ Y},   CategoryTh
eory.IsPushout f g inl inr →     (CategoryTheory.Limits.PreservesColimit (Catego
ryTheory.Limits.span f g) F ↔       CategoryTheory.IsPushout (F.map f) (F.map g)
 (F.map inl) (F.map inr))
参数：CategoryTheory.Limits.PreservesColimit (CategoryTheory.Limits.span f g) F ↔  
     CategoryTheory.IsPushout (F.map f) (F.map g) (F.map inl) (F.map inr)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.map`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   
(F : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma IsPushout.preservesColimit_span_iff {P X Y Z : C} {inl : X ⟶ P}
    {inr : Y ⟶ P} {f : Z ⟶ X} {g : Z ⟶ Y} (h : IsPushout f g inl inr) :
    PreservesColimit (span f g) F ↔ IsPushout (F.map f) (F.map g) (F.map inl) (F.map inr) := by
  refine ⟨fun _ ↦ h.map _, fun hF ↦ ?_⟩
  apply preservesColimit_of_preserves_colimit_cocone h.isColimit
  exact (PushoutCocone.isColimitMapCoconeEquiv _ _).symm hF.isColimit

variable {F} in
/-
**CategoryTheory.Limits.preservesLimitsOfShape_walkingCospan_of_forall_isPullbac
k** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
,   (∀ ⦃X Y Z : C⦄ (f : X ⟶ Z) (g : Y ⟶ Z) [CategoryTheory.Limits.HasPullback f 
g],       ∃ P fst snd,         CategoryTheory.IsPullback fst snd f g ∧ CategoryT
heory.IsPullback (F.map fst) (F.map snd) (F.map f) (F.map g)) →     CategoryTheo
ry.Limits.PreservesLimitsOfShape CategoryTheory.Limits.WalkingCospan F
参数：∀ ⦃X Y Z : C⦄ (f : X ⟶ Z) (g : Y ⟶ Z) [CategoryTheory.Limits.HasPullback f g]
,       ∃ P fst snd,         CategoryTheory.IsPullback fst snd f g ∧ CategoryThe
ory.IsPullback (F.map fst) (F.map snd) (F.map f) (F.map g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimit.mk'`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPullback.preservesLimit_cospan_iff`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t
-/
lemma Limits.preservesLimitsOfShape_walkingCospan_of_forall_isPullback
    (H : ∀ ⦃X Y Z : C⦄ (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g],
      ∃ (P : C) (fst : P ⟶ X) (snd : P ⟶ Y),
        IsPullback fst snd f g ∧ IsPullback (F.map fst) (F.map snd) (F.map f) (F.map g)) :
    PreservesLimitsOfShape WalkingCospan F := by
  suffices h : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), PreservesLimit (cospan f g) F from
    ⟨fun {K} ↦ preservesLimit_of_iso_diagram _ (Limits.diagramIsoCospan K).symm⟩
  intro X Y Z f g
  refine .mk' fun h ↦ ?_
  obtain ⟨P, fst, snd, h, h'⟩ := H f g
  rwa [h.preservesLimit_cospan_iff]

variable {F} in
/-
**CategoryTheory.Limits.preservesColimitsOfShape_walkingCospan_of_forall_isPusho
ut** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
,   (∀ ⦃X Y Z : C⦄ (f : Z ⟶ X) (g : Z ⟶ Y) [CategoryTheory.Limits.HasPushout f g
],       ∃ P inl inr,         CategoryTheory.IsPushout f g inl inr ∧ CategoryThe
ory.IsPushout (F.map f) (F.map g) (F.map inl) (F.map inr)) →     CategoryTheory.
Limits.PreservesColimitsOfShape CategoryTheory.Limits.WalkingSpan F
参数：∀ ⦃X Y Z : C⦄ (f : Z ⟶ X) (g : Z ⟶ Y) [CategoryTheory.Limits.HasPushout f g],
       ∃ P inl inr,         CategoryTheory.IsPushout f g inl inr ∧ CategoryTheor
y.IsPushout (F.map f) (F.map g) (F.map inl) (F.map inr)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimit.mk'`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPushout.preservesColimit_span_iff`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_iso_diagram`：preservesColimit_
of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F]
 : PreservesColimit K₂ F where preserves {c…
-/
lemma Limits.preservesColimitsOfShape_walkingCospan_of_forall_isPushout
    (H : ∀ ⦃X Y Z : C⦄ (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g],
      ∃ (P : C) (inl : X ⟶ P) (inr : Y ⟶ P),
        IsPushout f g inl inr ∧ IsPushout (F.map f) (F.map g) (F.map inl) (F.map inr)) :
    PreservesColimitsOfShape WalkingSpan F := by
  suffices h : ∀ {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y), PreservesColimit (span f g) F from
    ⟨fun {K} ↦ preservesColimit_of_iso_diagram _ (diagramIsoSpan K).symm⟩
  intro X Y Z f g
  refine .mk' fun h ↦ ?_
  obtain ⟨P, fst, snd, h, h'⟩ := H f g
  rwa [h.preservesColimit_span_iff]
/-
**CategoryTheory.IsPullback.app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsPull
back`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Limits.HasPullba
cks D] {F₁ F₂ F₃ F₄ : CategoryTheory.Functor C D} {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} 
  {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄},   CategoryTheory.IsPullback f₁ f₂ f₃ f₄ →     ∀
 (X : C), CategoryTheory.IsPullback (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X)
参数：X : C；f₁.app X；f₂.app X；f₃.app X；f₄.app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.map`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
lemma IsPullback.app [HasPullbacks D] {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄} (h : IsPullback f₁ f₂ f₃ f₄)
    (X : C) : IsPullback (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X) :=
  h.map ((evaluation _ _).obj X)
/-
**CategoryTheory.IsPullback.of_forall_isPullback_app** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.IsPullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F₁ F₂ F₃ F₄ : CategoryTheory.Fu
nctor C D} {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄},   (∀ (X 
: C), CategoryTheory.IsPullback (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X)) →  
   CategoryTheory.IsPullback f₁ f₂ f₃ f₄
参数：∀ (X : C), CategoryTheory.IsPullback (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app
 X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma IsPullback.of_forall_isPullback_app {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄}
    (h : ∀ (X : C), IsPullback (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X)) :
    IsPullback f₁ f₂ f₃ f₄ where
  w := by
    ext X
    simpa using (h X).w
  isLimit' := ⟨evaluationJointlyReflectsLimits _ fun X =>
    (PullbackCone.isLimitMapConeEquiv _ _).symm (h X).isLimit⟩
/-
**CategoryTheory.IsPullback.iff_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
Pullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Limits.HasPullba
cks D] {F₁ F₂ F₃ F₄ : CategoryTheory.Functor C D} {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} 
  {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄},   CategoryTheory.IsPullback f₁ f₂ f₃ f₄ ↔     ∀
 (X : C), CategoryTheory.IsPullback (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X)
参数：X : C；f₁.app X；f₂.app X；f₃.app X；f₄.app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.app`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 [CategoryTheory.Li…
· 使用定理 `CategoryTheory.IsPullback.of_forall_isPullback_app`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F₁ F₂ F₃ F₄ : Cat…
-/
lemma IsPullback.iff_app [HasPullbacks D] {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄} :
    IsPullback f₁ f₂ f₃ f₄ ↔ ∀ (X : C), IsPullback (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X) :=
  ⟨.app, .of_forall_isPullback_app⟩
/-
**CategoryTheory.IsPushout.app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsPusho
ut`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Limits.HasPushou
ts D] {F₁ F₂ F₃ F₄ : CategoryTheory.Functor C D} {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃}  
 {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄},   CategoryTheory.IsPushout f₁ f₂ f₃ f₄ → ∀ (X : 
C), CategoryTheory.IsPushout (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X)
参数：X : C；f₁.app X；f₂.app X；f₃.app X；f₄.app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.map`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   
(F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
lemma IsPushout.app [HasPushouts D] {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄} (h : IsPushout f₁ f₂ f₃ f₄)
    (X : C) : IsPushout (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X) :=
  h.map ((evaluation _ _).obj X)
/-
**CategoryTheory.IsPushout.of_forall_isPushout_app** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.IsPushout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F₁ F₂ F₃ F₄ : CategoryTheory.Fu
nctor C D} {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄},   (∀ (X 
: C), CategoryTheory.IsPushout (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X)) →   
  CategoryTheory.IsPushout f₁ f₂ f₃ f₄
参数：∀ (X : C), CategoryTheory.IsPushout (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app 
X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma IsPushout.of_forall_isPushout_app {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄}
    (h : ∀ (X : C), IsPushout (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X)) :
    IsPushout f₁ f₂ f₃ f₄ where
  w := by
    ext X
    simpa using (h X).w
  isColimit' := ⟨evaluationJointlyReflectsColimits _ fun X =>
    (PushoutCocone.isColimitMapCoconeEquiv _ _).symm (h X).isColimit⟩
/-
**CategoryTheory.IsPushout.iff_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsP
ushout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Limits.HasPushou
ts D] {F₁ F₂ F₃ F₄ : CategoryTheory.Functor C D} {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃}  
 {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄},   CategoryTheory.IsPushout f₁ f₂ f₃ f₄ ↔ ∀ (X : 
C), CategoryTheory.IsPushout (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X)
参数：X : C；f₁.app X；f₂.app X；f₃.app X；f₄.app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.app`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   
[CategoryTheory.Li…
· 使用定理 `CategoryTheory.IsPushout.of_forall_isPushout_app`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   {F₁ F₂ F₃ F₄ : Cat…
-/
lemma IsPushout.iff_app [HasPushouts D] {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄} :
    IsPushout f₁ f₂ f₃ f₄ ↔ ∀ (X : C), IsPushout (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X) :=
  ⟨.app, .of_forall_isPushout_app⟩

end Functor

section Thin

variable [Quiver.IsThin C]

/-
**CategoryTheory.isPullback_iff_isLimit_binaryFan_of_isThin** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory`。
形式化陈述：isPullback_iff_isLimit_binaryFan_of_isThin {P X Y Z : C} {fst : P ⟶ X} {sn
d : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} : IsPullback fst snd f g ↔ Nonempty (IsLimit 
(BinaryFan.mk fst snd))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
-/
lemma isPullback_iff_isLimit_binaryFan_of_isThin {P X Y Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} :
    IsPullback fst snd f g ↔ Nonempty (IsLimit (BinaryFan.mk fst snd)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨BinaryFan.IsLimit.mk _ (fun u v ↦ h.lift u v (by subsingleton))
      (by subsingleton) (by subsingleton) (by subsingleton)⟩
  · exact ⟨⟨by subsingleton⟩,
      ⟨PullbackCone.IsLimit.mk _ (fun s ↦ BinaryFan.IsLimit.lift h.some s.fst s.snd)
      (by subsingleton) (by subsingleton) (by subsingleton)⟩⟩
/-
**CategoryTheory.isPushout_iff_isColimit_binaryCofan_of_isThin** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory`。
形式化陈述：isPushout_iff_isColimit_binaryCofan_of_isThin {P X Y Z : C} {f : Z ⟶ X} {g
 : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} : IsPushout f g inl inr ↔ Nonempty (IsColi
mit (BinaryCofan.mk inl inr))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
-/
lemma isPushout_iff_isColimit_binaryCofan_of_isThin {P X Y Z : C}
    {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} :
    IsPushout f g inl inr ↔ Nonempty (IsColimit (BinaryCofan.mk inl inr)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨BinaryCofan.IsColimit.mk _ (fun u v ↦ h.desc u v (by subsingleton))
      (by subsingleton) (by subsingleton) (by subsingleton)⟩
  · exact ⟨⟨by subsingleton⟩,
      ⟨PushoutCocone.IsColimit.mk _ (fun s ↦ BinaryCofan.IsColimit.desc h.some s.inl s.inr)
      (by subsingleton) (by subsingleton) (by subsingleton)⟩⟩

variable {D : Type*} [Category* D] [Quiver.IsThin D] (F : C ⥤ D)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [PreservesLimitsOfShape (Discrete WalkingPair) F] :
    PreservesLimitsOfShape WalkingCospan F := by
  refine preservesLimitsOfShape_walkingCospan_of_forall_isPullback fun X Y Z f g hfg ↦ ?_
  use pullback f g, pullback.fst f g, pullback.snd f g, .of_hasPullback f g
  rw [isPullback_iff_isLimit_binaryFan_of_isThin]
  refine ⟨(BinaryFan.mk (pullback.fst f g) (pullback.snd f g)).isLimitMapConeEquiv ?_⟩
  apply isLimitOfPreserves _ (Nonempty.some ?_)
  rw [← CategoryTheory.isPullback_iff_isLimit_binaryFan_of_isThin (f := f) (g := g)]
  exact .of_hasPullback f g
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [PreservesColimitsOfShape (Discrete WalkingPair) F] :
    PreservesColimitsOfShape WalkingSpan F := by
  refine preservesColimitsOfShape_walkingCospan_of_forall_isPushout fun X Y Z f g hfg ↦ ?_
  use pushout f g, pushout.inl f g, pushout.inr f g, .of_hasPushout f g
  rw [isPushout_iff_isColimit_binaryCofan_of_isThin]
  refine ⟨(BinaryCofan.mk (pushout.inl f g) (pushout.inr f g)).isColimitMapConeEquiv ?_⟩
  apply isColimitOfPreserves _ (Nonempty.some ?_)
  rw [← CategoryTheory.isPushout_iff_isColimit_binaryCofan_of_isThin (f := f) (g := g)]
  exact .of_hasPushout f g

end Thin

section IsPullbackOverPullback

open Limits

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullbacksAlong g]

namespace IsPullback

set_option backward.defeqAttrib.useBackward true in
/-- An `IsPullback` square yields an isomorphism `Over.mk fst ≅ Over.mk (pullback.fst f g)`
in `Over X`. -/
/-
**CategoryTheory.IsPullback.isoOverPullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.IsPullback`。
形式化陈述：isoOverPullback {P : C} {fst : P ⟶ X} {snd : P ⟶ Y} (h : IsPullback fst sn
d f g) : Over.mk fst ≅ Over.mk (pullback.fst f g)
参数：h : IsPullback fst snd f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `IsPullback` square yields an isomorphism `Over.mk fst ≅ Over.mk (pullback.fs
t f g)`
in `Over X`.
-/
noncomputable def isoOverPullback {P : C} {fst : P ⟶ X} {snd : P ⟶ Y}
    (h : IsPullback fst snd f g) :
    Over.mk fst ≅ Over.mk (pullback.fst f g) :=
  Over.isoMk (h.isoIsPullback _ _ (IsPullback.of_hasPullback f g)) (by simp)

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPullback.isoOverPullback_hom_left_comp_snd** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.IsPullback`。
形式化陈述：isoOverPullback_hom_left_comp_snd {P : C} {fst : P ⟶ X} {snd : P ⟶ Y} (h :
 IsPullback fst snd f g) : dsimp% h.isoOverPullback.hom.left ≫ pullback.snd f g 
= snd
参数：h : IsPullback fst snd f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.isoIsPullback_hom_snd`：isoIsPullback_hom_snd (
h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) : (h.isoIsPullback _
 _ h').hom ≫ snd' = snd
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
lemma isoOverPullback_hom_left_comp_snd {P : C} {fst : P ⟶ X} {snd : P ⟶ Y}
    (h : IsPullback fst snd f g) :
    dsimp% h.isoOverPullback.hom.left ≫ pullback.snd f g = snd :=
  h.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f g)

set_option backward.defeqAttrib.useBackward true in
/-- An isomorphism `Over.mk p ≅ Over.mk (pullback.fst f g)` in `Over X` yields
an `IsPullback` square. -/
/-
**CategoryTheory.IsPullback.of_over_iso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.IsPullback`。
形式化陈述：of_over_iso {P : C} {p : P ⟶ X} (e : Over.mk p ≅ Over.mk (pullback.fst f g
)) : IsPullback p (e.hom.left ≫ pullback.snd f g) f g
参数：e : Over.mk p ≅ Over.mk (pullback.fst f g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.of_iso'`：of_iso' (h : IsPullback fst snd f g) 
{P' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'
} (e₁ : P' ≅ P) (e₂ : X…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
An isomorphism `Over.mk p ≅ Over.mk (pullback.fst f g)` in `Over X` yields
an `IsPullback` square.
-/
lemma of_over_iso {P : C} {p : P ⟶ X}
    (e : Over.mk p ≅ Over.mk (pullback.fst f g)) :
    IsPullback p (e.hom.left ≫ pullback.snd f g) f g :=
  (IsPullback.of_hasPullback f g).of_iso'
    ((Over.forget X).mapIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using Over.w e.hom) (by simp) (by simp) (by simp)

set_option backward.defeqAttrib.useBackward true in
/-- An `IsPullback` square over a cospan `(f, g)` is equivalent to an isomorphism
`Over.mk fst ≅ Over.mk (pullback.fst f g)` in `Over X`, together with the
second projection being determined by the isomorphism. -/
/-
**CategoryTheory.IsPullback.iff_exists_over_iso** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.IsPullback`。
形式化陈述：iff_exists_over_iso {P : C} {p : P ⟶ X} {q : P ⟶ Y} : IsPullback p q f g ↔
 exists e : Over.mk p ≅ Over.mk (pullback.fst f g), q = e.hom.left ≫ pullback.sn
d f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.IsPullback.isoOverPullback_hom_left_comp_snd`：isoOverPull
back_hom_left_comp_snd {P : C} {fst : P ⟶ X} {snd : P ⟶ Y} (h : IsPullback fst s
nd f g) : dsimp% h.isoOverPullback.hom.left ≫ pul…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.IsPullback.of_over_iso`：of_over_iso {P : C} {p : P ⟶ X} (
e : Over.mk p ≅ Over.mk (pullback.fst f g)) : IsPullback p (e.hom.left ≫ pullbac
k.snd f g) f g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
An `IsPullback` square over a cospan `(f, g)` is equivalent to an isomorphism
`Over.mk fst ≅ Over.mk (pullback.fst f g)` in `Over X`, together with the
second projection being determined by the isomorphism.
-/
lemma iff_exists_over_iso {P : C} {p : P ⟶ X} {q : P ⟶ Y} :
    IsPullback p q f g ↔
    ∃ e : Over.mk p ≅ Over.mk (pullback.fst f g),
      q = e.hom.left ≫ pullback.snd f g := by
  constructor
  · intro h
    exact ⟨h.isoOverPullback, by simp⟩
  · rintro ⟨e, rfl⟩
    exact of_over_iso e

end IsPullback

end IsPullbackOverPullback

namespace Limits

/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) {X' : C} (i : X' ⟶ X) [IsIso i] [HasPullback f g] :
    HasPullback (i ≫ f) g :=
  IsPullback.paste_vert
    (IsPullback.of_vert_isIso_mono (fst := pullback.fst _ _ ≫ inv i) (snd := 𝟙 (pullback f g)) <|
      ⟨by simp⟩) (.of_hasPullback f g) |>.hasPullback

@[simp]
/-
**CategoryTheory.Limits.HasPullback.comp_left_left_iff_of_isIso** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Limits.HasPullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} {f
 : X ⟶ Z} {g : Y ⟶ Z} {X' : C} (i : X' ⟶ X)   [CategoryTheory.IsIso i],   Catego
ryTheory.Limits.HasPullback (CategoryTheory.CategoryStruct.comp i f) g ↔ Categor
yTheory.Limits.HasPullback f g
参数：i : X' ⟶ X；CategoryTheory.CategoryStruct.comp i f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Limits.instHasPullbackCompOfIsIso`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) {X' : 
C} (i : X' ⟶ X)   [CategoryTheory.IsIs…
-/
lemma HasPullback.comp_left_left_iff_of_isIso
    {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {X' : C} (i : X' ⟶ X) [IsIso i] :
    HasPullback (i ≫ f) g ↔ HasPullback f g := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  rw [← IsIso.inv_hom_id_assoc i f]
  infer_instance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z Z' : C} {f : X ⟶ Z} {g : Y ⟶ Z'} (i : Z ⟶ Z') [IsIso i] [HasPullback (f ≫ i) g] :
    HasPullback f (g ≫ inv i) := by
  simpa using hasPullback_of_comp_mono (f ≫ i) g (inv i)
/-
**CategoryTheory.Limits.HasPullback.comp_left_right_iff_of_isIso** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits.HasPullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z Z' : C}
 {f : X ⟶ Z} {g : Y ⟶ Z'} (i : Z ⟶ Z')   [inst_1 : CategoryTheory.IsIso i],   Ca
tegoryTheory.Limits.HasPullback (CategoryTheory.CategoryStruct.comp f i) g ↔    
 CategoryTheory.Limits.HasPullback f (CategoryTheory.CategoryStruct.comp g (Cate
goryTheory.inv i))
参数：i : Z ⟶ Z'；CategoryTheory.CategoryStruct.comp f i；CategoryTheory.CategoryStru
ct.comp g (CategoryTheory.inv i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasPullbackCompInv`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y Z Z' : C} {f : X ⟶ Z} {g : Y ⟶ Z'} (i : Z
 ⟶ Z')   [inst_1 : CategoryTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
-/
lemma HasPullback.comp_left_right_iff_of_isIso
    {X Y Z Z' : C} {f : X ⟶ Z} {g : Y ⟶ Z'} (i : Z ⟶ Z') [IsIso i] :
    HasPullback (f ≫ i) g ↔ HasPullback f (g ≫ inv i) :=
  ⟨fun h ↦ inferInstance, fun h ↦ by simpa using hasPullback_of_comp_mono f (g ≫ inv i) i⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) {X' : C} (i : X ⟶ X') [IsIso i] [HasPushout f g] :
    HasPushout (f ≫ i) g :=
  IsPushout.paste_horiz (.of_hasPushout f g)
    (IsPushout.of_horiz_isIso_epi (inl := inv i ≫ pushout.inl _ _) (inr := 𝟙 (pushout f g)) <|
      ⟨by simp⟩) |>.hasPushout

@[simp]
/-
**CategoryTheory.Limits.HasPushout.comp_left_left_iff_of_isIso** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits.HasPushout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} {f
 : Z ⟶ X} {g : Z ⟶ Y} {X' : C} (i : X ⟶ X')   [CategoryTheory.IsIso i],   Catego
ryTheory.Limits.HasPushout (CategoryTheory.CategoryStruct.comp f i) g ↔ Category
Theory.Limits.HasPushout f g
参数：i : X ⟶ X'；CategoryTheory.CategoryStruct.comp f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.instHasPushoutCompOfIsIso`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) {X' : C
} (i : X ⟶ X')   [CategoryTheory.IsIs…
-/
lemma HasPushout.comp_left_left_iff_of_isIso
    {X Y Z : C} {f : Z ⟶ X} {g : Z ⟶ Y} {X' : C} (i : X ⟶ X') [IsIso i] :
    HasPushout (f ≫ i) g ↔ HasPushout f g := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  rw [← Category.comp_id f, ← IsIso.hom_inv_id i, ← Category.assoc]
  infer_instance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z Z' : C} {f : Z ⟶ X} {g : Z' ⟶ Y} (i : Z' ⟶ Z) [IsIso i] [HasPushout (i ≫ f) g] :
    HasPushout f (inv i ≫ g) := by
  simpa using hasPushout_of_epi_comp (i ≫ f) g (inv i)
/-
**CategoryTheory.Limits.HasPushout.comp_left_right_iff_of_isIso** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Limits.HasPushout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z Z' : C}
 {f : Z ⟶ X} {g : Z' ⟶ Y} (i : Z' ⟶ Z)   [inst_1 : CategoryTheory.IsIso i],   Ca
tegoryTheory.Limits.HasPushout (CategoryTheory.CategoryStruct.comp i f) g ↔     
CategoryTheory.Limits.HasPushout f (CategoryTheory.CategoryStruct.comp (Category
Theory.inv i) g)
参数：i : Z' ⟶ Z；CategoryTheory.CategoryStruct.comp i f；CategoryTheory.CategoryStru
ct.comp (CategoryTheory.inv i) g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasPushoutCompInv`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {X Y Z Z' : C} {f : Z ⟶ X} {g : Z' ⟶ Y} (i : Z'
 ⟶ Z)   [inst_1 : CategoryTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
-/
lemma HasPushout.comp_left_right_iff_of_isIso
    {X Y Z Z' : C} {f : Z ⟶ X} {g : Z' ⟶ Y} (i : Z' ⟶ Z) [IsIso i] :
    HasPushout (i ≫ f) g ↔ HasPushout f (inv i ≫ g) :=
  ⟨fun h ↦ inferInstance, fun h ↦ by simpa using hasPushout_of_epi_comp f (inv i ≫ g) i⟩

end Limits

end CategoryTheory

