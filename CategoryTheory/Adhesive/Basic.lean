/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!

# Adhesive categories

## Main definitions
- `CategoryTheory.IsPushout.IsVanKampen`: A convenience formulation for a pushout being
  a van Kampen colimit.
- `CategoryTheory.Adhesive`: A category is adhesive if it has pushouts and pullbacks along
  monomorphisms, and such pushouts are van Kampen.

## Main Results
- `CategoryTheory.Type.adhesive`: The category of `Type` is adhesive.
- `CategoryTheory.Adhesive.isPullback_of_isPushout_of_mono_left`: In adhesive categories,
  pushouts along monomorphisms are pullbacks.
- `CategoryTheory.Adhesive.mono_of_isPushout_of_mono_left`: In adhesive categories,
  monomorphisms are stable under pushouts.
- `CategoryTheory.Adhesive.toRegularMonoCategory`: Monomorphisms in adhesive categories are
  regular (this implies that adhesive categories are balanced).
- `CategoryTheory.adhesive_functor`: The category `C ⥤ D` is adhesive if `D`
  has all pullbacks and all pushouts and is adhesive

## References
- https://ncatlab.org/nlab/show/adhesive+category
- [Stephen Lack and Paweł Sobociński, Adhesive Categories][adhesive2004]

-/

@[expose] public section


namespace CategoryTheory

open Limits

universe v' u' v u

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

-- This only makes sense when the original diagram is a pushout.
/-- A convenient formulation for a pushout being a van Kampen colimit. For any commutative cube of
which a van Kampen pushout forms the bottom face and the back faces are pullbacks, the front faces
are pullbacks if and only if the top face is a pushout. See `IsPushout.isVanKampen_iff` below. -/
@[nolint unusedArguments]
/-
**CategoryTheory.IsPushout.IsVanKampen** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.IsPushout`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y Z 
: C} → {f : W ⟶ X} → {g : W ⟶ Y} → {h : X ⟶ Z} → {i : Y ⟶ Z} → CategoryTheory.Is
Pushout f g h i → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convenient formulation for a pushout being a van Kampen colimit. For any commu
tative cube of
which a van Kampen pushout forms the bottom face and the back faces are pullback
s, the front faces
are pullbacks if and only if the top face is a pushout. See `IsPushout.isVanKamp
en_iff` below.
-/
def IsPushout.IsVanKampen (_ : IsPushout f g h i) : Prop :=
  ∀ ⦃W' X' Y' Z' : C⦄ (f' : W' ⟶ X') (g' : W' ⟶ Y') (h' : X' ⟶ Z') (i' : Y' ⟶ Z') (αW : W' ⟶ W)
    (αX : X' ⟶ X) (αY : Y' ⟶ Y) (αZ : Z' ⟶ Z) (_ : IsPullback f' αW αX f)
    (_ : IsPullback g' αW αY g) (_ : CommSq h' αX αZ h) (_ : CommSq i' αY αZ i)
    (_ : CommSq f' g' h' i'), IsPushout f' g' h' i' ↔ IsPullback h' αX αZ h ∧ IsPullback i' αY αZ i

/-- If a van Kampen pushout forms the bottom face of a commutative "half-cube" whose front faces
are pullbacks, then there exist two back faces which are pullbacks and a top face which is a
pushout. -/
/-
**CategoryTheory.IsPushout.IsVanKampen.exists_cube_filling** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.IsPushout.IsVanKampen`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   {H : CategoryTheory.IsPushout f g
 h i},   H.IsVanKampen →     ∀ {X' Y' Z' : C} {h' : X' ⟶ Z'} {i' : Y' ⟶ Z'} {αX 
: X' ⟶ X} {αY : Y' ⟶ Y} {αZ : Z' ⟶ Z}       [CategoryTheory.Limits.HasPullback α
X f],       CategoryTheory.IsPullback h' αX αZ h →         CategoryTheory.IsPull
back i' αY αZ i →           ∃ W' f' g' αW,             CategoryTheory.IsPullback
 f' αW αX f ∧               CategoryTheory.IsPullback g' αW αY g ∧ CategoryTheor
y.IsPushout f' g' h' i'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `CategoryTheory.IsPullback.of_right'`：of_right' {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ 
: C} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {h₁₃ : X₁₁ ⟶ X₁₃} {v₁
₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂…
· 使用定理 `CategoryTheory.IsPullback.paste_horiz`：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ 
X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
 {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.IsPullback.lift_fst`：lift_fst (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ fst = h

--- 原说明 ---
If a van Kampen pushout forms the bottom face of a commutative "half-cube" whose
 front faces
are pullbacks, then there exist two back faces which are pullbacks and a top fac
e which is a
pushout.
-/
lemma IsPushout.IsVanKampen.exists_cube_filling {H : IsPushout f g h i} (H' : H.IsVanKampen)
    {X' Y' Z' : C} {h' : X' ⟶ Z'} {i' : Y' ⟶ Z'} {αX : X' ⟶ X} {αY : Y' ⟶ Y} {αZ : Z' ⟶ Z}
    [HasPullback αX f] (hh : IsPullback h' αX αZ h) (hi : IsPullback i' αY αZ i) :
    ∃ (W' : C) (f' : W' ⟶ X') (g' : W' ⟶ Y') (αW : W' ⟶ W),
      IsPullback f' αW αX f ∧ IsPullback g' αW αY g ∧ IsPushout f' g' h' i' := by
  let l := hi.lift ((pullback.fst αX f) ≫ h') ((pullback.snd αX f) ≫ g)
    (by simp only [Category.assoc, hh.toCommSq.w, pullback.condition_assoc, ← H.w])
  use (pullback αX f), (pullback.fst αX f), l, (pullback.snd αX f)
  refine ⟨IsPullback.of_hasPullback αX f, ?_, ?_⟩
  · refine IsPullback.of_right' ?_ hi
    rw [← H.w]
    exact IsPullback.paste_horiz (IsPullback.of_hasPullback αX f) hh
  · refine (H' (pullback.fst αX f) l h' i' (pullback.snd αX f) αX αY αZ
      (IsPullback.of_hasPullback αX f) ?_
        hh.toCommSq hi.toCommSq ⟨by simp only [IsPullback.lift_fst, l]⟩).2 ⟨hh, hi⟩
    · refine IsPullback.of_right' ?_ hi
      rw [← H.w]
      exact IsPullback.paste_horiz (IsPullback.of_hasPullback αX f) hh
/-
**CategoryTheory.IsPushout.IsVanKampen.flip** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.IsPushout.IsVanKampen`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   {H : CategoryTheory.IsPushout f g
 h i}, H.IsVanKampen → ⋯.IsVanKampen
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CommSq.flip`：flip (p : CommSq f g h i) : CommSq g f i h
-/
theorem IsPushout.IsVanKampen.flip {H : IsPushout f g h i} (H' : H.IsVanKampen) :
    H.flip.IsVanKampen := by
  introv W' hf hg hh hi w
  simpa only [IsPushout.flip_iff, IsPullback.flip_iff, and_comm] using
    H' g' f' i' h' αW αY αX αZ hg hf hi hh w.flip

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsPushout.isVanKampen_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.IsPushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   (H : CategoryTheory.IsPushout f g
 h i),   H.IsVanKampen ↔ CategoryTheory.IsVanKampenColimit (CategoryTheory.Limit
s.PushoutCocone.mk h i ⋯)
参数：H : CategoryTheory.IsPushout f g h i；CategoryTheory.Limits.PushoutCocone.mk h
 i ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsPushout.isColimit'`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {
inr : Y ⟶ P} (self : Cate…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.IsPullback.paste_horiz`：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ 
X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
 {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition_zero`：condition_zero (t : 
PushoutCocone f g) : t.ι.app WalkingSpan.zero = f ≫ t.inl
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CommSq.w_assoc`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y
 ⟶ Z},   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.of_horiz_isIso`：of_horiz_isIso [IsIso fst] [Is
Iso g] (sq : CommSq fst snd f g) : IsPullback fst snd f g
-/
theorem IsPushout.isVanKampen_iff (H : IsPushout f g h i) :
    H.IsVanKampen ↔ IsVanKampenColimit (PushoutCocone.mk h i H.w) := by
  constructor
  · intro H F' c' α fα eα hα
    refine Iff.trans ?_
        ((H (F'.map WalkingSpan.Hom.fst) (F'.map WalkingSpan.Hom.snd) (c'.ι.app _) (c'.ι.app _)
          (α.app _) (α.app _) (α.app _) fα (by convert! hα WalkingSpan.Hom.fst)
          (by convert! hα WalkingSpan.Hom.snd) ?_ ?_ ?_).trans ?_)
    · have : F'.map WalkingSpan.Hom.fst ≫ c'.ι.app WalkingSpan.left =
          F'.map WalkingSpan.Hom.snd ≫ c'.ι.app WalkingSpan.right := by
        simp only [Cocone.w]
      rw [(IsColimit.equivOfNatIsoOfIso (diagramIsoSpan F') c' (PushoutCocone.mk _ _ this)
            _).nonempty_congr]
      · exact ⟨fun h => ⟨⟨this⟩, h⟩, fun h => h.2⟩
      · refine Cocone.ext (Iso.refl c'.pt) ?_
        rintro (_ | _ | _) <;> dsimp <;>
          simp only [c'.w, Category.id_comp, Category.comp_id]
    · exact ⟨NatTrans.congr_app eα.symm _⟩
    · exact ⟨NatTrans.congr_app eα.symm _⟩
    · exact ⟨by simp⟩
    constructor
    · rintro ⟨h₁, h₂⟩ (_ | _ | _)
      · rw [← c'.w WalkingSpan.Hom.fst]; exact (hα WalkingSpan.Hom.fst).paste_horiz h₁
      exacts [h₁, h₂]
    · intro h; exact ⟨h _, h _⟩
  · introv H W' hf hg hh hi w
    refine
      Iff.trans ?_ ((H w.cocone ⟨by rintro (_ | _ | _); exacts [αW, αX, αY], ?_⟩ αZ ?_ ?_).trans ?_)
    rotate_left
    · rintro i _ (_ | _ | _)
      · dsimp; simp only [Functor.map_id, Category.comp_id, Category.id_comp]
      exacts [hf.w, hg.w]
    · ext (_ | _ | _)
      · simp [hh.w, hf.w_assoc]
      exacts [hh.w.symm, hi.w.symm]
    · rintro i _ (_ | _ | _)
      · dsimp; simp_rw [Functor.map_id]
        exact IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, Category.id_comp]⟩
      exacts [hf, hg]
    · constructor
      · intro h; exact ⟨h WalkingCospan.left, h WalkingCospan.right⟩
      · rintro ⟨h₁, h₂⟩ (_ | _ | _)
        · dsimp; rw [PushoutCocone.condition_zero]; exact hf.paste_horiz h₁
        exacts [h₁, h₂]
    · exact ⟨fun h => h.2, fun h => ⟨w, h⟩⟩

/-- A pushout is van Kampen if and only if whenever it forms the bottom face of a commutative
"half-cube", the front faces are pullbacks if and only if there exist back faces which are pullbacks
and a top face which is a pushout. -/
/-
**CategoryTheory.IsPushout.isVanKampen_iff'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.IsPushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   {H : CategoryTheory.IsPushout f g
 h i},   H.IsVanKampen ↔     ∀ ⦃X' Y' Z' : C⦄ (h' : X' ⟶ Z') (i' : Y' ⟶ Z') (αX 
: X' ⟶ X) (αY : Y' ⟶ Y) (αZ : Z' ⟶ Z),       CategoryTheory.CommSq h' αX αZ h → 
        CategoryTheory.CommSq i' αY αZ i →           ∀ [CategoryTheory.Limits.Ha
sPullback αX f],             CategoryTheory.IsPullback h' αX αZ h ∧ CategoryTheo
ry.IsPullback i' αY αZ i ↔               ∃ W' f' g' αW,                 Category
Theory.IsPullback f' αW αX f ∧                   CategoryTheory.IsPullback g' αW
 αY g ∧ CategoryTheory.IsPushout f' g' h' i'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.IsVanKampen.exists_cube_filling`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y}
 {h : X ⟶ Z} {i : Y ⟶ Z}   {H : CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用引理 `CategoryTheory.IsPullback.hasPullback`：hasPullback (h : IsPullback fst s
nd f g) : HasPullback f g where exists_limit
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.IsPushout.of_iso`：of_iso (h : IsPushout f g inl inr) {Z' 
X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'} (e
₁ : Z ≅ Z') (e₂ : X ≅…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsPullback.isoIsPullback_hom_fst`：isoIsPullback_hom_fst (
h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) : (h.isoIsPullback _
 _ h').hom ≫ fst' = fst
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.IsPullback.hom_ext`：hom_ext (hP : IsPullback fst snd f g)
 {W : C} {k l : W ⟶ P} (h₀ : k ≫ fst = l ≫ fst) (h₁ : k ≫ snd = l ≫ snd) : k = l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.isoIsPullback_hom_fst_assoc`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {P : C} (X Y : C) {Z : C} {fst : P ⟶ 
X} {snd : P ⟶ Y}   {f : X ⟶ Z} {g : Y ⟶ Z} …
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.IsPullback.isoIsPullback_hom_snd_assoc`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {P : C} (X Y : C) {Z : C} {fst : P ⟶ 
X} {snd : P ⟶ Y}   {f : X ⟶ Z} {g : Y ⟶ Z} …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
A pushout is van Kampen if and only if whenever it forms the bottom face of a co
mmutative
"half-cube", the front faces are pullbacks if and only if there exist back faces
 which are pullbacks
and a top face which is a pushout.
-/
theorem IsPushout.isVanKampen_iff' {H : IsPushout f g h i} :
    H.IsVanKampen ↔ ∀ ⦃X' Y' Z' : C⦄ (h' : X' ⟶ Z') (i' : Y' ⟶ Z')
      (αX : X' ⟶ X) (αY : Y' ⟶ Y) (αZ : Z' ⟶ Z)
      (_ : CommSq h' αX αZ h) (_ : CommSq i' αY αZ i) [HasPullback αX f],
      IsPullback h' αX αZ h ∧ IsPullback i' αY αZ i ↔
        ∃ (W' : C) (f' : W' ⟶ X') (g' : W' ⟶ Y') (αW : W' ⟶ W),
      IsPullback f' αW αX f ∧ IsPullback g' αW αY g ∧ IsPushout f' g' h' i' := by
  constructor
  · intro H' X' Y' Z' h' i' αX αY αZ sq_h sq_i _
    constructor
    · intro ⟨hh, hi⟩
      exact H'.exists_cube_filling hh hi
    · intro ⟨W', f', g', αW, hf, hg, H''⟩
      rwa [← H' f' g' h' i' αW αX αY αZ hf hg sq_h sq_i H''.toCommSq]
  · intro H' W' X' Y' Z' f' g' h' i' αW αX αY αZ hf hg sq_h sq_i cs
    let : HasPullback αX f := hf.hasPullback
    constructor
    · intro H''
      rw [H' h' i' αX αY αZ sq_h sq_i]
      refine ⟨W', f', g', αW, hf, hg, H''⟩
    · intro ⟨hh, hi⟩
      obtain ⟨W'', f'', g'', αW', hf', hg', hP⟩ := (H' h' i' αX αY αZ sq_h sq_i).1 ⟨hh, hi⟩
      refine hP.of_iso (IsPullback.isoIsPullback _ _ hf' hf)
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)
      · apply hi.hom_ext
        · simp [← cs.w, hP.w]
        · simp [hg.w, hg'.w]
/-
**CategoryTheory.IsPushout.isVanKampen_isPullback_isPullback_hom_ext** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.IsPushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   {H : CategoryTheory.IsPushout f g
 h i},   H.IsVanKampen →     ∀ {X' Y' Z' : C} {h' : X' ⟶ Z'} {i' : Y' ⟶ Z'} {αX 
: X' ⟶ X} [CategoryTheory.Limits.HasPullback αX f] {αY : Y' ⟶ Y}       {αZ : Z' 
⟶ Z} {W : C} {f₁ f₂ : Z' ⟶ W},       CategoryTheory.IsPullback h' αX αZ h →     
    CategoryTheory.IsPullback i' αY αZ i →           CategoryTheory.CategoryStru
ct.comp h' f₁ = CategoryTheory.CategoryStruct.comp h' f₂ →             CategoryT
heory.CategoryStruct.comp i' f₁ = CategoryTheory.CategoryStruct.comp i' f₂ → f₁ 
= f₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.IsVanKampen.exists_cube_filling`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y}
 {h : X ⟶ Z} {i : Y ⟶ Z}   {H : CategoryTheory…
· 使用引理 `CategoryTheory.IsPushout.hom_ext`：hom_ext (hP : IsPushout f g inl inr) {
W : C} {k l : P ⟶ W} (h₀ : inl ≫ k = inl ≫ l) (h₁ : inr ≫ k = inr ≫ l) : k = l
-/
lemma IsPushout.isVanKampen_isPullback_isPullback_hom_ext
    {H : IsPushout f g h i} (H' : H.IsVanKampen)
    {X' Y' Z' : C} {h' : X' ⟶ Z'} {i' : Y' ⟶ Z'}
    {αX : X' ⟶ X} [HasPullback αX f] {αY : Y' ⟶ Y} {αZ : Z' ⟶ Z} {W : C} {f₁ f₂ : Z' ⟶ W}
    (hh : IsPullback h' αX αZ h) (hi : IsPullback i' αY αZ i)
    (h'_w : h' ≫ f₁ = h' ≫ f₂) (i'_w : i' ≫ f₁ = i' ≫ f₂) : f₁ = f₂ := by
  obtain ⟨W', f', g', αW, _, _, H''⟩ := H'.exists_cube_filling hh hi
  exact H''.hom_ext h'_w i'_w

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.is_coprod_iff_isPushout** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：is_coprod_iff_isPushout {X E Y YE : C} (c : BinaryCofan X E) (hc : IsColim
it c) {f : X ⟶ Y} {iY : Y ⟶ YE} {fE : c.pt ⟶ YE} (H : CommSq f c.inl iY fE) : No
nempty (IsColimit (BinaryCofan.mk (c.inr ≫ fE) iY)) ↔ IsPushout f c.inl iY fE
参数：c : BinaryCofan X E；hc : IsColimit c；H : CommSq f c.inl iY fE。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.Limits.BinaryCofan.IsColimit.inr_desc`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {X Y W : C} {s : CategoryTheory.Limits.Bi
naryCofan X Y}   (h : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.BinaryCofan.IsColimit.hom_ext`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.Bin
aryCofan X Y}   (h : CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommSq.w_assoc`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y
 ⟶ Z},   CategoryTh…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition`：condition (t : PushoutCoc
one f g) : f ≫ inl t = g ≫ inr t
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.PushoutCocone.IsColimit.hom_ext`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   {t
 : CategoryTheory.Limits.PushoutCocone f g}…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
-/
theorem is_coprod_iff_isPushout {X E Y YE : C} (c : BinaryCofan X E) (hc : IsColimit c) {f : X ⟶ Y}
    {iY : Y ⟶ YE} {fE : c.pt ⟶ YE} (H : CommSq f c.inl iY fE) :
    Nonempty (IsColimit (BinaryCofan.mk (c.inr ≫ fE) iY)) ↔ IsPushout f c.inl iY fE := by
  constructor
  · rintro ⟨h⟩
    refine ⟨H, ⟨Limits.PushoutCocone.isColimitAux' _ ?_⟩⟩
    intro s
    dsimp
    refine ⟨BinaryCofan.IsColimit.desc h (c.inr ≫ s.inr) s.inl,
        BinaryCofan.IsColimit.inr_desc h _ _, ?_, ?_⟩
    · apply BinaryCofan.IsColimit.hom_ext hc
      · rw [← H.w_assoc]; erw [h.fac _ ⟨WalkingPair.right⟩]; exact s.condition
      · rw [← Category.assoc]; exact h.fac _ ⟨WalkingPair.left⟩
    · intro m e₁ e₂
      apply BinaryCofan.IsColimit.hom_ext h
      · dsimp
        rw [Category.assoc, e₂, eq_comm]; exact h.fac _ ⟨WalkingPair.left⟩
      · refine e₁.trans (Eq.symm ?_); exact h.fac _ _
  · refine fun H => ⟨?_⟩
    fapply Limits.BinaryCofan.isColimitMk
    · exact fun s => H.isColimit.desc (PushoutCocone.mk s.inr _ <|
        (hc.fac (BinaryCofan.mk (f ≫ s.inr) s.inl) ⟨WalkingPair.left⟩).symm)
    · intro s
      rw [Category.assoc]
      erw [H.isColimit.fac _ WalkingSpan.right]
      erw [hc.fac]
      rfl
    · intro s; exact H.isColimit.fac _ WalkingSpan.left
    · intro s m e₁ e₂
      apply PushoutCocone.IsColimit.hom_ext H.isColimit
      · symm; exact (H.isColimit.fac _ WalkingSpan.left).trans e₂.symm
      · rw [H.isColimit.fac _ WalkingSpan.right]
        apply BinaryCofan.IsColimit.hom_ext hc
        · erw [hc.fac]
          erw [← H.w_assoc]
          rw [e₂]
          rfl
        · refine ((Category.assoc _ _ _).symm.trans e₁).trans ?_; symm; exact hc.fac _ _

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsPushout.isVanKampen_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.IsPushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W E X Z : C} (c 
: CategoryTheory.Limits.BinaryCofan W E)   [CategoryTheory.FinitaryExtensive C] 
[CategoryTheory.Limits.HasPullbacks C] (hc : CategoryTheory.Limits.IsColimit c) 
  (f : W ⟶ X) (h : X ⟶ Z) (i : c.pt ⟶ Z) (H : CategoryTheory.IsPushout f c.inl h
 i), H.IsVanKampen
参数：c : CategoryTheory.Limits.BinaryCofan W E；hc : CategoryTheory.Limits.IsColimi
t c；f : W ⟶ X；h : X ⟶ Z；i : c.pt ⟶ Z；H : CategoryTheory.IsPushout f c.inl h i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.is_coprod_iff_isPushout`：is_coprod_iff_isPushout {X E Y Y
E : C} (c : BinaryCofan X E) (hc : IsColimit c) {f : X ⟶ Y} {iY : Y ⟶ YE} {fE : 
c.pt ⟶ YE} (H : CommSq f c.i…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.BinaryCofan.isVanKampen_iff`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y : C} (c : CategoryTheory.Limits.BinaryCofan X 
Y),   CategoryTheory.IsVanKampen…
· 使用定理 `CategoryTheory.FinitaryExtensive.vanKampen`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C]   {F : Categor
yTheory.Functor (CategoryTheory.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.IsPullback.of_right`：of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : 
C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ 
: X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ …
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.IsPullback.paste_horiz`：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ 
X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
 {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
· 使用定理 `CategoryTheory.Limits.BinaryCofan.IsColimit.hom_ext`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.Bin
aryCofan X Y}   (h : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso`：of_vert_isIso [IsIso snd] [IsIs
o f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem IsPushout.isVanKampen_inl {W E X Z : C} (c : BinaryCofan W E) [FinitaryExtensive C]
    [HasPullbacks C] (hc : IsColimit c) (f : W ⟶ X) (h : X ⟶ Z) (i : c.pt ⟶ Z)
    (H : IsPushout f c.inl h i) : H.IsVanKampen := by
  obtain ⟨hc₁⟩ := (is_coprod_iff_isPushout c hc H.1).mpr H
  introv W' hf hg hh hi w
  obtain ⟨hc₂⟩ := ((BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen c hc)
    (BinaryCofan.mk _ (pullback.fst _ _)) _ _ _ hg.w.symm pullback.condition.symm).mpr
    ⟨hg, IsPullback.of_hasPullback αY c.inr⟩
  refine (is_coprod_iff_isPushout _ hc₂ w).symm.trans ?_
  refine ((BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hc₁)
    (BinaryCofan.mk _ _) (pullback.snd _ _) _ _ ?_ hh.w.symm).trans ?_
  · dsimp; rw [← pullback.condition_assoc, Category.assoc, hi.w]
  constructor
  · rintro ⟨hc₃, hc₄⟩
    refine ⟨hc₄, ?_⟩
    let Y'' := pullback αZ i
    let cmp : Y' ⟶ Y'' := pullback.lift i' αY hi.w
    have e₁ : (g' ≫ cmp) ≫ pullback.snd _ _ = αW ≫ c.inl := by
      rw [Category.assoc, pullback.lift_snd, hg.w]
    have e₂ : (pullback.fst _ _ ≫ cmp : pullback αY c.inr ⟶ _) ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ c.inr := by
      rw [Category.assoc, pullback.lift_snd, pullback.condition]
    obtain ⟨hc₄⟩ := ((BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen c hc)
      (BinaryCofan.mk _ _) αW _ _ e₁.symm e₂.symm).mpr <| by
        constructor
        · apply IsPullback.of_right _ e₁ (IsPullback.of_hasPullback _ _)
          rw [Category.assoc, pullback.lift_fst, ← H.w, ← w.w]; exact hf.paste_horiz hc₄
        · apply IsPullback.of_right _ e₂ (IsPullback.of_hasPullback _ _)
          rw [Category.assoc, pullback.lift_fst]; exact hc₃
    rw [← Category.id_comp αZ, ← show cmp ≫ pullback.snd _ _ = αY from pullback.lift_snd _ _ _]
    apply IsPullback.paste_vert _ (IsPullback.of_hasPullback αZ i)
    have : cmp = (hc₂.coconePointUniqueUpToIso hc₄).hom := by
      apply BinaryCofan.IsColimit.hom_ext hc₂
      exacts [(hc₂.comp_coconePointUniqueUpToIso_hom hc₄ ⟨WalkingPair.left⟩).symm,
        (hc₂.comp_coconePointUniqueUpToIso_hom hc₄ ⟨WalkingPair.right⟩).symm]
    rw [this]
    exact IsPullback.of_vert_isIso ⟨by rw [← this, Category.comp_id, pullback.lift_fst]⟩
  · rintro ⟨hc₃, hc₄⟩
    exact ⟨(IsPullback.of_hasPullback αY c.inr).paste_horiz hc₄, hc₃⟩
/-
**CategoryTheory.IsPushout.IsVanKampen.isPullback_of_mono_left** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.IsPushout.IsVanKampen`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Mono f] {H : Cate
goryTheory.IsPushout f g h i}, H.IsVanKampen → CategoryTheory.IsPullback f g h i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.IsKernelPair.id_of_mono`：id_of_mono [Mono f] : IsKernelPa
ir f (𝟙 _) (𝟙 _)
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
· 使用定理 `CategoryTheory.CommSq.flip`：flip (p : CommSq f g h i) : CommSq g f i h
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `CategoryTheory.IsPushout.of_horiz_isIso`：of_horiz_isIso [IsIso f] [IsIso
 inr] (sq : CommSq f g inl inr) : IsPushout f g inl inr
-/
theorem IsPushout.IsVanKampen.isPullback_of_mono_left [Mono f] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : IsPullback f g h i :=
  ((H' (𝟙 _) g g (𝟙 Y) (𝟙 _) f (𝟙 _) i (IsKernelPair.id_of_mono f)
      (IsPullback.of_vert_isIso ⟨by simp⟩) H.1.flip ⟨rfl⟩ ⟨by simp⟩).mp
    (IsPushout.of_horiz_isIso ⟨by simp⟩)).1.flip
/-
**CategoryTheory.IsPushout.IsVanKampen.isPullback_of_mono_right** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.IsPushout.IsVanKampen`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Mono g] {H : Cate
goryTheory.IsPushout f g h i}, H.IsVanKampen → CategoryTheory.IsPullback f g h i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
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
· 使用定理 `CategoryTheory.IsKernelPair.id_of_mono`：id_of_mono [Mono f] : IsKernelPa
ir f (𝟙 _) (𝟙 _)
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `CategoryTheory.IsPushout.of_vert_isIso`：of_vert_isIso [IsIso g] [IsIso i
nl] (sq : CommSq f g inl inr) : IsPushout f g inl inr
-/
theorem IsPushout.IsVanKampen.isPullback_of_mono_right [Mono g] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : IsPullback f g h i :=
  ((H' f (𝟙 _) (𝟙 _) f (𝟙 _) (𝟙 _) g h (IsPullback.of_vert_isIso ⟨by simp⟩)
      (IsKernelPair.id_of_mono g) ⟨rfl⟩ H.1 ⟨by simp⟩).mp
    (IsPushout.of_vert_isIso ⟨by simp⟩)).2
/-
**CategoryTheory.IsPushout.IsVanKampen.mono_of_mono_left** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.IsPushout.IsVanKampen`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Mono f] {H : Cate
goryTheory.IsPushout f g h i}, H.IsVanKampen → CategoryTheory.Mono i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsKernelPair.mono_of_isIso_fst`：mono_of_isIso_fst (h : Is
KernelPair f a b) [IsIso a] : Mono f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.IsKernelPair.id_of_mono`：id_of_mono [Mono f] : IsKernelPa
ir f (𝟙 _) (𝟙 _)
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
· 使用定理 `CategoryTheory.CommSq.flip`：flip (p : CommSq f g h i) : CommSq g f i h
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `CategoryTheory.IsPushout.of_horiz_isIso`：of_horiz_isIso [IsIso f] [IsIso
 inr] (sq : CommSq f g inl inr) : IsPushout f g inl inr
-/
theorem IsPushout.IsVanKampen.mono_of_mono_left [Mono f] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : Mono i :=
  IsKernelPair.mono_of_isIso_fst
    ((H' (𝟙 _) g g (𝟙 Y) (𝟙 _) f (𝟙 _) i (IsKernelPair.id_of_mono f)
        (IsPullback.of_vert_isIso ⟨by simp⟩) H.1.flip ⟨rfl⟩ ⟨by simp⟩).mp
      (IsPushout.of_horiz_isIso ⟨by simp⟩)).2
/-
**CategoryTheory.IsPushout.IsVanKampen.mono_of_mono_right** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.IsPushout.IsVanKampen`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Mono g] {H : Cate
goryTheory.IsPushout f g h i}, H.IsVanKampen → CategoryTheory.Mono h
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsKernelPair.mono_of_isIso_fst`：mono_of_isIso_fst (h : Is
KernelPair f a b) [IsIso a] : Mono f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
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
· 使用定理 `CategoryTheory.IsKernelPair.id_of_mono`：id_of_mono [Mono f] : IsKernelPa
ir f (𝟙 _) (𝟙 _)
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `CategoryTheory.IsPushout.of_vert_isIso`：of_vert_isIso [IsIso g] [IsIso i
nl] (sq : CommSq f g inl inr) : IsPushout f g inl inr
-/
theorem IsPushout.IsVanKampen.mono_of_mono_right [Mono g] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : Mono h :=
  IsKernelPair.mono_of_isIso_fst
    ((H' f (𝟙 _) (𝟙 _) f (𝟙 _) (𝟙 _) g h (IsPullback.of_vert_isIso ⟨by simp⟩)
        (IsKernelPair.id_of_mono g) ⟨rfl⟩ H.1 ⟨by simp⟩).mp
      (IsPushout.of_vert_isIso ⟨by simp⟩)).1

/-- A category is adhesive if it has pushouts and pullbacks along monomorphisms,
and such pushouts are van Kampen. -/
/-
**CategoryTheory.Adhesive** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category is adhesive if it has pushouts and pullbacks along monomorphisms,
and such pushouts are van Kampen.
-/
class Adhesive (C : Type u) [Category.{v} C] : Prop where
  [hasPullback_of_mono_left : ∀ {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [Mono f], HasPullback f g]
  [hasPushout_of_mono_left : ∀ {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y) [Mono f], HasPushout f g]
  van_kampen : ∀ {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} [Mono f]
    (H : IsPushout f g h i), H.IsVanKampen

attribute [instance] Adhesive.hasPullback_of_mono_left Adhesive.hasPushout_of_mono_left
/-
**CategoryTheory.Adhesive.van_kampen'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Adhesive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Adhesive C] [Cate
goryTheory.Mono g] (H : CategoryTheory.IsPushout f g h i), H.IsVanKampen
参数：H : CategoryTheory.IsPushout f g h i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.IsVanKampen.flip`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i
 : Y ⟶ Z}   {H : CategoryTheory…
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `CategoryTheory.Adhesive.van_kampen`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Adhesive C] {W X Y Z : C} {f : W ⟶ X
}   {g : W ⟶ Y} {h : X ⟶…
-/
theorem Adhesive.van_kampen' [Adhesive C] [Mono g] (H : IsPushout f g h i) : H.IsVanKampen :=
  (Adhesive.van_kampen H.flip).flip
/-
**CategoryTheory.Adhesive.isPullback_of_isPushout_of_mono_left** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Adhesive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Adhesive C],   Ca
tegoryTheory.IsPushout f g h i → ∀ [CategoryTheory.Mono f], CategoryTheory.IsPul
lback f g h i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.IsVanKampen.isPullback_of_mono_left`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W 
⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Mon…
· 使用定理 `CategoryTheory.Adhesive.van_kampen`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Adhesive C] {W X Y Z : C} {f : W ⟶ X
}   {g : W ⟶ Y} {h : X ⟶…
-/
theorem Adhesive.isPullback_of_isPushout_of_mono_left [Adhesive C] (H : IsPushout f g h i)
    [Mono f] : IsPullback f g h i :=
  (Adhesive.van_kampen H).isPullback_of_mono_left
/-
**CategoryTheory.Adhesive.isPullback_of_isPushout_of_mono_right** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Adhesive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Adhesive C],   Ca
tegoryTheory.IsPushout f g h i → ∀ [CategoryTheory.Mono g], CategoryTheory.IsPul
lback f g h i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.IsVanKampen.isPullback_of_mono_right`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W
 ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Mon…
· 使用定理 `CategoryTheory.Adhesive.van_kampen'`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶
 Z}   [CategoryTheory.Adh…
-/
theorem Adhesive.isPullback_of_isPushout_of_mono_right [Adhesive C] (H : IsPushout f g h i)
    [Mono g] : IsPullback f g h i :=
  (Adhesive.van_kampen' H).isPullback_of_mono_right
/-
**CategoryTheory.Adhesive.mono_of_isPushout_of_mono_left** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Adhesive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Adhesive C], Cate
goryTheory.IsPushout f g h i → ∀ [CategoryTheory.Mono f], CategoryTheory.Mono i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.IsVanKampen.mono_of_mono_left`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {
h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Mon…
· 使用定理 `CategoryTheory.Adhesive.van_kampen`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Adhesive C] {W X Y Z : C} {f : W ⟶ X
}   {g : W ⟶ Y} {h : X ⟶…
-/
theorem Adhesive.mono_of_isPushout_of_mono_left [Adhesive C] (H : IsPushout f g h i) [Mono f] :
    Mono i :=
  (Adhesive.van_kampen H).mono_of_mono_left
/-
**CategoryTheory.Adhesive.mono_of_isPushout_of_mono_right** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Adhesive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Adhesive C], Cate
goryTheory.IsPushout f g h i → ∀ [CategoryTheory.Mono g], CategoryTheory.Mono h
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.IsVanKampen.mono_of_mono_right`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} 
{h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Mon…
· 使用定理 `CategoryTheory.Adhesive.van_kampen'`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶
 Z}   [CategoryTheory.Adh…
-/
theorem Adhesive.mono_of_isPushout_of_mono_right [Adhesive C] (H : IsPushout f g h i) [Mono g] :
    Mono h :=
  (Adhesive.van_kampen' H).mono_of_mono_right

attribute [local instance] Limits.hasPullback_symmetry in
/-
**CategoryTheory.Adhesive.isPushout_isPullback_isPullback_hom_ext** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Adhesive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Adhesive C] [Cate
goryTheory.Mono f],   CategoryTheory.IsPushout f g h i →     ∀ {X' Y' Z' : C} {h
' : X' ⟶ Z'} {i' : Y' ⟶ Z'} {αX : X' ⟶ X} {αY : Y' ⟶ Y} {αZ : Z' ⟶ Z} {W : C} {f
₁ f₂ : Z' ⟶ W},       CategoryTheory.IsPullback h' αX αZ h →         CategoryThe
ory.IsPullback i' αY αZ i →           CategoryTheory.CategoryStruct.comp h' f₁ =
 CategoryTheory.CategoryStruct.comp h' f₂ →             CategoryTheory.CategoryS
truct.comp i' f₁ = CategoryTheory.CategoryStruct.comp i' f₂ → f₁ = f₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.isVanKampen_isPullback_isPullback_hom_ext`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {
g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   {H : CategoryTheory…
· 使用定理 `CategoryTheory.Adhesive.van_kampen`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Adhesive C] {W X Y Z : C} {f : W ⟶ X
}   {g : W ⟶ Y} {h : X ⟶…
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `CategoryTheory.Adhesive.hasPullback_of_mono_left`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Adhesive C] {X Y S : C
} (f : X ⟶ S)   (g : Y ⟶ S) [CategoryT…
-/
lemma Adhesive.isPushout_isPullback_isPullback_hom_ext [Adhesive C] [Mono f] (H : IsPushout f g h i)
    {X' Y' Z' : C} {h' : X' ⟶ Z'} {i' : Y' ⟶ Z'}
    {αX : X' ⟶ X} {αY : Y' ⟶ Y} {αZ : Z' ⟶ Z}
    {W : C} {f₁ f₂ : Z' ⟶ W}
    (hh : IsPullback h' αX αZ h) (hi : IsPullback i' αY αZ i)
    (h'_w : h' ≫ f₁ = h' ≫ f₂) (i'_w : i' ≫ f₁ = i' ≫ f₂) : f₁ = f₂ :=
  IsPushout.isVanKampen_isPullback_isPullback_hom_ext (Adhesive.van_kampen H) hh hi h'_w i'_w

attribute [local instance] Limits.hasPullback_symmetry in
open IsPullback IsPushout pullback pushout in
/-- If `a : A ⟶ Z` and `b : B ⟶ Z` are monomorphisms in an adhesive category, then the map
`pushout (pullback.fst a b) (pullback.snd a b) ⟶ Z` induced by their pullback is a monomorphism.
See Theorem 5.1 in Lack and Sobociński. -/
/-
**CategoryTheory.Adhesive.desc_mono_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Adhesive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Adhesive C] {Z A B : C} {a : A ⟶ Z}   {b : B ⟶ Z} [inst_2 : CategoryTheo
ry.Mono a] [inst_3 : CategoryTheory.Mono b],   CategoryTheory.Mono (CategoryTheo
ry.Limits.pushout.desc a b ⋯)
参数：CategoryTheory.Limits.pushout.desc a b ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `CategoryTheory.Adhesive.hasPullback_of_mono_left`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Adhesive C] {X Y S : C
} (f : X ⟶ S)   (g : Y ⟶ S) [CategoryT…
· 使用定理 `CategoryTheory.Adhesive.hasPushout_of_mono_left`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Adhesive C] {X Y S : C}
 (f : S ⟶ X)   (g : S ⟶ Y) [CategoryT…
· 使用定理 `CategoryTheory.Limits.pullback.fst_of_mono`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cat
egoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Adhesive.mono_of_isPushout_of_mono_right`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} 
{h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Adh…
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
· 使用定理 `CategoryTheory.Limits.pullback.snd_of_mono`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cat
egoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Adhesive.mono_of_isPushout_of_mono_left`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {
h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Adh…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `CategoryTheory.IsPushout.IsVanKampen.exists_cube_filling`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y}
 {h : X ⟶ Z} {i : Y ⟶ Z}   {H : CategoryTheory…
· 使用定理 `CategoryTheory.Adhesive.van_kampen`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Adhesive C] {W X Y Z : C} {f : W ⟶ X
}   {g : W ⟶ Y} {h : X ⟶…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_fst`：isoPullback_hom_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.fst _ _
 = fst
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Adhesive.isPushout_isPullback_isPullback_hom_ext`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g :
 W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}   [CategoryTheory.Adh…
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.pushout.inl_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPushout …
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `a : A ⟶ Z` and `b : B ⟶ Z` are monomorphisms in an adhesive category, then t
he map
`pushout (pullback.fst a b) (pullback.snd a b) ⟶ Z` induced by their pullback is
 a monomorphism.
See Theorem 5.1 in Lack and Sobociński.
-/
instance Adhesive.desc_mono_of_mono [Adhesive C] {Z A B : C}
    {a : A ⟶ Z} {b : B ⟶ Z} [Mono a] [Mono b] :
    Mono (pushout.desc a b pullback.condition) where
  right_cancellation {K} f g w := by
    /- First, take the pullback of `a` and `b` and then form the pushout of the projection maps:
     `pullback a b` -> `B`
          |             |
          |            `v`
          |             |
          v             v
         `A` ---`u`---> C -/
    let u := pushout.inl (pullback.fst a b) (pullback.snd a b)
    let v := pushout.inr (pullback.fst a b) (pullback.snd a b)
    let : Mono u :=
      mono_of_isPushout_of_mono_right (of_hasPushout (pullback.fst a b) (pullback.snd a b))
    let : Mono v :=
      mono_of_isPushout_of_mono_left (of_hasPushout (pullback.fst a b) (pullback.snd a b))
    /- Then form the following pullbacks:
     L₁ --`l₁`-> K <--`l₂`-- L₂
     |           |           |
    `f₁`        `f`         `f₂`
     |           |           |
     v           v           v
    `A` --`u`--> C <--`v`-- `B`

     M₁ --`m₁`-> K <--`m₂`-- M₂
     |           |           |
    `g₁`        `g`         `g₂`
     |           |           |
     v           v           v
    `A` --`u`--> C <--`v`-- `B` -/
    let sq_f_u := of_hasPullback f u
    let sq_f_v := of_hasPullback f v
    let sq_g_u := of_hasPullback g u
    let sq_g_v := of_hasPullback g v
    /- Finally, form the following pullbacks:
     N₁₁ --m₁₁-> M₁ <--m₁₂-- N₁₂
     |           |           |
    l₁₁        `m₁`         l₁₂
     |           |           |
     v           v           v
    L₁ --`l₁`--> K <--`l₂`-- L₂
     ^           ^           ^
     |           |           |
    l₂₁        `m₂`         l₂₂
     |           |           |
    N₂₁ --m₂₁--> M₂ <--m₂₂-- N₂₂
    -/
    let l₁ := pullback.fst f u
    let f₁ := pullback.snd f u
    let l₂ := pullback.fst f v
    let f₂ := pullback.snd f v
    let m₁ := pullback.fst g u
    let g₁ := pullback.snd g u
    let m₂ := pullback.fst g v
    let g₂ := pullback.snd g v
    obtain ⟨_, f', _, _, p₁, _, h₁⟩ :=
      (van_kampen (of_hasPushout _ _)).exists_cube_filling sq_f_u sq_f_v
    let : Mono f' := by
      rw [← p₁.isoPullback_hom_fst]
      infer_instance
    /- apply `isPushout_isPullback_isPullback_hom_ext` to reduce `f = g` to `m₁ ≫ f = m₁ ≫ g`
      and `m₂ ≫ f = m₂ ≫ g`. -/
    apply isPushout_isPullback_isPullback_hom_ext (of_hasPushout _ _) sq_g_u sq_g_v
    · let sq₁₁ := of_hasPullback m₁ l₁
      let sq₁₂ := of_hasPullback m₁ l₂
      /- apply `isPushout_isPullback_isPullback_hom_ext` to reduce `m₁ ≫ f = m₁ ≫ g` to
        `m₁₁ ≫ m₁ ≫ f = m₁₁ ≫ m₁ ≫ g` and `m₁₂ ≫ m₁ ≫ f = m₁₂ ≫ m₁ ≫ g`. -/
      apply isPushout_isPullback_isPullback_hom_ext h₁ sq₁₁ sq₁₂
      · rw [pullback.condition_assoc, sq_f_u.w, sq_g_u.w, ← Category.assoc, ← Category.assoc]
        refine ?_ =≫ u
        let : Mono (u ≫ pushout.desc a b pullback.condition) := by rwa [pushout.inl_desc]
        rw [← cancel_mono (u ≫ pushout.desc a b pullback.condition), Category.assoc,
          ← sq_f_u.w_assoc, w, ← pullback.condition_assoc, Category.assoc, ← sq_g_u.w_assoc]
      · have : (pullback.fst m₁ l₂ ≫ g₁) ≫ a = (pullback.snd m₁ l₂ ≫ f₂) ≫ b := by
          rw [← _ ≫= pushout.inl_desc a b pullback.condition, Category.assoc, ← sq_g_u.w_assoc,
            sq₁₂.w_assoc, ← w, Category.assoc, pullback.condition_assoc, pushout.inr_desc]
        rw [sq₁₂.w_assoc, sq_f_v.w, ← Category.assoc, ← pullback.lift_snd_assoc _ _ this,
          ← pushout.condition, pullback.lift_fst_assoc _ _ this, Category.assoc, sq_g_u.w]
    · let sq₂₁ := of_hasPullback m₂ l₁
      let sq₂₂ := of_hasPullback m₂ l₂
      /- apply `isPushout_isPullback_isPullback_hom_ext` to reduce `m₂ ≫ f = m₂ ≫ g` to
        `m₂₁ ≫ m₂ ≫ f = m₂₁ ≫ m₂ ≫ g` and `m₂₂ ≫ m₂ ≫ f = m₂₂ ≫ m₂ ≫ g`. -/
      apply isPushout_isPullback_isPullback_hom_ext h₁ sq₂₁ sq₂₂
      · have : (pullback.snd m₂ l₁ ≫ f₁) ≫ a = (pullback.fst m₂ l₁ ≫ g₂) ≫ b := by
          rw [← _ ≫= pushout.inl_desc a b pullback.condition, Category.assoc, ← sq_f_u.w_assoc,
            w, ← sq₂₁.w_assoc, Category.assoc, sq_g_v.w_assoc, pushout.inr_desc]
        rw [sq₂₁.w_assoc, sq_f_u.w, ← Category.assoc, ← pullback.lift_fst_assoc _ _ this,
          pushout.condition, pullback.lift_snd_assoc _ _ this, sq_g_v.w, Category.assoc]
      · rw [sq₂₂.w_assoc, sq_f_v.w, sq_g_v.w, ← Category.assoc, ← Category.assoc]
        refine ?_ =≫ v
        let : Mono (v ≫ pushout.desc a b pullback.condition) := by rwa [pushout.inr_desc]
        rw [← cancel_mono (v ≫ pushout.desc a b pullback.condition), Category.assoc,
          ← sq_f_v.w_assoc, w, ← pullback.condition_assoc, Category.assoc,
          ← sq_g_v.w_assoc]
/-
**CategoryTheory.Type.adhesive** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Type`。
形式化陈述：CategoryTheory.Adhesive (Type u)
参数：Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.IsPushout.IsVanKampen.flip`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i
 : Y ⟶ Z}   {H : CategoryTheory…
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `CategoryTheory.IsPushout.isVanKampen_inl`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W E X Z : C} (c : CategoryTheory.Limits.BinaryCofan 
W E)   [CategoryTheory.Finitar…
· 使用定理 `CategoryTheory.types.finitaryExtensive`：CategoryTheory.FinitaryExtensive
 (Type u)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
-/
instance Type.adhesive : Adhesive (Type u) :=
  ⟨fun {_ _ _ _ f _ _ _ _} H =>
    (IsPushout.isVanKampen_inl _ (Types.isCoprodOfMono f) _ _ _ H.flip).flip⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (priority := 100) Adhesive.toRegularMonoCategory [Adhesive C] :
    IsRegularMonoCategory C :=
  ⟨fun f _ => ⟨⟨{
      Z := pushout f f
      left := pushout.inl _ _
      right := pushout.inr _ _
      w := pushout.condition
      isLimit := (Adhesive.isPullback_of_isPushout_of_mono_left
        (IsPushout.of_hasPushout f f)).isLimitFork }⟩⟩⟩

-- This then implies that adhesive categories are balanced
/-
**CategoryTheory.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [Adhesive C] : Balanced C :=
  inferInstance

section functor

universe v'' u''

variable {D : Type u''} [Category.{v''} D]

/-
**CategoryTheory.adhesive_functor** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：adhesive_functor [Adhesive C] [HasPullbacks C] [HasPushouts C] : Adhesive 
(D ⥤ C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPushout.isVanKampen_iff`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i 
: Y ⟶ Z}   (H : CategoryTheory…
· 使用定理 `CategoryTheory.isVanKampenColimit_of_evaluation`：isVanKampenColimit_of_e
valuation [HasPullbacks D] [HasColimitsOfShape J D] (F : J ⥤ C ⥤ D) (c : Cocone 
F) (hc : forall x : C, IsVanKampenCol…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.IsVanKampenColimit.precompose_isIso_iff`：∀ {J : Type v'} 
[inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheor
y.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.IsVanKampenColimit.of_iso`：∀ {J : Type v'} [inst : Catego
ryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPushout.map`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   
(F : CategoryTheor…
· 使用定理 `CategoryTheory.Adhesive.van_kampen`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Adhesive C] {W X Y Z : C} {f : W ⟶ X
}   {g : W ⟶ Y} {h : X ⟶…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
instance adhesive_functor [Adhesive C] [HasPullbacks C] [HasPushouts C] :
    Adhesive (D ⥤ C) := by
  constructor
  intro W X Y Z f g h i hf H
  rw [IsPushout.isVanKampen_iff]
  apply isVanKampenColimit_of_evaluation
  intro x
  refine (IsVanKampenColimit.precompose_isIso_iff (diagramIsoSpan _).inv).mp ?_
  refine IsVanKampenColimit.of_iso ?_ (PushoutCocone.isoMk _).symm
  refine (IsPushout.isVanKampen_iff (H.map ((evaluation _ _).obj x))).mp ?_
  apply Adhesive.van_kampen
/-
**CategoryTheory.adhesive_of_preserves_and_reflects** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory`。
形式化陈述：adhesive_of_preserves_and_reflects (F : C ⥤ D) [Adhesive D] [H₁ : forall {
X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [Mono f], HasPullback f g] [H₂ : forall {X Y 
S : C} (f : S ⟶ X) (g : S ⟶ Y) [Mono f], HasPushout f g] [PreservesLimitsOfShape
 WalkingCospan F] [ReflectsLimitsOfShape WalkingCospan F] [PreservesColimitsOfSh
ape WalkingSpan F] [ReflectsColimitsOfShape WalkingSpan F] : Adhesive C
参数：F : C ⥤ D；f : X ⟶ S；g : Y ⟶ S；f : S ⟶ X；g : S ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPushout.isVanKampen_iff`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i 
: Y ⟶ Z}   (H : CategoryTheory…
· 使用定理 `CategoryTheory.IsVanKampenColimit.of_mapCocone`：∀ {J : Type v'} [inst : 
CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {D : Type u_2} [inst_…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.IsVanKampenColimit.precompose_isIso_iff`：∀ {J : Type v'} 
[inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheor
y.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.IsVanKampenColimit.of_iso`：∀ {J : Type v'} [inst : Catego
ryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPushout.map`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   
(F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Adhesive.van_kampen`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Adhesive C] {W X Y Z : C} {f : W ⟶ X
}   {g : W ⟶ Y} {h : X ⟶…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
theorem adhesive_of_preserves_and_reflects (F : C ⥤ D) [Adhesive D]
    [H₁ : ∀ {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [Mono f], HasPullback f g]
    [H₂ : ∀ {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y) [Mono f], HasPushout f g]
    [PreservesLimitsOfShape WalkingCospan F]
    [ReflectsLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape WalkingSpan F]
    [ReflectsColimitsOfShape WalkingSpan F] :
    Adhesive C := by
  apply Adhesive.mk (hasPullback_of_mono_left := H₁) (hasPushout_of_mono_left := H₂)
  intro W X Y Z f g h i hf H
  rw [IsPushout.isVanKampen_iff]
  refine IsVanKampenColimit.of_mapCocone F ?_
  refine (IsVanKampenColimit.precompose_isIso_iff (diagramIsoSpan _).inv).mp ?_
  refine IsVanKampenColimit.of_iso ?_ (PushoutCocone.isoMk _).symm
  refine (IsPushout.isVanKampen_iff (H.map F)).mp ?_
  apply Adhesive.van_kampen
/-
**CategoryTheory.adhesive_of_preserves_and_reflects_isomorphism** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory`。
形式化陈述：adhesive_of_preserves_and_reflects_isomorphism (F : C ⥤ D) [Adhesive D] [H
asPullbacks C] [HasPushouts C] [PreservesLimitsOfShape WalkingCospan F] [Preserv
esColimitsOfShape WalkingSpan F] [F.ReflectsIsomorphisms] : Adhesive C
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsIsomorphisms`：ref
lectsLimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms] 
[HasLimitsOfShape J C] [PreservesLimitsOfShape J G] : Ref…
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsIsomorphisms`：r
eflectsColimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphis
ms] [HasColimitsOfShape J C] [PreservesColimitsOfShape J G]…
· 使用定理 `CategoryTheory.adhesive_of_preserves_and_reflects`：adhesive_of_preserves
_and_reflects (F : C ⥤ D) [Adhesive D] [H₁ : forall {X Y S : C} (f : X ⟶ S) (g :
 Y ⟶ S) [Mono f], HasPullback f g] [H₂ …
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem adhesive_of_preserves_and_reflects_isomorphism (F : C ⥤ D)
    [Adhesive D] [HasPullbacks C] [HasPushouts C]
    [PreservesLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape WalkingSpan F]
    [F.ReflectsIsomorphisms] :
    Adhesive C := by
  have : ReflectsLimitsOfShape WalkingCospan F :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : ReflectsColimitsOfShape WalkingSpan F :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact adhesive_of_preserves_and_reflects F
/-
**CategoryTheory.adhesive_of_reflective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：adhesive_of_reflective [HasPullbacks D] [Adhesive C] [HasPullbacks C] [Has
Pushouts C] [H₂ : forall {X Y S : D} (f : S ⟶ X) (g : S ⟶ Y) [Mono f], HasPushou
t f g] {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [Gr.Full] [Gr.Faithful] [Preser
vesLimitsOfShape WalkingCospan Gl] : Adhesive D
参数：f : S ⟶ X；g : S ⟶ Y；adj : Gl ⊣ Gr。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`：leftAdjoint_pre
servesColimits : PreservesColimitsOfSize.{v, u} F where preservesColimitsOfShape
· 使用引理 `CategoryTheory.Adjunction.rightAdjoint_preservesLimits`：rightAdjoint_pre
servesLimits : PreservesLimitsOfSize.{v, u} G where preservesLimitsOfShape
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Adhesive.hasPushout_of_mono_left`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Adhesive C] {X Y S : C}
 (f : S ⟶ X)   (g : S ⟶ Y) [CategoryT…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
· 使用定理 `CategoryTheory.Adhesive.van_kampen`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Adhesive C] {W X Y Z : C} {f : W ⟶ X
}   {g : W ⟶ Y} {h : X ⟶…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPushout.isVanKampen_iff`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i 
: Y ⟶ Z}   (H : CategoryTheory…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.IsVanKampenColimit.precompose_isIso_iff`：∀ {J : Type v'} 
[inst : CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheor
y.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.IsVanKampenColimit.of_iso`：∀ {J : Type v'} [inst : Catego
ryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.IsVanKampenColimit.map_reflective`：∀ {J : Type v'} [inst 
: CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Cate
gory.{v, u} C]   {D : Type u_2} [inst_…
· 使用定理 `CategoryTheory.IsVanKampenColimit.precompose_isIso`：∀ {J : Type v'} [ins
t : CategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Ca
tegory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
theorem adhesive_of_reflective [HasPullbacks D] [Adhesive C] [HasPullbacks C] [HasPushouts C]
    [H₂ : ∀ {X Y S : D} (f : S ⟶ X) (g : S ⟶ Y) [Mono f], HasPushout f g]
    {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [Gr.Full] [Gr.Faithful]
    [PreservesLimitsOfShape WalkingCospan Gl] :
    Adhesive D := by
  have := adj.leftAdjoint_preservesColimits
  have := adj.rightAdjoint_preservesLimits
  apply Adhesive.mk (hasPushout_of_mono_left := H₂)
  intro W X Y Z f g h i _ H
  have := Adhesive.van_kampen (IsPushout.of_hasPushout (Gr.map f) (Gr.map g))
  rw [IsPushout.isVanKampen_iff] at this ⊢
  refine (IsVanKampenColimit.precompose_isIso_iff
    (Functor.isoWhiskerLeft _ (asIso adj.counit) ≪≫ Functor.rightUnitor _).hom).mp ?_
  refine ((this.precompose_isIso (spanCompIso _ _ _).hom).map_reflective adj).of_iso
    (IsColimit.uniqueUpToIso ?_ ?_)
  · exact isColimitOfPreserves Gl ((IsColimit.precomposeHomEquiv _ _).symm <| pushoutIsPushout _ _)
  · exact (IsColimit.precomposeHomEquiv _ _).symm H.isColimit

end functor

end CategoryTheory

