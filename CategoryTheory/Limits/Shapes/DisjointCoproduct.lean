/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial

/-!
# Disjoint coproducts

Defines disjoint coproducts: coproducts where the intersection is initial and the coprojections
are monic.
Shows that a category with disjoint coproducts is `InitialMonoClass`.

## TODO

* Adapt this to the infinitary (small) version: This is one of the conditions in Giraud's theorem
  characterising sheaf topoi.
* Construct examples (and counterexamples?), e.g. Type, Vec.
* Define extensive categories, and show every extensive category has disjoint coproducts.
* Define coherent categories and use this to define positive coherent categories.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

open Category

variable {C : Type u} [Category.{v} C]

/--
We say the coproduct of the family `Xᵢ` is disjoint, if whenever we have a pullback diagram of the
form
```
Z  ⟶ X₁
↓    ↓
X₂ ⟶ ∐ X
```
`Z` is initial.
-/
/-
**CategoryTheory.Limits.CoproductDisjoint** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：{C : Type u} → [CategoryTheory.Category.{v, u} C] → {ι : Type u_1} → (ι → 
C) → Prop
参数：ι → C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say the coproduct of the family `Xᵢ` is disjoint, if whenever we have a pullb
ack diagram of the
form
```
Z  ⟶ X₁
↓    ↓
X₂ ⟶ ∐ X
```
`Z` is initial.
-/
class CoproductDisjoint {ι : Type*} (X : ι → C) : Prop where
  nonempty_isInitial_of_ne {c : Cofan X} (hc : IsColimit c) {i j : ι} (_ : i ≠ j)
    (s : PullbackCone (c.inj i) (c.inj j)) :
    IsLimit s → Nonempty (IsInitial s.pt)
  mono_inj {c : Cofan X} (hc : IsColimit c) (i : ι) : Mono (c.inj i)

section

variable {ι : Type*} {X : ι → C}

/-
**CategoryTheory.Limits.CoproductDisjoint.of_cofan** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.CoproductDisjoint`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_1} {X
 : ι → C} {c : CategoryTheory.Limits.Cofan X}   (hc : CategoryTheory.Limits.IsCo
limit c) [∀ (i : ι), CategoryTheory.Mono (c.inj i)]   (s : {i j : ι} → i ≠ j → C
ategoryTheory.Limits.PullbackCone (c.inj i) (c.inj j))   (hs : {i j : ι} → (hij 
: i ≠ j) → CategoryTheory.Limits.IsLimit (s hij))   (H : {i j : ι} → (hij : i ≠ 
j) → CategoryTheory.Limits.IsInitial (s hij).pt),   CategoryTheory.Limits.Coprod
uctDisjoint X
参数：hc : CategoryTheory.Limits.IsColimit c；i : ι；c.inj i；s : {i j : ι} → i ≠ j → 
CategoryTheory.Limits.PullbackCone (c.inj i) (c.inj j)；hs : {i j : ι} → (hij : i
 ≠ j) → CategoryTheory.Limits.IsLimit (s hij)；H : {i j : ι} → (hij : i ≠ j) → Ca
tegoryTheory.Limits.IsInitial (s hij).pt。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.CoconeMorphism.w`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃,
 u₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition_assoc`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   (t : 
CategoryTheory.Limits.PullbackCone f g) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.hom_ext`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t : 
CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsInitial.to_comp`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X : C} (t : CategoryTheory.Limits.IsInitial X) {Y 
Z : C}   (f : Y ⟶ Z), Categor…
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_fst`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_snd`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `CategoryTheory.Limits.IsColimit.uniqueUpToIso_inv`：∀ {J : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Ca
tegory.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsColimit.descCoconeMorphism_hom`：∀ {J : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheo
ry.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.inj_desc`：∀ {β : Type w} {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {X : β → C} {c : CategoryTheory.Li
mits.Cofan X}   (d : CategoryTheory.…
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Limits.instIsIsoHomHomCocone`：∀ {J : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category
.{v₃, u₃} C]   {F : CategoryTheor…
-/
lemma CoproductDisjoint.of_cofan {c : Cofan X} (hc : IsColimit c)
    [∀ i, Mono (c.inj i)]
    (s : ∀ {i j : ι} (_ : i ≠ j), PullbackCone (c.inj i) (c.inj j))
    (hs : ∀ {i j : ι} (hij : i ≠ j), IsLimit (s hij))
    (H : ∀ {i j : ι} (hij : i ≠ j), IsInitial (s hij).pt) :
    CoproductDisjoint X where
  nonempty_isInitial_of_ne {d} hd {i j} hij t ht := by
    let e := hd.uniqueUpToIso hc
    have heq (i) : d.inj i ≫ e.hom.hom = c.inj i := e.hom.w ⟨i⟩
    let u : t.pt ⟶ (s hij).pt := by
      refine PullbackCone.IsLimit.lift (hs hij) t.fst t.snd ?_
      simp [← heq, t.condition_assoc]
    refine ⟨(H hij).ofIso ⟨(H hij).to t.pt, u, (H hij).hom_ext _ _, ?_⟩⟩
    refine PullbackCone.IsLimit.hom_ext ht ?_ ?_
    · simp [show (H hij).to (X i) = (s hij).fst from (H hij).hom_ext _ _, u]
    · simp [show (H hij).to (X j) = (s hij).snd from (H hij).hom_ext _ _, u]
  mono_inj {d} hd i := by
    rw [show d.inj i = c.inj i ≫ (hd.uniqueUpToIso hc).inv.hom by simp]
    infer_instance
/-
**CategoryTheory.Limits.CoproductDisjoint.of_hasCoproduct** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.CoproductDisjoint`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_1} {X
 : ι → C}   [inst_1 : CategoryTheory.Limits.HasCoproduct X] [∀ (i : ι), Category
Theory.Mono (CategoryTheory.Limits.Sigma.ι X i)]   (s :     {i j : ι} →       i 
≠ j →         CategoryTheory.Limits.PullbackCone (CategoryTheory.Limits.Sigma.ι 
X i) (CategoryTheory.Limits.Sigma.ι X j))   (hs : {i j : ι} → (hij : i ≠ j) → Ca
tegoryTheory.Limits.IsLimit (s hij))   (H : {i j : ι} → (hij : i ≠ j) → Category
Theory.Limits.IsInitial (s hij).pt),   CategoryTheory.Limits.CoproductDisjoint X
参数：i : ι；CategoryTheory.Limits.Sigma.ι X i；s :     {i j : ι} →       i ≠ j →    
     CategoryTheory.Limits.PullbackCone (CategoryTheory.Limits.Sigma.ι X i) (Cat
egoryTheory.Limits.Sigma.ι X j)；hs : {i j : ι} → (hij : i ≠ j) → CategoryTheory.
Limits.IsLimit (s hij)；H : {i j : ι} → (hij : i ≠ j) → CategoryTheory.Limits.IsI
nitial (s hij).pt。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.CoproductDisjoint.of_cofan`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {ι : Type u_1} {X : ι → C} {c : CategoryTheor
y.Limits.Cofan X}   (hc : CategoryTheo…
-/
lemma CoproductDisjoint.of_hasCoproduct [HasCoproduct X] [∀ i, Mono (Sigma.ι X i)]
    (s : ∀ {i j : ι} (_ : i ≠ j), PullbackCone (Sigma.ι X i) (Sigma.ι X j))
    (hs : ∀ {i j : ι} (hij : i ≠ j), IsLimit (s hij))
    (H : ∀ {i j : ι} (hij : i ≠ j), IsInitial (s hij).pt) :
    CoproductDisjoint X :=
  have (i : ι) : Mono ((Cofan.mk (∐ X) (Sigma.ι X)).inj i) := inferInstanceAs <| Mono (Sigma.ι X i)
  .of_cofan (coproductIsCoproduct X) s hs H

variable [CoproductDisjoint X]
/-
**CategoryTheory.Limits._root_.CategoryTheory.Mono.of_coproductDisjoint** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.Mono.of_coproductDisjoint {c : Cofan X} (hc : IsColimit c) (i : ι) :
    Mono (c.inj i) :=
  CoproductDisjoint.mono_inj hc i
/-
**CategoryTheory.Limits._root_.CategoryTheory.Mono.** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.CategoryTheory.Mono.ι_of_coproductDisjoint [HasCoproduct X] (i : ι) :
    Mono (Sigma.ι X i) :=
  CoproductDisjoint.mono_inj (colimit.isColimit _) i

namespace IsInitial
variable {i j : ι} (hij : i ≠ j)

/-- If `i ≠ j` and `Xᵢ ← Y → Xⱼ` is a pullback diagram over `Z`, where `Z` is the
coproduct of the `Xᵢ`, then `Y` is initial. -/
/-
**CategoryTheory.Limits.IsInitial.ofCoproductDisjointOfIsColimitOfIsLimit** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.IsInitial`。
形式化陈述：ofCoproductDisjointOfIsColimitOfIsLimit {c : Cofan X} (hc : IsColimit c) {
s : PullbackCone (c.inj i) (c.inj j)} (hs : IsLimit s) : IsInitial s.pt
参数：hc : IsColimit c；c.inj i；c.inj j；hs : IsLimit s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.CoproductDisjoint.nonempty_isInitial_of_ne`：∀ {C :
 Type u} {inst : CategoryTheory.Category.{v, u} C} {ι : Type u_1} {X : ι → C}   
[self : CategoryTheory.Limits.CoproductDisjoint X] {c …

--- 原说明 ---
If `i ≠ j` and `Xᵢ ← Y → Xⱼ` is a pullback diagram over `Z`, where `Z` is the
coproduct of the `Xᵢ`, then `Y` is initial.
-/
noncomputable def ofCoproductDisjointOfIsColimitOfIsLimit {c : Cofan X} (hc : IsColimit c)
    {s : PullbackCone (c.inj i) (c.inj j)} (hs : IsLimit s) :
    IsInitial s.pt :=
  (CoproductDisjoint.nonempty_isInitial_of_ne hc hij _ hs).some

/-- If `i ≠ j`, the pullback `Xᵢ ×[∐ X] Xⱼ` is initial. -/
/-
**CategoryTheory.Limits.IsInitial.ofCoproductDisjoint** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.IsInitial`。
形式化陈述：ofCoproductDisjoint [HasCoproduct X] [HasPullback (Sigma.ι X i) (Sigma.ι X
 j)] : IsInitial (pullback (Sigma.ι X i) (Sigma.ι X j))
参数：Sigma.ι X i；Sigma.ι X j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i ≠ j`, the pullback `Xᵢ ×[∐ X] Xⱼ` is initial.
-/
noncomputable def ofCoproductDisjoint [HasCoproduct X] [HasPullback (Sigma.ι X i) (Sigma.ι X j)] :
    IsInitial (pullback (Sigma.ι X i) (Sigma.ι X j)) :=
  ofCoproductDisjointOfIsColimitOfIsLimit hij (colimit.isColimit _)
    (pullback.isLimit (Sigma.ι X i) (Sigma.ι X j))

/-- If `i ≠ j`, the pullback `Xᵢ ×[Z] Xⱼ` is initial, if `Z` is the coproduct of the `Xᵢ`. -/
/-
**CategoryTheory.Limits.IsInitial.ofCoproductDisjointOfIsColimit** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Limits.IsInitial`。
形式化陈述：ofCoproductDisjointOfIsColimit {Z : C} {f : forall i, X i ⟶ Z} [HasPullbac
k (f i) (f j)] (hc : IsColimit (Cofan.mk _ f)) : IsInitial (pullback (f i) (f j)
)
参数：f i；f j；hc : IsColimit (Cofan.mk _ f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i ≠ j`, the pullback `Xᵢ ×[Z] Xⱼ` is initial, if `Z` is the coproduct of the
 `Xᵢ`.
-/
noncomputable def ofCoproductDisjointOfIsColimit
    {Z : C} {f : ∀ i, X i ⟶ Z} [HasPullback (f i) (f j)] (hc : IsColimit (Cofan.mk _ f)) :
    IsInitial (pullback (f i) (f j)) :=
  ofCoproductDisjointOfIsColimitOfIsLimit hij hc (pullback.isLimit (f i) (f j))

/-- If `i ≠ j` and `Xᵢ ← Y → Xⱼ` is a pullback diagram over `∐ X`, `Y` is initial. -/
/-
**CategoryTheory.Limits.IsInitial.ofCoproductDisjointOfIsLimit** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Limits.IsInitial`。
形式化陈述：ofCoproductDisjointOfIsLimit [HasCoproduct X] {s : PullbackCone (Sigma.ι X
 i) (Sigma.ι X j)} (hs : IsLimit s) : IsInitial s.pt
参数：Sigma.ι X i；Sigma.ι X j；hs : IsLimit s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i ≠ j` and `Xᵢ ← Y → Xⱼ` is a pullback diagram over `∐ X`, `Y` is initial.
-/
noncomputable def ofCoproductDisjointOfIsLimit
    [HasCoproduct X] {s : PullbackCone (Sigma.ι X i) (Sigma.ι X j)} (hs : IsLimit s) :
    IsInitial s.pt :=
  ofCoproductDisjointOfIsColimitOfIsLimit hij (colimit.isColimit _) hs

/-- If `C` has strict initial objects and there is a commutative square `Xᵢ ← Z → Xⱼ`
over `∐ X`, then `Z` is initial. -/
/-
**CategoryTheory.Limits.IsInitial.ofCoproductDisjointOfCommSq** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Limits.IsInitial`。
形式化陈述：ofCoproductDisjointOfCommSq [HasStrictInitialObjects C] {c : Cofan X} (hc 
: IsColimit c) {Z : C} (fst : Z ⟶ X i) (snd : Z ⟶ X j) (h : fst ≫ c.inj i = snd 
≫ c.inj j) [HasPullback (c.inj i) (c.inj j)] : Limits.IsInitial Z
参数：hc : IsColimit c；fst : Z ⟶ X i；snd : Z ⟶ X j；h : fst ≫ c.inj i = snd ≫ c.inj 
j；c.inj i；c.inj j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` has strict initial objects and there is a commutative square `Xᵢ ← Z → Xⱼ
`
over `∐ X`, then `Z` is initial.
-/
noncomputable def ofCoproductDisjointOfCommSq [HasStrictInitialObjects C]
    {c : Cofan X} (hc : IsColimit c) {Z : C} (fst : Z ⟶ X i) (snd : Z ⟶ X j)
    (h : fst ≫ c.inj i = snd ≫ c.inj j) [HasPullback (c.inj i) (c.inj j)] :
    Limits.IsInitial Z :=
  .ofStrict (pullback.lift fst snd h) <|
    .ofCoproductDisjointOfIsColimitOfIsLimit hij hc (limit.isLimit _)

end IsInitial

/-
**CategoryTheory.Limits.CoproductDisjoint.isPullback_of_isInitial** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Limits.CoproductDisjoint`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_1} {X
 : ι → C}   [CategoryTheory.Limits.CoproductDisjoint X] {c : CategoryTheory.Limi
ts.Cofan X}   (hc : CategoryTheory.Limits.IsColimit c) {Y : C} (hY : CategoryThe
ory.Limits.IsInitial Y) {i j : ι}   [CategoryTheory.Limits.HasPullback (c.inj i)
 (c.inj j)],   i ≠ j → CategoryTheory.IsPullback (hY.to (X i)) (hY.to (X j)) (c.
inj i) (c.inj j)
参数：hc : CategoryTheory.Limits.IsColimit c；hY : CategoryTheory.Limits.IsInitial Y
；c.inj i；c.inj j；hY.to (X i)；hY.to (X j)；c.inj i；c.inj j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_iso_pullback`：of_iso_pullback (h : CommSq f
st snd f g) [HasPullback f g] (i : P ≅ pullback f g) (w₁ : i.hom ≫ pullback.fst 
_ _ = fst) (w₂ : i.hom ≫ pullba…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsInitial.to_comp`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X : C} (t : CategoryTheory.Limits.IsInitial X) {Y 
Z : C}   (f : Y ⟶ Z), Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.IsInitial.uniqueUpToIso_hom`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {I I' : C} (hI : CategoryTheory.Limits.Is
Initial I)   (hI' : CategoryTheory.Limi…
-/
lemma CoproductDisjoint.isPullback_of_isInitial {c : Cofan X} (hc : IsColimit c)
    {Y : C} (hY : IsInitial Y) {i j : ι} [HasPullback (c.inj i) (c.inj j)] (hij : i ≠ j) :
    IsPullback (hY.to _) (hY.to _) (c.inj i) (c.inj j) := by
  refine .of_iso_pullback (by simp) ?_ ?_ ?_
  · refine hY.uniqueUpToIso ?_
    exact IsInitial.ofCoproductDisjointOfIsColimit hij hc
  · simp
  · simp

end

/-- The binary coproduct of `X` and `Y` is disjoint if the coproduct of the family `{X, Y}` is
disjoint. -/
/-
**CategoryTheory.Limits.BinaryCoproductDisjoint** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：BinaryCoproductDisjoint (X Y : C)
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary coproduct of `X` and `Y` is disjoint if the coproduct of the family `
{X, Y}` is
disjoint.
-/
abbrev BinaryCoproductDisjoint (X Y : C) :=
  CoproductDisjoint (fun j : WalkingPair ↦ (j.casesOn X Y : C))

section

variable {X Y : C}

/-
**CategoryTheory.Limits.BinaryCoproductDisjoint.of_binaryCofan** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits.BinaryCoproductDisjoint`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {c : Ca
tegoryTheory.Limits.BinaryCofan X Y}   (hc : CategoryTheory.Limits.IsColimit c) 
[CategoryTheory.Mono c.inl] [CategoryTheory.Mono c.inr]   {s : CategoryTheory.Li
mits.PullbackCone c.inl c.inr} (hs : CategoryTheory.Limits.IsLimit s)   (H : Cat
egoryTheory.Limits.IsInitial s.pt), CategoryTheory.Limits.BinaryCoproductDisjoin
t X Y
参数：hc : CategoryTheory.Limits.IsColimit c；hs : CategoryTheory.Limits.IsLimit s；H
 : CategoryTheory.Limits.IsInitial s.pt。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.CoproductDisjoint.of_cofan`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {ι : Type u_1} {X : ι → C} {c : CategoryTheor
y.Limits.Cofan X}   (hc : CategoryTheo…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma BinaryCoproductDisjoint.of_binaryCofan {c : BinaryCofan X Y} (hc : IsColimit c)
    [Mono c.inl] [Mono c.inr] {s : PullbackCone c.inl c.inr}
    (hs : IsLimit s) (H : IsInitial s.pt) :
    BinaryCoproductDisjoint X Y := by
  have (i : WalkingPair) : Mono (Cofan.inj c i) := by
    cases i
    · exact inferInstanceAs <| Mono c.inl
    · exact inferInstanceAs <| Mono c.inr
  refine .of_cofan hc (fun {i j} hij ↦ ?_) (fun {i j} hij ↦ ?_) (fun {i j} hij ↦ ?_)
  · match i, j with
    | .left, .right => exact s
    | .right, .left => exact s.flip
  · dsimp
    split
    · exact hs
    · exact PullbackCone.flipIsLimit hs
  · dsimp; split <;> exact H

variable [BinaryCoproductDisjoint X Y]
/-
**CategoryTheory.Limits._root_.CategoryTheory.Mono.cofanInl_of_binaryCoproductDi
sjoint** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.Mono.cofanInl_of_binaryCoproductDisjoint {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inl :=
  .of_coproductDisjoint hc .left
/-
**CategoryTheory.Limits._root_.CategoryTheory.Mono.cofanInr_of_binaryCoproductDi
sjoint** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.Mono.cofanInr_of_binaryCoproductDisjoint {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inr :=
  .of_coproductDisjoint hc .right
/-
**CategoryTheory.Limits._root_.CategoryTheory.Mono.of_binaryCoproductDisjoint_le
ft** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.Mono.of_binaryCoproductDisjoint_left {Z : C}
    {f : X ⟶ Z} (g : Y ⟶ Z) (hc : IsColimit <| BinaryCofan.mk f g) : Mono f :=
  .of_coproductDisjoint hc .left
/-
**CategoryTheory.Limits._root_.CategoryTheory.Mono.of_binaryCoproductDisjoint_ri
ght** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.Mono.of_binaryCoproductDisjoint_right {Z : C}
    (f : X ⟶ Z) {g : Y ⟶ Z} (hc : IsColimit <| BinaryCofan.mk f g) : Mono g :=
  .of_coproductDisjoint hc .right
/-
**CategoryTheory.Limits._root_.CategoryTheory.Mono.inl_of_binaryCoproductDisjoin
t** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.CategoryTheory.Mono.inl_of_binaryCoproductDisjoint [HasBinaryCoproduct X Y] :
    Mono (coprod.inl : X ⟶ X ⨿ Y) :=
  @Mono.ι_of_coproductDisjoint _ _ _ _ _ ‹_› WalkingPair.left
/-
**CategoryTheory.Limits._root_.CategoryTheory.Mono.inr_of_binaryCoproductDisjoin
t** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.CategoryTheory.Mono.inr_of_binaryCoproductDisjoint [HasBinaryCoproduct X Y] :
    Mono (coprod.inr : Y ⟶ X ⨿ Y) :=
  @Mono.ι_of_coproductDisjoint _ _ _ _ _ ‹_› WalkingPair.right

namespace IsInitial

/-- If `X ← Z → Y` is a pullback diagram over `W`, where `W` is the
coproduct of `X` and `Y`, then `Z` is initial. -/
/-
**CategoryTheory.Limits.IsInitial.ofBinaryCoproductDisjointOfIsColimitOfIsLimit*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.IsInitial`。
形式化陈述：ofBinaryCoproductDisjointOfIsColimitOfIsLimit {c : BinaryCofan X Y} (hc : 
IsColimit c) {s : PullbackCone c.inl c.inr} (hs : IsLimit s) : IsInitial s.pt
参数：hc : IsColimit c；hs : IsLimit s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X ← Z → Y` is a pullback diagram over `W`, where `W` is the
coproduct of `X` and `Y`, then `Z` is initial.
-/
noncomputable def ofBinaryCoproductDisjointOfIsColimitOfIsLimit
    {c : BinaryCofan X Y} (hc : IsColimit c) {s : PullbackCone c.inl c.inr} (hs : IsLimit s) :
    IsInitial s.pt :=
  (CoproductDisjoint.nonempty_isInitial_of_ne hc (by simp) _ hs).some

/-- `X ×[X ⨿ Y] Y` is initial. -/
/-
**CategoryTheory.Limits.IsInitial.ofBinaryCoproductDisjoint** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits.IsInitial`。
形式化陈述：ofBinaryCoproductDisjoint [HasBinaryCoproduct X Y] [HasPullback (coprod.in
l : X ⟶ X ⨿ Y) coprod.inr] : IsInitial (pullback (coprod.inl : X ⟶ X ⨿ Y) coprod
.inr)
参数：coprod.inl : X ⟶ X ⨿ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X ×[X ⨿ Y] Y` is initial.
-/
noncomputable def ofBinaryCoproductDisjoint [HasBinaryCoproduct X Y]
    [HasPullback (coprod.inl : X ⟶ X ⨿ Y) coprod.inr] :
    IsInitial (pullback (coprod.inl : X ⟶ X ⨿ Y) coprod.inr) :=
  ofBinaryCoproductDisjointOfIsColimitOfIsLimit (colimit.isColimit _) (pullback.isLimit _ _)

/-- The pullback `X ×[W] Y` is initial, if `W` is the coproduct of `X` and `Y`. -/
/-
**CategoryTheory.Limits.IsInitial.ofBinaryCoproductDisjointOfIsColimit** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Limits.IsInitial`。
形式化陈述：ofBinaryCoproductDisjointOfIsColimit {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasP
ullback f g] (hc : IsColimit (BinaryCofan.mk f g)) : IsInitial (pullback f g)
参数：hc : IsColimit (BinaryCofan.mk f g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback `X ×[W] Y` is initial, if `W` is the coproduct of `X` and `Y`.
-/
noncomputable def ofBinaryCoproductDisjointOfIsColimit {Z : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (hc : IsColimit (BinaryCofan.mk f g)) :
    IsInitial (pullback f g) :=
  ofBinaryCoproductDisjointOfIsColimitOfIsLimit hc (pullback.isLimit f g)

/-- If `X ← Z → Y` is a pullback diagram over `X ⨿ Y`, `Z` is initial. -/
/-
**CategoryTheory.Limits.IsInitial.ofBinaryCoproductDisjointOfIsLimit** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Limits.IsInitial`。
形式化陈述：ofBinaryCoproductDisjointOfIsLimit [HasBinaryCoproduct X Y] (s : PullbackC
one (coprod.inl : X ⟶ X ⨿ Y) coprod.inr) (hs : IsLimit s) : IsInitial s.pt
参数：s : PullbackCone (coprod.inl : X ⟶ X ⨿ Y) coprod.inr；hs : IsLimit s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X ← Z → Y` is a pullback diagram over `X ⨿ Y`, `Z` is initial.
-/
noncomputable def ofBinaryCoproductDisjointOfIsLimit
    [HasBinaryCoproduct X Y] (s : PullbackCone (coprod.inl : X ⟶ X ⨿ Y) coprod.inr)
    (hs : IsLimit s) : IsInitial s.pt :=
  ofBinaryCoproductDisjointOfIsColimitOfIsLimit (colimit.isColimit _) hs

end IsInitial

end

/-- `C` has disjoint coproducts if every coproduct is disjoint. -/
/-
**CategoryTheory.Limits.CoproductsOfShapeDisjoint** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：(C : Type u_1) → [CategoryTheory.Category.{v_1, u_1} C] → Type u_2 → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C` has disjoint coproducts if every coproduct is disjoint.
-/
class CoproductsOfShapeDisjoint (C : Type*) [Category* C] (ι : Type*) : Prop where
  coproductDisjoint (X : ι → C) : CoproductDisjoint X

/-- `C` has disjoint binary coproducts if every binary coproduct is disjoint. -/
/-
**CategoryTheory.Limits.BinaryCoproductsDisjoint** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：BinaryCoproductsDisjoint (C : Type*) [Category* C] : Prop
参数：C : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C` has disjoint binary coproducts if every binary coproduct is disjoint.
-/
abbrev BinaryCoproductsDisjoint (C : Type*) [Category* C] : Prop :=
  CoproductsOfShapeDisjoint C WalkingPair

attribute [instance 999] CoproductsOfShapeDisjoint.coproductDisjoint
/-
**CategoryTheory.Limits.BinaryCoproductsDisjoint.mk** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.BinaryCoproductsDisjoint`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C],   (∀ (X Y : C), 
CategoryTheory.Limits.BinaryCoproductDisjoint X Y) → CategoryTheory.Limits.Binar
yCoproductsDisjoint C
参数：∀ (X Y : C), CategoryTheory.Limits.BinaryCoproductDisjoint X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma BinaryCoproductsDisjoint.mk (H : ∀ (X Y : C), BinaryCoproductDisjoint X Y) :
    BinaryCoproductsDisjoint C where
  coproductDisjoint X := by
    convert! H (X .left) (X .right) using 2
    casesm WalkingPair <;> simp

/-- If `C` has disjoint coproducts, any morphism out of initial is mono. Note it isn't true in
general that `C` has strict initial objects, for instance consider the category of types and
partial functions. -/
/-
**CategoryTheory.Limits.initialMonoClass_of_coproductsDisjoint** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：initialMonoClass_of_coproductsDisjoint [BinaryCoproductsDisjoint C] : Init
ialMonoClass C where isInitial_mono_from X hI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Mono.of_binaryCoproductDisjoint_left`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y : C} [CategoryTheory.Limits.BinaryCop
roductDisjoint X Y]   {Z : C} {f : X ⟶ Z}…
· 使用定理 `CategoryTheory.Limits.CoproductsOfShapeDisjoint.coproductDisjoint`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {ι : Type u_2}   [self
 : CategoryTheory.Limits.CoproductsOfShapeDisjoint C ι]…
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `C` has disjoint coproducts, any morphism out of initial is mono. Note it isn
't true in
general that `C` has strict initial objects, for instance consider the category 
of types and
partial functions.
-/
theorem initialMonoClass_of_coproductsDisjoint [BinaryCoproductsDisjoint C] :
    InitialMonoClass C where
  isInitial_mono_from X hI :=
    .of_binaryCoproductDisjoint_left (CategoryTheory.CategoryStruct.id X)
      { desc := fun s : BinaryCofan _ _ => s.inr
        fac := fun _s j =>
          Discrete.casesOn j fun j => WalkingPair.casesOn j (hI.hom_ext _ _) (id_comp _)
        uniq := fun (_s : BinaryCofan _ _) _m w =>
          (id_comp _).symm.trans (w ⟨WalkingPair.right⟩) }

end CategoryTheory.Limits

