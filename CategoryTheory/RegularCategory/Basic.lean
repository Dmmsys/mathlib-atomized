/-
Copyright (c) 2025 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
module

public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.Coherent.Basic

/-!
# Regular categories

A regular category is a category with finite limits such that each kernel pair has a coequalizer
and such that regular epimorphisms are stable under pullback.

These categories provide a good ground to develop the calculus of relations, as well as being the
semantics for regular logic.

## Main results

* We show that every regular category has strong epi-mono factorisations, following Theorem 1.11
  in [Gran2021].
* We show that every regular category satisfies Frobenius reciprocity. That is, that in their
  internal language, we have `∃ x, (P(x) ⊓ Q)` iff `(∃ x, P(x)) ⊓ Q`, for a proposition `Q` not
  depending on `x`.

## Future work
* Show that every topos is regular
* Show that regular logic has an interpretation in regular categories

## References
* [Marino Gran, An Introduction to Regular Categories][Gran2021]
* <https://ncatlab.org/nlab/show/regular+category>
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/--
A regular category is a category with finite limits, such that every kernel pair has a coequalizer,
and such that regular epimorphisms are stable under base change.
-/
/-
**CategoryTheory.Regular** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A regular category is a category with finite limits, such that every kernel pair
 has a coequalizer,
and such that regular epimorphisms are stable under base change.
-/
class Regular extends HasFiniteLimits C where
  hasCoequalizer_of_isKernelPair {X Y Z : C} {f : X ⟶ Y} {g₁ g₂ : Z ⟶ X} :
    IsKernelPair f g₁ g₂ → HasCoequalizer g₁ g₂
  regularEpiIsStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange (.regularEpi C)

variable {C} [Regular C]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y B : C} (f : X ⟶ B) (g : Y ⟶ B) [HasPullback f g] [IsRegularEpi f] :
    IsRegularEpi (pullback.snd f g) := by
  apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g)
  dsimp [MorphismProperty.regularEpi]
  infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y B : C} (f : X ⟶ B) (g : Y ⟶ B) [HasPullback f g] [IsRegularEpi g] :
    IsRegularEpi (pullback.fst f g) := by
  apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g).flip
  dsimp [MorphismProperty.regularEpi]
  infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preregular C where
  exists_fac f g := ⟨_, pullback.snd g f, inferInstance, pullback.fst g f, pullback.condition⟩

variable {X Y : C} (f : X ⟶ Y)

namespace Regular

section StrongEpiMonoFactorisation

local instance : HasCoequalizer (pullback.fst f f) (pullback.snd f f) :=
  Regular.hasCoequalizer_of_isKernelPair <| IsKernelPair.of_hasPullback f

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Regular.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Regular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (coequalizer.desc f pullback.condition) := by
  -- It suffices to show that the two projections from the kernel pair are equal:
  apply (IsKernelPair.of_hasPullback _).mono_of_eq_fst_snd
  /- We fill in the kernel pair square of `f` as follows:
  ```
                  g₁                   fst
  pullback f f------->pullback e k₁----------> X
        |                 |                    |
      g₂|                 |snd                 |e
        v        fst      v            k₁      v
  pullback k₂ e------>pullback m m---------->coeq
        |                                      |
     snd|                                      |m
        v              e ≫ m = f               v
        X------------------------------------->Y
  ```
  Where `m`, `e`, `k₁`, `k₂`, `g₁`, `g₂` are defined below, `fst` and `snd` denote the projections
  in the pullbacks indicated as the source of those morphisms, and `coeq` is the coequalizer of the
  two projections in from the kernel pair of `f`.
  -/
  let m := (coequalizer.desc f pullback.condition)
  let e := coequalizer.π (pullback.fst f f) (pullback.snd f f)
  let k₁ := pullback.fst m m
  let k₂ := pullback.snd m m
  let d : pullback f f ⟶ (pullback m m) :=
    pullback.lift (pullback.fst f f ≫ e) (pullback.snd f f ≫ e) (by simp [m, e, pullback.condition])
  let g₁ : pullback f f ⟶ (pullback e k₁) := pullback.lift (pullback.fst f f) d (by simp [d, k₁])
  let g₂ : pullback f f ⟶ (pullback k₂ e) := pullback.lift d (pullback.snd f f) (by simp [d, k₂])
  /-
  Since the big square, the bottom square, and the top right square above are pullback squares,
  the top left square is also a pullback square.
  -/
  have h : IsPullback g₁ g₂ (pullback.snd e k₁) (pullback.fst k₂ e) := by
    refine .of_right ?_ (by simp [g₁, g₂]) (.of_hasPullback e k₁)
    refine .of_bot ?_ ?_ (.paste_horiz (.of_hasPullback k₂ e) (.of_hasPullback m m))
    · simpa [g₁, g₂, e, m, pullback.lift_fst, pullback.lift_snd] using .of_hasPullback f f
    · simp [g₁, g₂, k₁, d]
  /-
  Since `g₁` is the base change of a regular epi (the map `fst` in the middle row of the diagram
  above, which itself is a regular epi because it is a base change of the regular epi `e`),
  it is a regular epi.
  -/
  have : IsRegularEpi g₁ := by
    apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback h.flip
    dsimp [MorphismProperty.regularEpi]
    infer_instance
  -- We precompose with the epimorphism `g₁ ≫ pullback.snd e k₁`, and finish
  rw [← cancel_epi (g₁ ≫ pullback.snd e k₁)]
  convert! coequalizer.condition (pullback.fst f f) (pullback.snd f f) using 1
  all_goals cat_disch

set_option backward.isDefEq.respectTransparency false in
/--
In a regular category, every morphism `f : X ⟶ Y` factors as `e ≫ m`, where `e` is the projection
map to the coequalizer of the kernel pair of `f`, and `m` is the canonical map from that
coequalizer to `Y`. In particular, `f` factors as a strong epimorphism followed by a monomorphism.
-/
/-
**CategoryTheory.Regular.strongEpiMonoFactorisation** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Regular`。
形式化陈述：strongEpiMonoFactorisation : StrongEpiMonoFactorisation f where I
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Regular.instHasCoequalizerFstSnd`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Regular C] {X Y : C} 
(f : X ⟶ Y),   CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Regular.instMonoDesc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Regular C] {X Y : C} (f : X ⟶ Y),
   CategoryTheory.Mono (C…

--- 原说明 ---
In a regular category, every morphism `f : X ⟶ Y` factors as `e ≫ m`, where `e` 
is the projection
map to the coequalizer of the kernel pair of `f`, and `m` is the canonical map f
rom that
coequalizer to `Y`. In particular, `f` factors as a strong epimorphism followed 
by a monomorphism.
-/
noncomputable def strongEpiMonoFactorisation : StrongEpiMonoFactorisation f where
  I := coequalizer (pullback.fst f f) (pullback.snd f f)
  m := coequalizer.desc f pullback.condition
  e := coequalizer.π (pullback.fst f f) (pullback.snd f f)
/-
**CategoryTheory.Regular.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Regular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsRegularEpi (strongEpiMonoFactorisation f).e := by
  dsimp [strongEpiMonoFactorisation]
  infer_instance

/--
In a regular category, every morphism `f` factors as `e ≫ m`, with `e` a strong epimorphism
and `m` a monomorphism.
-/
/-
**CategoryTheory.Regular.hasStrongEpiMonoFactorisations** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.Regular`。
形式化陈述：hasStrongEpiMonoFactorisations : HasStrongEpiMonoFactorisations C where ha
s_fac f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a regular category, every morphism `f` factors as `e ≫ m`, with `e` a strong 
epimorphism
and `m` a monomorphism.
-/
instance hasStrongEpiMonoFactorisations : HasStrongEpiMonoFactorisations C where
  has_fac f := ⟨strongEpiMonoFactorisation f⟩

set_option backward.isDefEq.respectTransparency false in
/-- In a regular category, every extremal epimorphism is a regular epimorphism. -/
/-
**CategoryTheory.Regular.regularEpiOfExtremalEpi** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Regular`。
形式化陈述：regularEpiOfExtremalEpi [h : ExtremalEpi f] : RegularEpi f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Regular.instIsRegularEpiEStrongEpiMonoFactorisation`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Re
gular C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.IsRegul…

--- 原说明 ---
In a regular category, every extremal epimorphism is a regular epimorphism.
-/
noncomputable def regularEpiOfExtremalEpi [h : ExtremalEpi f] : RegularEpi f :=
  have := h.isIso (strongEpiMonoFactorisation f).e (strongEpiMonoFactorisation f).m (by simp)
  RegularEpi.ofArrowIso (Arrow.isoMk (f := .mk (strongEpiMonoFactorisation f).e) (Iso.refl _)
    (asIso (strongEpiMonoFactorisation f).m)) (IsRegularEpi.getStruct _)
/-
**CategoryTheory.Regular.isRegularEpi_of_extremalEpi** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Regular`。
形式化陈述：isRegularEpi_of_extremalEpi (f : X ⟶ Y) [ExtremalEpi f] : IsRegularEpi f
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isRegularEpi_of_extremalEpi (f : X ⟶ Y) [ExtremalEpi f] : IsRegularEpi f :=
  ⟨⟨regularEpiOfExtremalEpi f⟩⟩

end StrongEpiMonoFactorisation

section Frobenius

open Subobject

variable {A B : C} (f : A ⟶ B) (A' : Subobject A) (B' : Subobject B)

set_option backward.isDefEq.respectTransparency false in
/--
Given a morphism `f : A ⟶ B` and subobjects `A' ⟶ A` and `B' ⟶ B`, we have a canonical morphism
`(A' ⊓ (Subobject.pullback f).obj B') ⟶ ((«exists» f).obj A' ⊓ B')`.
This morphism is part of a `StrongEpiMonoFactorisation` of
`(A' ⊓ (Subobject.pullback f).obj B').arrow ≫ f`, see `frobeniusStrongEpiMonoFactorisation`.
-/
/-
**CategoryTheory.Regular.frobeniusMorphism** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Regular`。
形式化陈述：frobeniusMorphism : underlying.obj (A' ⊓ (Subobject.pullback f).obj B') ⟶ 
underlying.obj ((«exists» f).obj A' ⊓ B')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `f : A ⟶ B` and subobjects `A' ⟶ A` and `B' ⟶ B`, we have a can
onical morphism
`(A' ⊓ (Subobject.pullback f).obj B') ⟶ ((«exists» f).obj A' ⊓ B')`.
This morphism is part of a `StrongEpiMonoFactorisation` of
`(A' ⊓ (Subobject.pullback f).obj B').arrow ≫ f`, see `frobeniusStrongEpiMonoFac
torisation`.
-/
noncomputable def frobeniusMorphism :
    underlying.obj (A' ⊓ (Subobject.pullback f).obj B') ⟶
      underlying.obj ((«exists» f).obj A' ⊓ B') :=
  (inf_isPullback ((«exists» f).obj A') B').flip.lift
    ((ofLE _ _ (inf_le_right A' ((Subobject.pullback f).obj B'))) ≫ (pullbackπ _ _))
    ((ofLE _ _ (inf_le_left A' ((Subobject.pullback f).obj B'))) ≫ (imageFactorisation f A').F.e)
    (by simp [← imageFactorisation_F_m, (isPullback _ _).w])

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Regular.frobeniusMorphism_isPullback** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Regular`。
形式化陈述：frobeniusMorphism_isPullback : IsPullback (frobeniusMorphism f A' B') ((of
LE _ _ (inf_le_left A' ((Subobject.pullback f).obj B')))) ((ofLE _ _ (inf_le_lef
t ((«exists» f).obj A') B'))) (imageFactorisation _ _).F.e
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Regular.toHasFiniteLimits`：∀ {C : Type u} {inst : Categor
yTheory.Category.{v, u} C} [self : CategoryTheory.Regular C],   CategoryTheory.L
imits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Subobject.inf_le_left`：inf_le_left {A : C} (f g : Subobje
ct A) : (inf.obj f).obj g <= f
· 使用定理 `CategoryTheory.IsPullback.of_right`：of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : 
C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ 
: X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.IsPullback.lift_snd`：lift_snd (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ snd = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.Subobject.inf_isPullback`：inf_isPullback {A : C} (f g : S
ubobject A) : IsPullback (ofLE (f ⊓ g) f (by simp)) (ofLE (f ⊓ g) g (by simp)) f
.arrow g.arrow
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.IsPullback.lift.congr_simp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {fst fst_1 : P ⟶ X} (e_fst : fst = 
fst_1)   {snd snd_1 : P ⟶ Y} (e…
· 使用引理 `CategoryTheory.IsPullback.lift_fst`：lift_fst (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ fst = h
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.fac`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : CategoryTheory.Lim
its.MonoFactorisation f), Categor…
· 使用定理 `CategoryTheory.IsPullback.paste_horiz_iff`：paste_horiz_iff {X₁₁ X₁₂ X₁₃ 
X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂
₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂…
· 使用定理 `CategoryTheory.Subobject.isPullback`：isPullback (f : X ⟶ Y) (y : Subobje
ct Y) : IsPullback (pullbackπ f y) ((pullback f).obj y).arrow y.arrow f
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
-/
lemma frobeniusMorphism_isPullback :
    IsPullback (frobeniusMorphism f A' B')
      ((ofLE _ _ (inf_le_left A' ((Subobject.pullback f).obj B'))))
      ((ofLE _ _ (inf_le_left ((«exists» f).obj A') B')))
      (imageFactorisation _ _).F.e := by
  apply IsPullback.of_right (t := (inf_isPullback ((«exists» f).obj A') B').flip)
    (p := by simp [frobeniusMorphism])
  simpa [frobeniusMorphism, IsPullback.lift_fst, ← imageFactorisation_F_m,
    (isPullback f B').paste_horiz_iff] using
    (inf_isPullback A' ((Subobject.pullback f).obj B')).flip

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Regular.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Regular`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsRegularEpi (frobeniusMorphism f A' B') := by
  apply regularEpiIsStableUnderBaseChange.of_isPullback (frobeniusMorphism_isPullback f A' B').flip
  have := strongEpi_of_strongEpiMonoFactorisation (strongEpiMonoFactorisation (A'.arrow ≫ f))
    (imageFactorisation f A').isImage
  simp only [MorphismProperty.regularEpi_iff]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Given a morphism `f : A ⟶ B` and subobjects `A' ⟶ A` and `B' ⟶ B`, the `frobeniusMorphism`
gives a `StrongEpiMonoFactorisation` of `(A' ⊓ (Subobject.pullback f).obj B').arrow ≫ f` through
`((«exists» f).obj A' ⊓ B').arrow`.
This is an auxiliary definition to show `frobenius_reciprocity`.
-/
@[simps!]
/-
**CategoryTheory.Regular.frobeniusStrongEpiMonoFactorisation** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Regular`。
形式化陈述：frobeniusStrongEpiMonoFactorisation : StrongEpiMonoFactorisation ((A' ⊓ (S
ubobject.pullback f).obj B').arrow ≫ f) where I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `f : A ⟶ B` and subobjects `A' ⟶ A` and `B' ⟶ B`, the `frobeniu
sMorphism`
gives a `StrongEpiMonoFactorisation` of `(A' ⊓ (Subobject.pullback f).obj B').ar
row ≫ f` through
`((«exists» f).obj A' ⊓ B').arrow`.
This is an auxiliary definition to show `frobenius_reciprocity`.
-/
noncomputable def frobeniusStrongEpiMonoFactorisation :
    StrongEpiMonoFactorisation ((A' ⊓ (Subobject.pullback f).obj B').arrow ≫ f) where
  I := underlying.obj <| («exists» f).obj A' ⊓ B'
  m := ((«exists» f).obj A' ⊓ B').arrow
  e := frobeniusMorphism f A' B'
  fac := by
    rw [frobeniusMorphism, ← inf_comp_left, ← Category.assoc,
      (inf_isPullback ((«exists» f).obj A') B').flip.lift_snd]
    simp [← imageFactorisation_F_m]

/--
Regular categories satisfy Frobenius reciprocity. That is, in the internal language of regular
categories, we have `∃ x, (P(x) ⊓ Q)` iff `(∃ x, P(x)) ⊓ Q`, for a proposition `Q` not depending on
`x`.
-/
/-
**CategoryTheory.Regular.exists_inf_pullback_eq_exists_inf** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Regular`。
形式化陈述：exists_inf_pullback_eq_exists_inf : («exists» f).obj (A' ⊓ (Subobject.pull
back f).obj B') = («exists» f).obj A' ⊓ B'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comm`：eq_of_comm {B : C} {X Y : Subobject
 B} (f : (X : C) ≅ (Y : C)) (w : f.hom ≫ Y.arrow = X.arrow) : X = Y
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Regular.toHasFiniteLimits`：∀ {C : Type u} {inst : Categor
yTheory.Category.{v, u} C} [self : CategoryTheory.Regular C],   CategoryTheory.L
imits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.IsImage.isoExt_hom_m`：isoExt_hom_m : (isoExt hF hF
').hom ≫ F'.m = F.m

--- 原说明 ---
Regular categories satisfy Frobenius reciprocity. That is, in the internal langu
age of regular
categories, we have `∃ x, (P(x) ⊓ Q)` iff `(∃ x, P(x)) ⊓ Q`, for a proposition `
Q` not depending on
`x`.
-/
theorem exists_inf_pullback_eq_exists_inf :
    («exists» f).obj (A' ⊓ (Subobject.pullback f).obj B') = («exists» f).obj A' ⊓ B' :=
  eq_of_comm
    (IsImage.isoExt (imageFactorisation _ _).isImage
      (frobeniusStrongEpiMonoFactorisation f A' B').toMonoIsImage)
    (IsImage.isoExt_hom_m (imageFactorisation _ _).isImage
      (frobeniusStrongEpiMonoFactorisation f A' B').toMonoIsImage)

end Frobenius

end Regular

end CategoryTheory

