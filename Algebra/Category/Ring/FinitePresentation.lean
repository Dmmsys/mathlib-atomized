/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation

/-!

# Finitely presentable objects in `Under R` with `R : CommRingCat`

In this file, we show that finitely presented algebras are finitely presentable in `Under R`,
i.e. `Hom_R(S, -)` preserves filtered colimits.

-/

public section

open CategoryTheory Limits

universe vJ uJ u

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J]
variable (R : CommRingCat.{u}) (F : J ⥤ CommRingCat.{u}) (α : (Functor.const _).obj R ⟶ F)
variable {S : CommRingCat.{u}} (f : R ⟶ S) (c : Cocone F) (hc : IsColimit c)
variable [PreservesColimit F (forget CommRingCat)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
/--
Given a filtered diagram `F` of rings over `R`, `S` an (essentially) of finite type `R`-algebra,
and two ring homs `a : S ⟶ Fᵢ` and `b : S ⟶ Fⱼ` over `R`.
If `a` and `b` agree at `S ⟶ colimit F`,
then there exists `k` such that `a` and `b` are equal at `S ⟶ F_k`.
In other words, the map `colimᵢ Hom_R(S, Fᵢ) ⟶ Hom_R(S, colim F)` is injective.
-/
/-
**RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit (hf : f.hom.EssFinit
eType) {i : J} (a : S ⟶ F.obj i) (ha : f ≫ a = α.app i) {j : J} (b : S ⟶ F.obj j
) (hb : f ≫ b = α.app j) (hab : a ≫ c.ι.app i = b ≫ c.ι.app j) : exists (k : J) 
(hik : i ⟶ k) (hjk : j ⟶ k), a ≫ F.map hik = b ≫ F.map hjk
参数：hf : f.hom.EssFiniteType；a : S ⟶ F.obj i；ha : f ≫ a = α.app i；b : S ⟶ F.obj j
；hb : f ≫ b = α.app j；hab : a ≫ c.ι.app i = b ≫ c.ι.app j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFiltered.cocone_nonempty`：cocone_nonempty (F : J ⥤ C) :
 Nonempty (Cocone F)
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.EssFiniteType.ext`：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   {f : R →+* S
} (hf : f.EssFi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff`：isColimit_
eq_iff {t : Cocone F} (ht : IsColimit t) {i j : J} {xi : F.obj i} {xj : F.obj j}
 : t.ι.app i xi = t.ι.app j xj ↔ exists (k : _) (f…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C

--- 原说明 ---
Given a filtered diagram `F` of rings over `R`, `S` an (essentially) of finite t
ype `R`-algebra,
and two ring homs `a : S ⟶ Fᵢ` and `b : S ⟶ Fⱼ` over `R`.
If `a` and `b` agree at `S ⟶ colimit F`,
then there exists `k` such that `a` and `b` are equal at `S ⟶ F_k`.
In other words, the map `colimᵢ Hom_R(S, Fᵢ) ⟶ Hom_R(S, colim F)` is injective.
-/
lemma RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit (hf : f.hom.EssFiniteType)
    {i : J} (a : S ⟶ F.obj i) (ha : f ≫ a = α.app i)
    {j : J} (b : S ⟶ F.obj j) (hb : f ≫ b = α.app j)
    (hab : a ≫ c.ι.app i = b ≫ c.ι.app j) :
    ∃ (k : J) (hik : i ⟶ k) (hjk : j ⟶ k),
      a ≫ F.map hik = b ≫ F.map hjk := by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  choose k f₁ f₂ h using fun x : S ↦
    (Types.FilteredColimit.isColimit_eq_iff _ hc').mp congr(($hab).hom x)
  let J' : MulticospanShape := ⟨Unit ⊕ Unit, hf.finset, fun _ ↦ .inl .unit, fun _ ↦ .inr .unit⟩
  let D : MulticospanIndex J' J :=
  { left := Sum.elim (fun _ ↦ i) (fun _ ↦ j)
    right x := k x.1
    fst x := f₁ x
    snd x := f₂ x }
  obtain ⟨c'⟩ := IsFiltered.cocone_nonempty D.multicospan
  refine ⟨c'.pt, c'.ι.app (.left (.inl .unit)), c'.ι.app (.left (.inr .unit)), ?_⟩
  ext1
  apply hf.ext
  · rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, reassoc_of% ha, reassoc_of% hb]
    simp [← α.naturality]
  · intro x hx
    rw [← c'.w (.fst (by exact ⟨x, hx⟩)), ← c'.w (.snd (by exact ⟨x, hx⟩))]
    have (x : _) : F.map (f₁ x) (a x) = F.map (f₂ x) (b x) := h x
    simp [D, this]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
/--
Given a filtered diagram `F` of rings over `R`, `S` a finitely presented `R`-algebra,
and a ring hom `g : S ⟶ colimit F` over `R`.
then there exists `i` such that `g` factors through `Fᵢ`.
In other words, the map `colimᵢ Hom_R(S, Fᵢ) ⟶ Hom_R(S, colim F)` is surjective.
-/
/-
**RingHom.EssFiniteType.exists_eq_comp_** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a filtered diagram `F` of rings over `R`, `S` a finitely presented `R`-alg
ebra,
and a ring hom `g : S ⟶ colimit F` over `R`.
then there exists `i` such that `g` factors through `Fᵢ`.
In other words, the map `colimᵢ Hom_R(S, Fᵢ) ⟶ Hom_R(S, colim F)` is surjective.
-/
lemma RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit (hf : f.hom.FinitePresentation)
    (g : S ⟶ c.pt) (hg : ∀ i, f ≫ g = α.app i ≫ c.ι.app i) :
    ∃ (i : J) (g' : S ⟶ F.obj i), f ≫ g' = α.app i ∧ g = g' ≫ c.ι.app i := by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  let := f.hom.toAlgebra
  obtain ⟨n, hn⟩ := hf
  let P := CommRingCat.of (MvPolynomial (Fin n) R)
  let iP : R ⟶ P := CommRingCat.ofHom MvPolynomial.C
  obtain ⟨π, rfl, hπ, s, hs⟩ :
      ∃ π : P ⟶ S, iP ≫ π = f ∧ Function.Surjective π ∧ (RingHom.ker π.hom).FG := by
    obtain ⟨π, h₁, h₂⟩ := hn
    exact ⟨CommRingCat.ofHom π, by ext1; exact π.comp_algebraMap, h₁, h₂⟩
  obtain ⟨i, g', hg', hg''⟩ : ∃ (i : J) (g' : P ⟶ F.obj i),
      π ≫ g = g' ≫ c.ι.app i ∧ iP ≫ g' = α.app i := by
    choose j x h using fun i ↦ Types.jointly_surjective_of_isColimit hc' ((π ≫ g) (.X i))
    obtain ⟨i, ⟨hi⟩⟩ : ∃ i, Nonempty (∀ a, (j a ⟶ i)) := by
      have : ∃ i, ∀ a, Nonempty (j a ⟶ i) := by
        simpa using! IsFiltered.sup_objs_exists (Finset.univ.image j)
      simpa [← exists_true_iff_nonempty, Classical.skolem, -exists_const_iff] using! this
    refine ⟨i, CommRingCat.ofHom (MvPolynomial.eval₂Hom
      (α.app i).hom (F.map (hi _) <| x ·)), ?_, ?_⟩
    · ext1
      apply MvPolynomial.ringHom_ext
      · simpa using! fun x ↦ congr($(hg i).hom x)
      · intro i
        simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
          Functor.const_obj_obj, CommRingCat.hom_ofHom, MvPolynomial.coe_eval₂Hom,
          MvPolynomial.eval₂_X]
        exact (congr($(c.w (hi i)).hom (x i)).trans (h i)).symm
    · ext x
      simp [P, iP]
  have : ∀ r : s, ∃ (i' : J) (hi' : i ⟶ i'), F.map hi' (g' r) = 0 := by
    intro r
    have := Types.FilteredColimit.isColimit_eq_iff _ hc' (xi := g' r) (j := i) (xj := (0 : F.obj i))
    suffices H : (g' ≫ c.ι.app i) r = 0 by
      obtain ⟨k, f, g, e⟩ := this.mp (by simpa using! H)
      exact ⟨k, f, by simpa using! e⟩
    rw [← hg']
    simp [show π r = 0 from hs.le (Ideal.subset_span r.2)]
  choose i' hi' hi'' using this
  obtain ⟨c'⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan i i' hi')
  refine ⟨c'.pt, CommRingCat.ofHom (RingHom.liftOfSurjective π.hom hπ
    ⟨(g' ≫ F.map (c'.ι.app none)).hom, ?_⟩), ?_, ?_⟩
  · rw [← hs, Ideal.span_le]
    intro r hr
    rw [← c'.w (.init ⟨r, hr⟩)]
    simp [hi'']
  · ext x
    suffices (iP ≫ g' ≫ F.map (c'.ι.app none)) x = α.app c'.pt x by
      simpa [RingHom.liftOfRightInverse_comp_apply] using! this
    rw [← Category.assoc, hg'', ← NatTrans.naturality]
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
  · ext x
    obtain ⟨x, rfl⟩ := hπ x
    suffices (π ≫ g) x = (g' ≫ F.map (c'.ι.app none) ≫ c.ι.app _) x by
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom,
        RingHom.liftOfRightInverse_comp_apply, coe_comp, Function.comp_apply] using! this
    rw [c.w, hg']
    rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `S` is a finitely presented `R`-algebra, then `Hom_R(S, -)` preserves filtered colimits. -/
/-
**CommRingCat.preservesColimit_coyoneda_of_finitePresentation** 是 Mathlib 中的一个引理
，位于命名空间 ``。
形式化陈述：CommRingCat.preservesColimit_coyoneda_of_finitePresentation (S : Under R) 
(hS : S.hom.hom.FinitePresentation) (F : J ⥤ Under R) [PreservesColimit (F ⋙ Und
er.forget R) (forget CommRingCat)] : PreservesColimit F (coyoneda.obj (.op S))
参数：S : Under R；hS : S.hom.hom.FinitePresentation；F : J ⥤ Under R；F ⋙ Under.forge
t R；forget CommRingCat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Under.w`：w : f.hom ≫ φ.right = g.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`：RingHom.EssFini
teType.exists_eq_comp_ι_app_of_isColimit (hf : f.hom.FinitePresentation) (g : S 
⟶ c.pt) (hg : forall i, f ≫ g = α.app i ≫ c.ι…
· 使用定理 `CategoryTheory.Limits.PreservesColimit.preserves`：∀ {C : Type u₁} {inst 
: CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instPreservesFilteredColimitsOfSizeUnderForget`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C},   Category
Theory.Limits.PreservesFilteredColimitsOfSize.{u_2, u_3, v…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.Under.UnderMorphism.ext`：∀ {T : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Under X} {f g : U ⟶ V}
,   CategoryTheory.Under.Hom…
· 使用引理 `RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit`：RingHom.EssFinite
Type.exists_comp_map_eq_of_isColimit (hf : f.hom.EssFiniteType) {i : J} (a : S ⟶
 F.obj i) (ha : f ≫ a = α.app i) {j : J} (b…
· 使用定理 `RingHom.FiniteType.essFiniteType`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] {f : R →+* S}, f.FiniteType → f.EssFiniteTyp
e
· 使用定理 `RingHom.FiniteType.of_finitePresentation`：of_finitePresentation {f : A -
>+* B} (hf : f.FinitePresentation) : f.FiniteType

--- 原说明 ---
If `S` is a finitely presented `R`-algebra, then `Hom_R(S, -)` preserves filtere
d colimits.
-/
lemma CommRingCat.preservesColimit_coyoneda_of_finitePresentation
    (S : Under R) (hS : S.hom.hom.FinitePresentation) (F : J ⥤ Under R)
    [PreservesColimit (F ⋙ Under.forget R) (forget CommRingCat)] :
    PreservesColimit F (coyoneda.obj (.op S)) := by
  constructor
  intro c hc
  refine ⟨Types.FilteredColimit.isColimitOf _ _ ?_ ?_⟩
  · intro f
    obtain ⟨i, g, h₁, h₂⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
       R (F ⋙ Under.forget R) { app i := (F.obj i).hom } S.hom ((Under.forget R).mapCocone c)
      (PreservesColimit.preserves hc).some hS f.right (by simp)
    exact ⟨i, Under.homMk g h₁, Under.UnderMorphism.ext h₂⟩
  · intro i j f₁ f₂ e
    obtain ⟨k, hik, hjk, e⟩ := RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit
      R (F ⋙ Under.forget R) { app i := (F.obj i).hom } S.hom ((Under.forget R).mapCocone c)
      (PreservesColimit.preserves hc).some
      (RingHom.FiniteType.of_finitePresentation hS).essFiniteType
      f₁.right (Under.w f₁) f₂.right (Under.w f₂) congr($(e).right)
    exact ⟨k, hik, hjk, Under.UnderMorphism.ext e⟩

/-- If `S` is a finitely presented `R`-algebra, then `Hom_R(S, -)` preserves filtered colimits. -/
/-
**CommRingCat.preservesFilteredColimits_coyoneda** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CommRingCat.preservesFilteredColimits_coyoneda (S : Under R) (hS : S.hom.h
om.FinitePresentation) : PreservesFilteredColimits (coyoneda.obj (.op S))
参数：S : Under R；hS : S.hom.hom.FinitePresentation。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommRingCat.preservesColimit_coyoneda_of_finitePresentation`：CommRingCat
.preservesColimit_coyoneda_of_finitePresentation (S : Under R) (hS : S.hom.hom.F
initePresentation) (F : J ⥤ Under R) [PreservesCo…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `S` is a finitely presented `R`-algebra, then `Hom_R(S, -)` preserves filtere
d colimits.
-/
lemma CommRingCat.preservesFilteredColimits_coyoneda (S : Under R)
    (hS : S.hom.hom.FinitePresentation) :
    PreservesFilteredColimits (coyoneda.obj (.op S)) :=
  ⟨fun _ _ _ ↦ ⟨preservesColimit_coyoneda_of_finitePresentation R S hS _⟩⟩

/-- If `S` is a finitely presented `R`-algebra, `S : Under R` is finitely presentable. -/
/-
**CommRingCat.isFinitelyPresentable_under** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CommRingCat.isFinitelyPresentable_under (S : Under R) (hS : S.hom.hom.Fini
tePresentation) : IsFinitelyPresentable.{u} S
参数：S : Under R；hS : S.hom.hom.FinitePresentation。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits`：isFi
nitelyPresentable_iff_preservesFilteredColimits {X : C} : IsFinitelyPresentable.
{v} X ↔ PreservesFilteredColimits (coyoneda.obj (op X))
· 使用引理 `CommRingCat.preservesFilteredColimits_coyoneda`：CommRingCat.preservesFil
teredColimits_coyoneda (S : Under R) (hS : S.hom.hom.FinitePresentation) : Prese
rvesFilteredColimits (coyoneda.obj (…

--- 原说明 ---
If `S` is a finitely presented `R`-algebra, `S : Under R` is finitely presentabl
e.
-/
lemma CommRingCat.isFinitelyPresentable_under (S : Under R) (hS : S.hom.hom.FinitePresentation) :
    IsFinitelyPresentable.{u} S := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimits]
  exact preservesFilteredColimits_coyoneda R S hS

variable {R} in
/-
**CommRingCat.isFinitelyPresentable_hom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CommRingCat.isFinitelyPresentable_hom {S : CommRingCat.{u}} (f : R ⟶ S) (h
f : f.hom.FinitePresentation) : MorphismProperty.isFinitelyPresentable.{u} _ f
参数：f : R ⟶ S；hf : f.hom.FinitePresentation。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommRingCat.isFinitelyPresentable_under`：CommRingCat.isFinitelyPresentab
le_under (S : Under R) (hS : S.hom.hom.FinitePresentation) : IsFinitelyPresentab
le.{u} S
-/
lemma CommRingCat.isFinitelyPresentable_hom {S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : f.hom.FinitePresentation) :
    MorphismProperty.isFinitelyPresentable.{u} _ f :=
  isFinitelyPresentable_under R (Under.mk f) hf
