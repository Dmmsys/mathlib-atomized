/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# The jointly surjective precoverage

In the category of types, the jointly surjective precoverage has the jointly surjective
families as coverings. We show that this precoverage is stable under the standard constructions.

## Notes

See `Mathlib/CategoryTheory/Sites/Types.lean` for the Grothendieck topology of jointly surjective
covers.
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

namespace Types

/-- The jointly surjective precoverage in the category of types has the jointly surjective
families as coverings. -/
/-
**CategoryTheory.Types.jointlySurjectivePrecoverage** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Types`。
形式化陈述：jointlySurjectivePrecoverage : Precoverage (Type u) where coverings X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The jointly surjective precoverage in the category of types has the jointly surj
ective
families as coverings.
-/
def jointlySurjectivePrecoverage : Precoverage (Type u) where
  coverings X := {R | ∀ x : X, ∃ (Y : Type u) (g : Y ⟶ X), R g ∧ x ∈ Set.range g}
/-
**CategoryTheory.Types.mem_jointlySurjectivePrecoverage_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Types`。
形式化陈述：mem_jointlySurjectivePrecoverage_iff {X : Type u} {R : Presieve X} : R in 
jointlySurjectivePrecoverage X ↔ forall x : X, exists (Y : Type u) (g : Y ⟶ X), 
R g ∧ x in Set.range g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_jointlySurjectivePrecoverage_iff {X : Type u} {R : Presieve X} :
    R ∈ jointlySurjectivePrecoverage X ↔
      ∀ x : X, ∃ (Y : Type u) (g : Y ⟶ X), R g ∧ x ∈ Set.range g :=
  .rfl
/-
**CategoryTheory.Types.singleton_mem_jointlySurjectivePrecoverage_iff** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Types`。
形式化陈述：singleton_mem_jointlySurjectivePrecoverage_iff {X Y : Type u} {f : X ⟶ Y} 
: Presieve.singleton f in jointlySurjectivePrecoverage Y ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Types.mem_jointlySurjectivePrecoverage_iff`：mem_jointlySu
rjectivePrecoverage_iff {X : Type u} {R : Presieve X} : R in jointlySurjectivePr
ecoverage X ↔ forall x : X, exists (Y : Type u)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
-/
lemma singleton_mem_jointlySurjectivePrecoverage_iff {X Y : Type u} {f : X ⟶ Y} :
    Presieve.singleton f ∈ jointlySurjectivePrecoverage Y ↔ Function.Surjective f := by
  rw [mem_jointlySurjectivePrecoverage_iff]
  refine ⟨fun hf x ↦ ?_, fun hf x ↦ ⟨X, f, ⟨⟩, by simp [hf.range_eq]⟩⟩
  obtain ⟨_, _, ⟨⟩, hx⟩ := hf x
  exact hx

@[simp]
/-
**CategoryTheory.Types.ofArrows_mem_jointlySurjectivePrecoverage_iff** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Types`。
形式化陈述：ofArrows_mem_jointlySurjectivePrecoverage_iff {X : Type u} {ι : Type*} {Y 
: ι -> Type u} {f : forall i, Y i ⟶ X} : Presieve.ofArrows Y f in jointlySurject
ivePrecoverage X ↔ forall x, exists (i : ι), x in Set.range (f i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma ofArrows_mem_jointlySurjectivePrecoverage_iff {X : Type u} {ι : Type*}
    {Y : ι → Type u} {f : ∀ i, Y i ⟶ X} :
    Presieve.ofArrows Y f ∈ jointlySurjectivePrecoverage X ↔
      ∀ x, ∃ (i : ι), x ∈ Set.range (f i) := by
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨Y, g, ⟨i⟩, hx⟩ := h x
    use i
  · obtain ⟨i, hx⟩ := h x
    use Y i, f i, ⟨i⟩
/-
**CategoryTheory.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : jointlySurjectivePrecoverage.HasIsos where
  mem_coverings_of_isIso {S T} f hf x := by
    use S, f, ⟨⟩
    exact surjective_of_epi f x
/-
**CategoryTheory.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : jointlySurjectivePrecoverage.IsStableUnderComposition where
  comp_mem_coverings {ι} S X f hf σ Y g hg := by
    simp_rw [ofArrows_mem_jointlySurjectivePrecoverage_iff] at hf hg ⊢
    intro x
    obtain ⟨i, y, rfl⟩ := hf x
    obtain ⟨j, z, rfl⟩ := hg i y
    use ⟨i, j⟩, z
    simp
/-
**CategoryTheory.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : jointlySurjectivePrecoverage.IsStableUnderSup where
  sup_mem_coverings {X} R S hR _ x := by
    obtain ⟨Y, f, hf, hx⟩ := hR x
    use Y, f, .inl hf
/-
**CategoryTheory.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Precoverage.Small.{u} jointlySurjectivePrecoverage.{u} where
  zeroHypercoverSmall {X} E := by
    choose i y hy using ofArrows_mem_jointlySurjectivePrecoverage_iff.mp E.mem₀
    refine ⟨X, i, ?_⟩
    rw [ofArrows_mem_jointlySurjectivePrecoverage_iff]
    intro x
    use x, y x, hy x

end Types

variable {C : Type*} [Category* C] (F : C ⥤ Type u)

/-
**CategoryTheory.Presieve.mem_comap_jointlySurjectivePrecoverage_iff** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Presieve`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (F : Catego
ryTheory.Functor C (Type u)) {X : C}   {R : CategoryTheory.Presieve X},   R ∈ (C
ategoryTheory.Precoverage.comap F CategoryTheory.Types.jointlySurjectivePrecover
age).coverings X ↔     ∀ (x : F.obj X), ∃ Y f, R f ∧ x ∈ Set.range ⇑(CategoryThe
ory.ConcreteCategory.hom (F.map f))
参数：F : CategoryTheory.Functor C (Type u)；CategoryTheory.Precoverage.comap F Cate
goryTheory.Types.jointlySurjectivePrecoverage；x : F.obj X；CategoryTheory.Concret
eCategory.hom (F.map f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Precoverage.mem_comap_iff`：mem_comap_iff {X : C} {R : Pre
sieve X} : R in J.comap F X ↔ R.map F in J (F.obj X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma Presieve.mem_comap_jointlySurjectivePrecoverage_iff {X : C} {R : Presieve X} :
    R ∈ Types.jointlySurjectivePrecoverage.comap F X ↔
      ∀ x : F.obj X, ∃ (Y : C) (f : Y ⟶ X), R f ∧ x ∈ Set.range (F.map f) := by
  rw [Precoverage.mem_comap_iff]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨-, -, ⟨hf⟩, hi⟩ := h x
    exact ⟨_, _, hf, hi⟩
  · obtain ⟨Y, g, hg, hi⟩ := h x
    exact ⟨_, _, ⟨hg⟩, hi⟩
/-
**CategoryTheory.Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff** 
是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Presieve`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (F : Catego
ryTheory.Functor C (Type u)) {X : C}   {ι : Type u_2} {Y : ι → C} {f : (i : ι) →
 Y i ⟶ X},   CategoryTheory.Presieve.ofArrows Y f ∈       (CategoryTheory.Precov
erage.comap F CategoryTheory.Types.jointlySurjectivePrecoverage).coverings X ↔  
   ∀ (x : F.obj X), ∃ i, x ∈ Set.range ⇑(CategoryTheory.ConcreteCategory.hom (F.
map (f i)))
参数：F : CategoryTheory.Functor C (Type u)；i : ι；CategoryTheory.Precoverage.comap 
F CategoryTheory.Types.jointlySurjectivePrecoverage；x : F.obj X；CategoryTheory.C
oncreteCategory.hom (F.map (f i))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presieve.map_ofArrows`：map_ofArrows {X : C} {ι : Type*} {
Y : ι -> C} (f : forall i, Y i ⟶ X) : (ofArrows Y f).map F = ofArrows _ (fun i =
> F.map (f i))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff {X : C} {ι : Type*}
    {Y : ι → C} {f : ∀ i, Y i ⟶ X} :
    ofArrows Y f ∈ Types.jointlySurjectivePrecoverage.comap F X ↔
      ∀ x : F.obj X, ∃ (i : ι), x ∈ Set.range (F.map (f i)) := by
  simp

/-- The pullback of the jointly surjective precoverage of types to any category `C` via a
(forgetful) functor `C ⥤ Type u` is stable under base change if the canonical map
`F (X ×[Y] Z) ⟶ F(X) ×[F(Y)] F(Z)` is surjective. -/
/-
**CategoryTheory.isStableUnderBaseChange_comap_jointlySurjectivePrecoverage** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isStableUnderBaseChange_comap_jointlySurjectivePrecoverage (H : forall {X 
Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g], Function.Surjective (pullbac
kComparison F f g)) : (Types.jointlySurjectivePrecoverage.comap F).IsStableUnder
BaseChange where mem_coverings_of_isPullback {ι} S X f hf Y g P p₁ p₂ h
参数：H : forall {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g], Function.Su
rjective (pullbackComparison F f g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Precoverage.mem_comap_iff`：mem_comap_iff {X : C} {R : Pre
sieve X} : R in J.comap F X ↔ R.map F in J (F.obj X)
· 使用引理 `CategoryTheory.Presieve.map_ofArrows`：map_ofArrows {X : C} {ι : Type*} {
Y : ι -> C} (f : forall i, Y i ⟶ X) : (ofArrows Y f).map F = ofArrows _ (fun i =
> F.map (f i))
· 使用引理 `CategoryTheory.Types.ofArrows_mem_jointlySurjectivePrecoverage_iff`：ofAr
rows_mem_jointlySurjectivePrecoverage_iff {X : Type u} {ι : Type*} {Y : ι -> Typ
e u} {f : forall i, Y i ⟶ X} : Presieve.ofArrows Y f in …
· 使用引理 `CategoryTheory.IsPullback.hasPullback`：hasPullback (h : IsPullback fst s
nd f g) : HasPullback f g where exists_limit
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.pullbackComparison_comp_fst`：pullbackComparison_co
mp_fst (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g
)] : pullbackComparison G f g ≫ pullbac…
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_fst`：isoPullback_hom_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.fst _ _
 = fst
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.types_comp`：types_comp {X Y Z : Type u} (f : X ⟶ Y) (g : 
Y ⟶ Z) : ConcreteCategory.hom (f ≫ g) = g ∘ f
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `CategoryTheory.surjective_of_epi`：surjective_of_epi {X Y : Type u} (f : 
X ⟶ Y) [hf : Epi f] : Function.Surjective f
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `CategoryTheory.Limits.Types.range_pullbackFst`：∀ {X Y Z : Type u} (f : X
 ⟶ Z) (g : Y ⟶ Z),   Set.range ⇑(CategoryTheory.ConcreteCategory.hom (CategoryTh
eory.Limits.pullback.fst f g)) =   …

--- 原说明 ---
The pullback of the jointly surjective precoverage of types to any category `C` 
via a
(forgetful) functor `C ⥤ Type u` is stable under base change if the canonical ma
p
`F (X ×[Y] Z) ⟶ F(X) ×[F(Y)] F(Z)` is surjective.
-/
lemma isStableUnderBaseChange_comap_jointlySurjectivePrecoverage
    (H : ∀ {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g],
      Function.Surjective (pullbackComparison F f g)) :
    (Types.jointlySurjectivePrecoverage.comap F).IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S X f hf Y g P p₁ p₂ h := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows,
      Types.ofArrows_mem_jointlySurjectivePrecoverage_iff] at hf ⊢
    intro x
    obtain ⟨i, hi⟩ := hf (F.map g x)
    have : HasPullback g (f i) := (h i).hasPullback
    use i
    have : F.map (p₁ i) = F.map ((h i).isoPullback.hom) ≫ pullbackComparison F g (f i) ≫
        pullback.fst _ _ := by simp [← Functor.map_comp]
    rwa [this, types_comp, types_comp, Function.comp_assoc, Set.range_comp,
      Function.Surjective.range_eq <| (H _ _).comp (surjective_of_epi _), Set.image_univ,
      Types.range_pullbackFst]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Types.jointlySurjectivePrecoverage.IsStableUnderBaseChange := by
  rw [← Precoverage.comap_id Types.jointlySurjectivePrecoverage]
  apply isStableUnderBaseChange_comap_jointlySurjectivePrecoverage
  intro X Y S f g _
  exact surjective_of_epi _

end CategoryTheory

