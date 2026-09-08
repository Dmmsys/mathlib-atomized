/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Nikolas Kuhn
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
public import Mathlib.Data.Finite.Sigma

/-!
# Description of the covering sieves of the coherent topology

This file characterises the covering sieves of the coherent topology.

## Main result

* `coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily`: a sieve is a covering sieve for the
  coherent topology if and only if it contains a finite effective epimorphic family.

-/

public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [Precoherent C] {X : C}

/--
For a precoherent category, any sieve that contains an `EffectiveEpiFamily` is a sieve of the
coherent topology.
Note: This is one direction of `mem_sieves_iff_hasEffectiveEpiFamily`, but is needed for the proof.
-/
/-
**CategoryTheory.coherentTopology.mem_sieves_of_hasEffectiveEpiFamily** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.coherentTopology`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Precoherent C] {X : C}   (S : CategoryTheory.Sieve X),   (∃ α, ∃ (
_ : Finite α), ∃ Y π, CategoryTheory.EffectiveEpiFamily Y π ∧ ∀ (a : α), S.arrow
s (π a)) →     S ∈ (CategoryTheory.coherentTopology C) X
参数：S : CategoryTheory.Sieve X；∃ α, ∃ (_ : Finite α), ∃ Y π, CategoryTheory.Effec
tiveEpiFamily Y π ∧ ∀ (a : α), S.arrows (π a)；CategoryTheory.coherentTopology C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Coverage.mem_toGrothendieck_sieves_of_superset`：mem_toGro
thendieck_sieves_of_superset (K : Coverage C) {X : C} {S : Sieve X} {R : Presiev
e X} (h : R <= S) (hR : R in K X) : S in K.toGrothe…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
For a precoherent category, any sieve that contains an `EffectiveEpiFamily` is a
 sieve of the
coherent topology.
Note: This is one direction of `mem_sieves_iff_hasEffectiveEpiFamily`, but is ne
eded for the proof.
-/
theorem coherentTopology.mem_sieves_of_hasEffectiveEpiFamily (S : Sieve X) :
    (∃ (α : Type) (_ : Finite α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
      EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a))) →
        (S ∈ (coherentTopology C) X) := by
  intro ⟨α, _, Y, π, hπ⟩
  apply (coherentCoverage C).mem_toGrothendieck_sieves_of_superset (R := Presieve.ofArrows Y π)
  · exact fun _ _ h ↦ by cases h; exact hπ.2 _
  · exact ⟨_, inferInstance, Y, π, rfl, hπ.1⟩

/--
Effective epi families in a precoherent category are transitive, in the sense that an
`EffectiveEpiFamily` and an `EffectiveEpiFamily` over each member, the composition is an
`EffectiveEpiFamily`.
Note: The finiteness condition is an artifact of the proof and is probably unnecessary.
-/
/-
**CategoryTheory.EffectiveEpiFamily.transitive_of_finite** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.EffectiveEpiFamily`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTh
eory.Precoherent C] {X : C} {α : Type}   [Finite α] {Y : α → C} (π : (a : α) → Y
 a ⟶ X),   CategoryTheory.EffectiveEpiFamily Y π →     ∀ {β : α → Type} [∀ (a : 
α), Finite (β a)] {Y_n : (a : α) → β a → C} (π_n : (a : α) → (b : β a) → Y_n a b
 ⟶ Y a),       (∀ (a : α), CategoryTheory.EffectiveEpiFamily (Y_n a) (π_n a)) → 
        CategoryTheory.EffectiveEpiFamily (fun c => Y_n c.fst c.snd) fun c =>   
        CategoryTheory.CategoryStruct.comp (π_n c.fst c.snd) (π c.fst)
参数：π : (a : α) → Y a ⟶ X；a : α；β a；a : α；π_n : (a : α) → (b : β a) → Y_n a b ⟶ Y
 a；∀ (a : α), CategoryTheory.EffectiveEpiFamily (Y_n a) (π_n a)；fun c => Y_n c.f
st c.snd；π_n c.fst c.snd；π c.fst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.effectiveEpimorphic_family`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {B : C} {α : Type u_1} (X : α → C) (π : (a : α
) → X a ⟶ B),   (CategoryTheory.Presi…
· 使用定理 `CategoryTheory.Sieve.pullback_comp`：pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y
} (S : Sieve X) : S.pullback (g ≫ f) = (S.pullback f).pullback g
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable'`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] (self : CategoryTheory.GrothendieckTopolo
gy C) ⦃X Y : C⦄   ⦃S : CategoryTheory.Siev…
· 使用定理 `CategoryTheory.coherentTopology.mem_sieves_of_hasEffectiveEpiFamily`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Precoherent C] {X : C}   (S : CategoryTheory.Sieve X…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Sieve.forallYonedaIsSheaf_iff_colimit`：forallYonedaIsShea
f_iff_colimit (S : Sieve X) : (forall W : C, Presieve.IsSheafFor (yoneda.obj W) 
(S : Presieve X)) ↔ Nonempty (IsColimit S.…
· 使用定理 `CategoryTheory.coherentTopology.isSheaf_yoneda_obj`：isSheaf_yoneda_obj (
W : C) : Presieve.IsSheaf (coherentTopology C) (yoneda.obj W)

--- 原说明 ---
Effective epi families in a precoherent category are transitive, in the sense th
at an
`EffectiveEpiFamily` and an `EffectiveEpiFamily` over each member, the compositi
on is an
`EffectiveEpiFamily`.
Note: The finiteness condition is an artifact of the proof and is probably unnec
essary.
-/
theorem EffectiveEpiFamily.transitive_of_finite {α : Type} [Finite α] {Y : α → C}
    (π : (a : α) → (Y a ⟶ X)) (h : EffectiveEpiFamily Y π) {β : α → Type} [∀ (a : α), Finite (β a)]
    {Y_n : (a : α) → β a → C} (π_n : (a : α) → (b : β a) → (Y_n a b ⟶ Y a))
    (H : ∀ a, EffectiveEpiFamily (Y_n a) (π_n a)) :
    EffectiveEpiFamily
      (fun (c : Σ a, β a) => Y_n c.fst c.snd) (fun c => π_n c.fst c.snd ≫ π c.fst) := by
  rw [← Sieve.effectiveEpimorphic_family]
  suffices h₂ : (Sieve.generate (Presieve.ofArrows (fun (⟨a, b⟩ : Σ _, β _) => Y_n a b)
        (fun ⟨a,b⟩ => π_n a b ≫ π a))) ∈ (coherentTopology C) X by
    change Nonempty _
    rw [← Sieve.forallYonedaIsSheaf_iff_colimit]
    exact fun W => coherentTopology.isSheaf_yoneda_obj W _ h₂
  -- Show that a covering sieve is a colimit, which implies the original set of arrows is regular
  -- epimorphic. We use the transitivity property of saturation
  apply Coverage.Saturate.transitive X (Sieve.generate (Presieve.ofArrows Y π))
  · apply Coverage.Saturate.of
    use α, inferInstance, Y, π
  · intro V f ⟨Y₁, h, g, ⟨hY, hf⟩⟩
    rw [← hf, Sieve.pullback_comp]
    apply (coherentTopology C).pullback_stable'
    apply coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
    -- Need to show that the pullback of the family `π_n` to a given `Y i` is effective epimorphic
    obtain ⟨i⟩ := hY
    exact ⟨β i, inferInstance, Y_n i, π_n i, H i, fun b ↦
      ⟨Y_n i b, (𝟙 _), π_n i b ≫ π i, ⟨(⟨i, b⟩ : Σ (i : α), β i)⟩, by simp⟩⟩
/-
**CategoryTheory.precoherentEffectiveEpiFamilyCompEffectiveEpis** 是 Mathlib 中的一个
实例，位于命名空间 `CategoryTheory`。
形式化陈述：precoherentEffectiveEpiFamilyCompEffectiveEpis {α : Type} [Finite α] {Y Z 
: α -> C} (π : (a : α) -> (Y a ⟶ X)) [EffectiveEpiFamily Y π] (f : (a : α) -> Z 
a ⟶ Y a) [h : forall a, EffectiveEpi (f a)] : EffectiveEpiFamily _ fun a => f a 
≫ π a
参数：π : (a : α) -> (Y a ⟶ X)；f : (a : α) -> Z a ⟶ Y a；f a。
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EffectiveEpiFamily.reindex`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {B : C} {α : Type u_2} {α' : Type u_3} (X : α 
→ C)   (π : (a : α) → X a ⟶ B) …
· 使用定理 `CategoryTheory.EffectiveEpiFamily.transitive_of_finite`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Precoherent C] {X
 : C} {α : Type}   [Finite α] {Y : α → C} (π…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
instance precoherentEffectiveEpiFamilyCompEffectiveEpis
    {α : Type} [Finite α] {Y Z : α → C} (π : (a : α) → (Y a ⟶ X)) [EffectiveEpiFamily Y π]
    (f : (a : α) → Z a ⟶ Y a) [h : ∀ a, EffectiveEpi (f a)] :
    EffectiveEpiFamily _ fun a ↦ f a ≫ π a := by
  simp_rw [effectiveEpi_iff_effectiveEpiFamily] at h
  exact EffectiveEpiFamily.reindex (e := Equiv.sigmaPUnit α) _ _
    (EffectiveEpiFamily.transitive_of_finite (β := fun _ ↦ Unit) _ inferInstance _ h)

/--
A sieve belongs to the coherent topology if and only if it contains a finite
`EffectiveEpiFamily`.
-/
/-
**CategoryTheory.coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.coherentTopology`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Precoherent C] {X : C}   (S : CategoryTheory.Sieve X),   S ∈ (Cate
goryTheory.coherentTopology C) X ↔     ∃ α, ∃ (_ : Finite α), ∃ Y π, CategoryThe
ory.EffectiveEpiFamily Y π ∧ ∀ (a : α), S.arrows (π a)
参数：S : CategoryTheory.Sieve X；CategoryTheory.coherentTopology C；_ : Finite α；a :
 α；π a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.instEffectiveEpiFamily`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] {B X : C} (f : X ⟶ B) [CategoryTheory.EffectiveEpi
 f],   CategoryTheory.Effec…
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finite.instSigma`：∀ {α : Type u_1} {β : α → Type u_2} [Finite α] [∀ (a :
 α), Finite (β a)], Finite ((a : α) × β a)
· 使用定理 `CategoryTheory.EffectiveEpiFamily.transitive_of_finite`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Precoherent C] {X
 : C} {α : Type}   [Finite α] {Y : α → C} (π…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CategoryTheory.coherentTopology.mem_sieves_of_hasEffectiveEpiFamily`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Precoherent C] {X : C}   (S : CategoryTheory.Sieve X…

--- 原说明 ---
A sieve belongs to the coherent topology if and only if it contains a finite
`EffectiveEpiFamily`.
-/
theorem coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily (S : Sieve X) :
    (S ∈ (coherentTopology C) X) ↔
    (∃ (α : Type) (_ : Finite α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
        EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a))) := by
  constructor
  · intro h
    induction h with
    | of Y T hS =>
      obtain ⟨a, h, Y', π, h', _⟩ := hS
      refine ⟨a, h, Y', π, inferInstance, fun a' ↦ ?_⟩
      obtain ⟨rfl, _⟩ := h'
      exact ⟨Y' a', 𝟙 Y' a', π a', Presieve.ofArrows.mk a', by simp⟩
    | top Y =>
      exact ⟨Unit, inferInstance, fun _ => Y, fun _ => (𝟙 Y), inferInstance, by simp⟩
    | transitive Y R S _ _ a b =>
      obtain ⟨α, w, Y₁, π, ⟨h₁, h₂⟩⟩ := a
      choose β _ Y_n π_n H using fun a => b (h₂ a)
      exact ⟨(Σ a, β a), inferInstance, fun ⟨a,b⟩ => Y_n a b, fun ⟨a, b⟩ => (π_n a b) ≫ (π a),
        EffectiveEpiFamily.transitive_of_finite _ h₁ _ (fun a => (H a).1),
        fun c => (H c.fst).2 c.snd⟩
  · exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily S

end CategoryTheory

