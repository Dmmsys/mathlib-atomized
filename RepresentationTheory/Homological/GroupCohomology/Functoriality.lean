/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Functoriality of group cohomology

Given a commutative ring `k`, a group homomorphism `f : G →* H`, a `k`-linear `H`-representation
`A`, a `k`-linear `G`-representation `B`, and a representation morphism `Res(f)(A) ⟶ B`, we get
a cochain map `inhomogeneousCochains A ⟶ inhomogeneousCochains B` and hence maps on
cohomology `Hⁿ(H, A) ⟶ Hⁿ(G, B)`.
We also provide extra API for these maps in degrees 0, 1, 2.

## Main definitions

* `groupCohomology.cochainsMap f φ` is the map `inhomogeneousCochains A ⟶ inhomogeneousCochains B`
  induced by a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`.
* `groupCohomology.map f φ n` is the map `Hⁿ(H, A) ⟶ Hⁿ(G, B)` induced by a group
  homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`.
* `groupCohomology.H1InfRes A S` is the short complex `H¹(G ⧸ S, A^S) ⟶ H¹(G, A) ⟶ H¹(S, A)` for
  a normal subgroup `S ≤ G` and a `G`-representation `A`.

-/

@[expose] public section

universe v u

namespace groupCohomology
open Rep CategoryTheory Representation

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  {A : Rep k H} {B : Rep k G} (f : G →* H) (φ : res f A ⟶ B) (n : ℕ)

section

/-
**groupCohomology.congr** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
形式化陈述：congr {f₁ f₂ : G ->* H} (h : f₁ = f₂) {φ : res f₁ A ⟶ B} {T : Type*} (F : 
(f : G ->* H) -> (φ : res f A ⟶ B) -> T) : F f₁ φ = F f₂ (h ▸ φ)
参数：h : f₁ = f₂；F : (f : G ->* H) -> (φ : res f A ⟶ B) -> T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr {f₁ f₂ : G →* H} (h : f₁ = f₂) {φ : res f₁ A ⟶ B} {T : Type*}
    (F : (f : G →* H) → (φ : res f A ⟶ B) → T) :
    F f₁ φ = F f₂ (h ▸ φ) := by
  subst h
  rfl

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the chain map sending `x : Hⁿ → A` to `(g : Gⁿ) ↦ φ (x (f ∘ g))`. -/
@[simps! -isSimp f f_hom]
/-
**groupCohomology.cochainsMap** 是 Mathlib 中的一个定义，位于命名空间 `groupCohomology`。
形式化陈述：cochainsMap : inhomogeneousCochains A ⟶ inhomogeneousCochains B where f i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f
)(A) ⟶ B`,
this is the chain map sending `x : Hⁿ → A` to `(g : Gⁿ) ↦ φ (x (f ∘ g))`.
-/
noncomputable def cochainsMap :
    inhomogeneousCochains A ⟶ inhomogeneousCochains B where
  f i := ModuleCat.ofHom <|
    φ.hom.toLinearMap.compLeft (Fin i → G) ∘ₗ LinearMap.funLeft k A (fun x : Fin i → G => (f ∘ x))
  comm' i j (hij : _ = _) := by
    subst hij
    ext
    simpa [inhomogeneousCochains.d_hom_apply, Fin.comp_contractNth, CochainComplex.of.d]
      using! (hom_comm_apply φ _ _).symm

@[simp]
/-
**groupCohomology.cochainsMap_id** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
形式化陈述：cochainsMap_id : cochainsMap (MonoidHom.id _) (𝟙 A) = 𝟙 (inhomogeneousCoch
ains A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma cochainsMap_id :
    cochainsMap (MonoidHom.id _) (𝟙 A) = 𝟙 (inhomogeneousCochains A) := by
  rfl

@[simp]
/-
**groupCohomology.cochainsMap_id_f_hom_eq_compLeft** 是 Mathlib 中的一个引理，位于命名空间 `gr
oupCohomology`。
形式化陈述：cochainsMap_id_f_hom_eq_compLeft {A B : Rep k G} (f : A ⟶ B) (i : Nat) : (
(cochainsMap (MonoidHom.id G) f).f i).hom = f.hom.toLinearMap.compLeft _
参数：f : A ⟶ B；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma cochainsMap_id_f_hom_eq_compLeft {A B : Rep k G} (f : A ⟶ B) (i : ℕ) :
    ((cochainsMap (MonoidHom.id G) f).f i).hom = f.hom.toLinearMap.compLeft _ := rfl

@[reassoc]
/-
**groupCohomology.cochainsMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
形式化陈述：cochainsMap_comp {G H K : Type u} [Group G] [Group H] [Group K] {A : Rep k
 K} {B : Rep k H} {C : Rep k G} (f : H ->* K) (g : G ->* H) (φ : res f A ⟶ B) (ψ
 : res g B ⟶ C) : cochainsMap (f.comp g) ((resFunctor g).map φ ≫ ψ) = cochainsMa
p f φ ≫ cochainsMap g ψ
参数：f : H ->* K；g : G ->* H；φ : res f A ⟶ B；ψ : res g B ⟶ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma cochainsMap_comp {G H K : Type u} [Group G] [Group H]
    [Group K] {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : res f A ⟶ B) (ψ : res g B ⟶ C) :
    cochainsMap (f.comp g) ((resFunctor g).map φ ≫ ψ) =
      cochainsMap f φ ≫ cochainsMap g ψ := by
  rfl

@[reassoc]
/-
**groupCohomology.cochainsMap_id_comp** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology
`。
形式化陈述：cochainsMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) : cochainsMa
p (MonoidHom.id G) (φ ≫ ψ) = cochainsMap (MonoidHom.id G) φ ≫ cochainsMap (Monoi
dHom.id G) ψ
参数：φ : A ⟶ B；ψ : B ⟶ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma cochainsMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    cochainsMap (MonoidHom.id G) (φ ≫ ψ) =
      cochainsMap (MonoidHom.id G) φ ≫ cochainsMap (MonoidHom.id G) ψ := by
  rfl

@[simp]
/-
**groupCohomology.cochainsMap_zero** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
形式化陈述：cochainsMap_zero : cochainsMap (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma cochainsMap_zero : cochainsMap (A := A) (B := B) f 0 = 0 := by rfl
/-
**groupCohomology.cochainsMap_f_map_mono** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomol
ogy`。
形式化陈述：cochainsMap_f_map_mono (hf : Function.Surjective f) [Mono φ] (i : Nat) : M
ono ((cochainsMap f φ).f i)
参数：hf : Function.Surjective f；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Function.Injective.comp_left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort 
u_3} {g : β → γ}, Function.Injective g → Function.Injective fun x => g ∘ x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Rep.mono_iff_injective`：mono_iff_injective (f : A ⟶ B) : Mono f ↔ Functi
on.Injective f.hom
· 使用定理 `LinearMap.funLeft_injective_of_surjective`：funLeft_injective_of_surjecti
ve (f : m -> n) (hf : Surjective f) : Injective (funLeft R M f)
· 使用定理 `Function.Surjective.comp_left`：∀ {α : Sort u} {β : Sort v} {γ : Sort w} 
{g : β → γ}, Function.Surjective g → Function.Surjective fun x => g ∘ x
-/
lemma cochainsMap_f_map_mono (hf : Function.Surjective f) [Mono φ] (i : ℕ) :
    Mono ((cochainsMap f φ).f i) := by
  simpa [ModuleCat.mono_iff_injective] using!
    ((Rep.mono_iff_injective φ).1 inferInstance).comp_left.comp <|
    LinearMap.funLeft_injective_of_surjective k A _ hf.comp_left
/-
**groupCohomology.cochainsMap_id_f_map_mono** 是 Mathlib 中的一个实例，位于命名空间 `groupCoho
mology`。
形式化陈述：cochainsMap_id_f_map_mono {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : Nat) :
 Mono ((cochainsMap (MonoidHom.id G) φ).f i)
参数：φ : A ⟶ B；i : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `groupCohomology.cochainsMap_f_map_mono`：cochainsMap_f_map_mono (hf : Fun
ction.Surjective f) [Mono φ] (i : Nat) : Mono ((cochainsMap f φ).f i)
-/
instance cochainsMap_id_f_map_mono {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : ℕ) :
    Mono ((cochainsMap (MonoidHom.id G) φ).f i) :=
  cochainsMap_f_map_mono (MonoidHom.id G) φ (fun x => ⟨x, rfl⟩) i
/-
**groupCohomology.cochainsMap_f_map_epi** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomolo
gy`。
形式化陈述：cochainsMap_f_map_epi (hf : Function.Injective f) [Epi φ] (i : Nat) : Epi 
((cochainsMap f φ).f i)
参数：hf : Function.Injective f；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Function.Surjective.comp_left`：∀ {α : Sort u} {β : Sort v} {γ : Sort w} 
{g : β → γ}, Function.Surjective g → Function.Surjective fun x => g ∘ x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Rep.epi_iff_surjective`：epi_iff_surjective (f : A ⟶ B) : Epi f ↔ Functio
n.Surjective f.hom
· 使用定理 `LinearMap.funLeft_surjective_of_injective`：funLeft_surjective_of_injecti
ve (f : m -> n) (hf : Injective f) : Surjective (funLeft R M f)
· 使用定理 `Function.Injective.comp_left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort 
u_3} {g : β → γ}, Function.Injective g → Function.Injective fun x => g ∘ x
-/
lemma cochainsMap_f_map_epi (hf : Function.Injective f) [Epi φ] (i : ℕ) :
    Epi ((cochainsMap f φ).f i) := by
  simpa [ModuleCat.epi_iff_surjective] using!
    ((Rep.epi_iff_surjective φ).1 inferInstance).comp_left.comp <|
    LinearMap.funLeft_surjective_of_injective k A _ hf.comp_left
/-
**groupCohomology.cochainsMap_id_f_map_epi** 是 Mathlib 中的一个实例，位于命名空间 `groupCohom
ology`。
形式化陈述：cochainsMap_id_f_map_epi {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : Nat) : E
pi ((cochainsMap (MonoidHom.id G) φ).f i)
参数：φ : A ⟶ B；i : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `groupCohomology.cochainsMap_f_map_epi`：cochainsMap_f_map_epi (hf : Funct
ion.Injective f) [Epi φ] (i : Nat) : Epi ((cochainsMap f φ).f i)
-/
instance cochainsMap_id_f_map_epi {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : ℕ) :
    Epi ((cochainsMap (MonoidHom.id G) φ).f i) :=
  cochainsMap_f_map_epi (MonoidHom.id G) φ (fun _ _ h => h) i

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map `Zⁿ(H, A) ⟶ Zⁿ(G, B)` sending `x : Hⁿ → A` to
`(g : Gⁿ) ↦ φ (x (f ∘ g))`. -/
/-
**groupCohomology.cocyclesMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomology`。
形式化陈述：cocyclesMap (n : Nat) : groupCohomology.cocycles A n ⟶ groupCohomology.coc
ycles B n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f
)(A) ⟶ B`,
this is the induced map `Zⁿ(H, A) ⟶ Zⁿ(G, B)` sending `x : Hⁿ → A` to
`(g : Gⁿ) ↦ φ (x (f ∘ g))`.
-/
noncomputable abbrev cocyclesMap (n : ℕ) :
    groupCohomology.cocycles A n ⟶ groupCohomology.cocycles B n :=
  HomologicalComplex.cyclesMap (cochainsMap f φ) n
/-
**groupCohomology.cochainsMap_congr** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
形式化陈述：cochainsMap_congr {f g : G ->* H} {φ : res f A ⟶ B} {ψ : res g A ⟶ B} (hfg
 : f = g) (hφψ : φ.hom.toLinearMap = ψ.hom.toLinearMap) : cochainsMap f φ = coch
ainsMap g ψ
参数：hfg : f = g；hφψ : φ.hom.toLinearMap = ψ.hom.toLinearMap。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Rep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : M
onoid G] {A B : Rep.{w, u, v} k G} {f g : A ⟶ B},   Rep.Hom.hom f = Rep.Hom.hom 
g…
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cochainsMap_congr {f g : G →* H} {φ : res f A ⟶ B} {ψ : res g A ⟶ B} (hfg : f = g)
    (hφψ : φ.hom.toLinearMap = ψ.hom.toLinearMap) :
    cochainsMap f φ = cochainsMap g ψ := by
  subst hfg; congr; ext; simp [hφψ]

@[simp]
/-
**groupCohomology.cocyclesMap_id** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
形式化陈述：cocyclesMap_id : cocyclesMap (MonoidHom.id G) (𝟙 B) n = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.cyclesMap_id`：cyclesMap_id : cyclesMap (𝟙 K) i = 𝟙 _
-/
lemma cocyclesMap_id : cocyclesMap (MonoidHom.id G) (𝟙 B) n = 𝟙 _ :=
  HomologicalComplex.cyclesMap_id _ _

@[reassoc]
/-
**groupCohomology.cocyclesMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
形式化陈述：cocyclesMap_comp {G H K : Type u} [Group G] [Group H] [Group K] {A : Rep k
 K} {B : Rep k H} {C : Rep k G} (f : H ->* K) (g : G ->* H) (φ : res f A ⟶ B) (ψ
 : res g B ⟶ C) (n : Nat) : cocyclesMap (f.comp g) ((resFunctor g).map φ ≫ ψ) n 
= cocyclesMap f φ n ≫ cocyclesMap g ψ n
参数：f : H ->* K；g : G ->* H；φ : res f A ⟶ B；ψ : res g B ⟶ C；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cocyclesMap_comp {G H K : Type u} [Group G] [Group H]
    [Group K] {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : res f A ⟶ B) (ψ : res g B ⟶ C) (n : ℕ) :
    cocyclesMap (f.comp g) ((resFunctor g).map φ ≫ ψ) n =
      cocyclesMap f φ n ≫ cocyclesMap g ψ n := by
  simp [cocyclesMap, ← HomologicalComplex.cyclesMap_comp, ← cochainsMap_comp]

@[reassoc]
/-
**groupCohomology.cocyclesMap_id_comp** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology
`。
形式化陈述：cocyclesMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : Nat) : 
cocyclesMap (MonoidHom.id G) (φ ≫ ψ) n = cocyclesMap (MonoidHom.id G) φ n ≫ cocy
clesMap (MonoidHom.id G) ψ n
参数：φ : A ⟶ B；ψ : B ⟶ C；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `groupCohomology.cochainsMap_id_comp`：cochainsMap_id_comp {A B C : Rep k 
G} (φ : A ⟶ B) (ψ : B ⟶ C) : cochainsMap (MonoidHom.id G) (φ ≫ ψ) = cochainsMap 
(MonoidHom.id G) φ ≫ coch…
· 使用引理 `HomologicalComplex.cyclesMap_comp`：cyclesMap_comp : cyclesMap (φ ≫ ψ) i 
= cyclesMap φ i ≫ cyclesMap ψ i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cocyclesMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    cocyclesMap (MonoidHom.id G) (φ ≫ ψ) n =
      cocyclesMap (MonoidHom.id G) φ n ≫ cocyclesMap (MonoidHom.id G) ψ n := by
  simp [cocyclesMap, cochainsMap_id_comp, HomologicalComplex.cyclesMap_comp]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map `Hⁿ(H, A) ⟶ Hⁿ(G, B)` sending `x : Hⁿ → A` to
`(g : Gⁿ) ↦ φ (x (f ∘ g))`. -/
/-
**groupCohomology.map** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomology`。
形式化陈述：map (n : Nat) : groupCohomology A n ⟶ groupCohomology B n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f
)(A) ⟶ B`,
this is the induced map `Hⁿ(H, A) ⟶ Hⁿ(G, B)` sending `x : Hⁿ → A` to
`(g : Gⁿ) ↦ φ (x (f ∘ g))`.
-/
noncomputable abbrev map (n : ℕ) :
    groupCohomology A n ⟶ groupCohomology B n :=
  HomologicalComplex.homologyMap (cochainsMap f φ) n
/-
**groupCohomology.map_congr** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
形式化陈述：map_congr {f g : G ->* H} {φ : res f A ⟶ B} {ψ : res g A ⟶ B} (hfg : f = g
) (hφψ : φ.hom.toLinearMap = ψ.hom.toLinearMap) (n : Nat) : map f φ n = map g ψ 
n
参数：hfg : f = g；hφψ : φ.hom.toLinearMap = ψ.hom.toLinearMap；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : M
onoid G] {A B : Rep.{w, u, v} k G} {f g : A ⟶ B},   Rep.Hom.hom f = Rep.Hom.hom 
g…
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_congr {f g : G →* H} {φ : res f A ⟶ B} {ψ : res g A ⟶ B} (hfg : f = g)
    (hφψ : φ.hom.toLinearMap = ψ.hom.toLinearMap) (n : ℕ) :
    map f φ n = map g ψ n := by
  subst hfg; congr; ext; simp [hφψ]

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
/-
**groupCohomology.** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_map (n : ℕ) :
    π A n ≫ map f φ n = cocyclesMap f φ n ≫ π B n := by
  simp [map, cocyclesMap]

@[simp]
/-
**groupCohomology.map_id** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
形式化陈述：map_id : map (MonoidHom.id G) (𝟙 B) n = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.homologyMap_id`：homologyMap_id : homologyMap (𝟙 K) i 
= 𝟙 _
-/
lemma map_id : map (MonoidHom.id G) (𝟙 B) n = 𝟙 _ := HomologicalComplex.homologyMap_id _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**groupCohomology.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
形式化陈述：map_comp {G H K : Type u} [Group G] [Group H] [Group K] {A : Rep k K} {B :
 Rep k H} {C : Rep k G} (f : H ->* K) (g : G ->* H) (φ : res f A ⟶ B) (ψ : res g
 B ⟶ C) (n : Nat) : map (f.comp g) ((resFunctor g).map φ ≫ ψ) n = map f φ n ≫ ma
p g ψ n
参数：f : H ->* K；g : G ->* H；φ : res f A ⟶ B；ψ : res g B ⟶ C；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp {G H K : Type u} [Group G] [Group H]
    [Group K] {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : res f A ⟶ B) (ψ : res g B ⟶ C) (n : ℕ) :
    map (f.comp g) ((resFunctor g).map φ ≫ ψ) n = map f φ n ≫ map g ψ n := by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← cochainsMap_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**groupCohomology.map_id_comp** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
形式化陈述：map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : Nat) : map (Mon
oidHom.id G) (φ ≫ ψ) n = map (MonoidHom.id G) φ n ≫ map (MonoidHom.id G) ψ n
参数：φ : A ⟶ B；ψ : B ⟶ C；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `groupCohomology.map.eq_1`：∀ {k G H : Type u} [inst : CommRing k] [inst_1
 : Group G] [inst_2 : Group H] {A : Rep.{u, u, u} k H}   {B : Rep.{u, u, u} k G}
 (f : G →* H) …
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `groupCohomology.cochainsMap_id_comp`：cochainsMap_id_comp {A B C : Rep k 
G} (φ : A ⟶ B) (ψ : B ⟶ C) : cochainsMap (MonoidHom.id G) (φ ≫ ψ) = cochainsMap 
(MonoidHom.id G) φ ≫ coch…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用引理 `HomologicalComplex.homologyMap_comp`：homologyMap_comp : homologyMap (φ ≫
 ψ) i = homologyMap φ i ≫ homologyMap ψ i
-/
theorem map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    map (MonoidHom.id G) (φ ≫ ψ) n =
      map (MonoidHom.id G) φ n ≫ map (MonoidHom.id G) ψ n := by
  rw [map, cochainsMap_id_comp, HomologicalComplex.homologyMap_comp]

/-- The isomorphism between cohomology groups induced by a group isomorphism `e : G ≃* H` and a
isomorphism between representations (restricted by `e`). -/
@[simps]
/-
**groupCohomology.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `groupCohomology`。
形式化陈述：mapIso (e : G ≃* H) (e' : B.V ≃ₗ[k] A.V) (he : forall g, e' ∘ₗ B.ρ g = A.ρ
 (e g) ∘ₗ e') (n : Nat) : groupCohomology B n ≅ groupCohomology A n where hom
参数：e : G ≃* H；e' : B.V ≃ₗ[k] A.V；he : forall g, e' ∘ₗ B.ρ g = A.ρ (e g) ∘ₗ e'；n 
: Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between cohomology groups induced by a group isomorphism `e : G 
≃* H` and a
isomorphism between representations (restricted by `e`).
-/
noncomputable def mapIso (e : G ≃* H) (e' : B.V ≃ₗ[k] A.V)
    (he : ∀ g, e' ∘ₗ B.ρ g = A.ρ (e g) ∘ₗ e') (n : ℕ) :
    groupCohomology B n ≅ groupCohomology A n where
  hom := groupCohomology.map e.symm (ofHom ⟨e', fun h ↦ by simp [he]⟩) n
  inv := groupCohomology.map e (ofHom ⟨e'.symm, fun g ↦ by
    rw [e'.toLinearMap_symm_comp_eq, ← LinearMap.comp_assoc]
    simp [he, LinearMap.comp_assoc]⟩) n
  hom_inv_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    exact map_congr (by simp) (by simp [res_id]) n
  inv_hom_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    exact groupCohomology.map_congr (by simp) e'.comp_symm n

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map sending `x : H → A` to `(g : G) ↦ φ (x (f g))`. -/
/-
**groupCohomology.cochainsMap** 是 Mathlib 中的一个定义，位于命名空间 `groupCohomology`。
形式化陈述：cochainsMap : inhomogeneousCochains A ⟶ inhomogeneousCochains B where f i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f
)(A) ⟶ B`,
this is the induced map sending `x : H → A` to `(g : G) ↦ φ (x (f g))`.
-/
noncomputable abbrev cochainsMap₁ :
    ModuleCat.of k (H → A) ⟶ ModuleCat.of k (G → B) :=
  ModuleCat.ofHom <| φ.hom.toLinearMap.compLeft G ∘ₗ LinearMap.funLeft k A f

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map sending `x : H × H → A` to `(g₁, g₂ : G × G) ↦ φ (x (f g₁, f g₂))`. -/
/-
**groupCohomology.cochainsMap** 是 Mathlib 中的一个定义，位于命名空间 `groupCohomology`。
形式化陈述：cochainsMap : inhomogeneousCochains A ⟶ inhomogeneousCochains B where f i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f
)(A) ⟶ B`,
this is the induced map sending `x : H × H → A` to `(g₁, g₂ : G × G) ↦ φ (x (f g
₁, f g₂))`.
-/
noncomputable abbrev cochainsMap₂ :
    ModuleCat.of k (H × H → A) ⟶ ModuleCat.of k (G × G → B) :=
  ModuleCat.ofHom <| φ.hom.toLinearMap.compLeft (G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f f)

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map sending `x : H × H × H → A` to
`(g₁, g₂, g₃ : G × G × G) ↦ φ (x (f g₁, f g₂, f g₃))`. -/
/-
**groupCohomology.cochainsMap** 是 Mathlib 中的一个定义，位于命名空间 `groupCohomology`。
形式化陈述：cochainsMap : inhomogeneousCochains A ⟶ inhomogeneousCochains B where f i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f
)(A) ⟶ B`,
this is the induced map sending `x : H × H × H → A` to
`(g₁, g₂, g₃ : G × G × G) ↦ φ (x (f g₁, f g₂, f g₃))`.
-/
noncomputable abbrev cochainsMap₃ :
    ModuleCat.of k (H × H × H → A) ⟶ ModuleCat.of k (G × G × G → B) :=
  ModuleCat.ofHom <|
    φ.hom.toLinearMap.compLeft (G × G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f (Prod.map f f))

@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**groupCohomology.cochainsMap_f_0_comp_cochainsIso** 是 Mathlib 中的一个引理，位于命名空间 `gr
oupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cochainsMap_f_0_comp_cochainsIso₀ :
    (cochainsMap f φ).f 0 ≫ (cochainsIso₀ B).hom = (cochainsIso₀ A).hom ≫ φ.toModuleCatHom := by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**groupCohomology.cochainsMap_f_1_comp_cochainsIso** 是 Mathlib 中的一个引理，位于命名空间 `gr
oupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cochainsMap_f_1_comp_cochainsIso₁ :
    (cochainsMap f φ).f 1 ≫ (cochainsIso₁ B).hom = (cochainsIso₁ A).hom ≫ cochainsMap₁ f φ := rfl

@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**groupCohomology.cochainsMap_f_2_comp_cochainsIso** 是 Mathlib 中的一个引理，位于命名空间 `gr
oupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cochainsMap_f_2_comp_cochainsIso₂ :
    (cochainsMap f φ).f 2 ≫ (cochainsIso₂ B).hom = (cochainsIso₂ A).hom ≫ cochainsMap₂ f φ := by
  ext x g
  change φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**groupCohomology.cochainsMap_f_3_comp_cochainsIso** 是 Mathlib 中的一个引理，位于命名空间 `gr
oupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cochainsMap_f_3_comp_cochainsIso₃ :
    (cochainsMap f φ).f 3 ≫ (cochainsIso₃ B).hom = (cochainsIso₃ A).hom ≫ cochainsMap₃ f φ := by
  ext x g
  change φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

end

open ShortComplex

section H0

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**groupCohomology.map_H0Iso_hom_f** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
形式化陈述：map_H0Iso_hom_f : map f φ 0 ≫ (H0Iso B).hom ≫ (shortComplexH0 B).f = (H0Is
o A).hom ≫ (shortComplexH0 A).f ≫ φ.toModuleCatHom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `HomologicalComplex.instEpiHomologyπ`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.homologyπ_naturality_assoc`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {ι : Type u_2} {c : Com…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `groupCohomology.π_comp_H0Iso_hom_assoc`：∀ {k G : Type u} [inst : CommRin
g k] [inst_1 : Group G] (A : Rep.{u, u, u} k G) {Z : ModuleCat k}   (h : ModuleC
at.of k ↥A.ρ.invariants ⟶ Z)…
· 使用引理 `groupCohomology.cocyclesIso₀_hom_comp_f`：cocyclesIso₀_hom_comp_f : (cocy
clesIso₀ A).hom ≫ (shortComplexH0 A).f = iCocycles A 0 ≫ (cochainsIso₀ A).hom
· 使用定理 `HomologicalComplex.cyclesMap_i_assoc`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
   {ι : Type u_2} {c : Com…
· 使用引理 `groupCohomology.cochainsMap_f_0_comp_cochainsIso₀`：cochainsMap_f_0_comp_
cochainsIso₀ : (cochainsMap f φ).f 0 ≫ (cochainsIso₀ B).hom = (cochainsIso₀ A).h
om ≫ φ.toModuleCatHom
· 使用定理 `groupCohomology.cocyclesIso₀_hom_comp_f_assoc`：∀ {k G : Type u} [inst : 
CommRing k] [inst_1 : Group G] (A : Rep.{u, u, u} k G) {Z : ModuleCat k}   (h : 
(groupCohomology.shortComplexH0 A).…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_H0Iso_hom_f :
    map f φ 0 ≫ (H0Iso B).hom ≫ (shortComplexH0 B).f =
      (H0Iso A).hom ≫ (shortComplexH0 A).f ≫ φ.toModuleCatHom := by
  simp [← cancel_epi (π _ _)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**groupCohomology.map_id_comp_H0Iso_hom** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomolo
gy`。
形式化陈述：map_id_comp_H0Iso_hom {A B : Rep k G} (f : A ⟶ B) : map (MonoidHom.id G) f
 0 ≫ (H0Iso B).hom = (H0Iso A).hom ≫ (invariantsFunctor k G).map f
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `groupCohomology.instMonoModuleCatFShortComplexH0`：∀ {k G : Type u} [inst
 : CommRing k] [inst_1 : Group G] (A : Rep.{max u u_1, u, u} k G),   CategoryThe
ory.Mono (groupCohomology.shortComplex…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `groupCohomology.map_H0Iso_hom_f`：map_H0Iso_hom_f : map f φ 0 ≫ (H0Iso B)
.hom ≫ (shortComplexH0 B).f = (H0Iso A).hom ≫ (shortComplexH0 A).f ≫ φ.toModuleC
atHom
-/
theorem map_id_comp_H0Iso_hom {A B : Rep k G} (f : A ⟶ B) :
    map (MonoidHom.id G) f 0 ≫ (H0Iso B).hom = (H0Iso A).hom ≫ (invariantsFunctor k G).map f := by
  simp only [← cancel_mono (shortComplexH0 B).f, Category.assoc, map_H0Iso_hom_f]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**groupCohomology.mono_map_0_of_mono** 是 Mathlib 中的一个实例，位于命名空间 `groupCohomology`
。
形式化陈述：mono_map_0_of_mono {A B : Rep k G} (f : A ⟶ B) [Mono f] : Mono (map (Monoi
dHom.id G) f 0) where right_cancellation g h hgh
参数：f : A ⟶ B。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `Rep.instIsRightAdjointModuleCatInvariantsFunctor`：∀ (k : Type u) (G : Ty
pe v) [inst : CommRing k] [inst_1 : Group G], (Rep.invariantsFunctor k G).IsRigh
tAdjoint
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `groupCohomology.map_id_comp_H0Iso_hom`：map_id_comp_H0Iso_hom {A B : Rep 
k G} (f : A ⟶ B) : map (MonoidHom.id G) f 0 ≫ (H0Iso B).hom = (H0Iso A).hom ≫ (i
nvariantsFunctor k G).map f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance mono_map_0_of_mono {A B : Rep k G} (f : A ⟶ B) [Mono f] :
    Mono (map (MonoidHom.id G) f 0) where
  right_cancellation g h hgh := by
    simp only [← cancel_mono (H0Iso B).hom, Category.assoc, map_id_comp_H0Iso_hom] at hgh
    simp_all [cancel_mono]

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
/-
**groupCohomology.cocyclesMap_cocyclesIso** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomo
logy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cocyclesMap_cocyclesIso₀_hom_f :
    cocyclesMap f φ 0 ≫ (cocyclesIso₀ B).hom ≫ (shortComplexH0 B).f =
      (cocyclesIso₀ A).hom ≫ (shortComplexH0 A).f ≫ φ.toModuleCatHom := by
  simp

end H0
section H1

set_option backward.isDefEq.respectTransparency false in
/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map from the short complex `A --d₀₁--> Fun(H, A) --d₁₂--> Fun(H × H, A)`
to `B --d₀₁--> Fun(G, B) --d₁₂--> Fun(G × G, B)`. -/
@[simps]
/-
**groupCohomology.mapShortComplexH1** 是 Mathlib 中的一个定义，位于命名空间 `groupCohomology`。
形式化陈述：mapShortComplexH1 : shortComplexH1 A ⟶ shortComplexH1 B where τ₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f
)(A) ⟶ B`,
this is the induced map from the short complex `A --d₀₁--> Fun(H, A) --d₁₂--> Fu
n(H × H, A)`
to `B --d₀₁--> Fun(G, B) --d₁₂--> Fun(G × G, B)`.
-/
noncomputable def mapShortComplexH1 :
    shortComplexH1 A ⟶ shortComplexH1 B where
  τ₁ := φ.toModuleCatHom
  τ₂ := cochainsMap₁ f φ
  τ₃ := cochainsMap₂ f φ
  comm₁₂ := by
    ext x
    funext g
    simpa [shortComplexH1, d₀₁, cochainsMap₁] using (hom_comm_apply φ g x).symm
  comm₂₃ := by
    ext x
    funext g
    simpa [shortComplexH1, d₁₂, cochainsMap₁, cochainsMap₂] using (hom_comm_apply φ _ _).symm

@[simp]
/-
**groupCohomology.mapShortComplexH1_zero** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomol
ogy`。
形式化陈述：mapShortComplexH1_zero : mapShortComplexH1 (A
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapShortComplexH1_zero :
    mapShortComplexH1 (A := A) (B := B) f 0 = 0 := by
  rfl

@[simp]
/-
**groupCohomology.mapShortComplexH1_id** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomolog
y`。
形式化陈述：mapShortComplexH1_id : mapShortComplexH1 (MonoidHom.id _) (𝟙 A) = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapShortComplexH1_id :
    mapShortComplexH1 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  rfl

@[reassoc]
/-
**groupCohomology.mapShortComplexH1_comp** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomol
ogy`。
形式化陈述：mapShortComplexH1_comp {G H K : Type u} [Group G] [Group H] [Group K] {A :
 Rep k K} {B : Rep k H} {C : Rep k G} (f : H ->* K) (g : G ->* H) (φ : res f A ⟶
 B) (ψ : res g B ⟶ C) : mapShortComplexH1 (f.comp g) ((resFunctor g).map φ ≫ ψ) 
= mapShortComplexH1 f φ ≫ mapShortComplexH1 g ψ
参数：f : H ->* K；g : G ->* H；φ : res f A ⟶ B；ψ : res g B ⟶ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapShortComplexH1_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : res f A ⟶ B) (ψ : res g B ⟶ C) :
    mapShortComplexH1 (f.comp g) ((resFunctor g).map φ ≫ ψ) =
      mapShortComplexH1 f φ ≫ mapShortComplexH1 g ψ := rfl

@[reassoc]
/-
**groupCohomology.mapShortComplexH1_id_comp** 是 Mathlib 中的一个定理，位于命名空间 `groupCoho
mology`。
形式化陈述：mapShortComplexH1_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) : mapS
hortComplexH1 (MonoidHom.id G) (φ ≫ ψ) = mapShortComplexH1 (MonoidHom.id G) φ ≫ 
mapShortComplexH1 (MonoidHom.id G) ψ
参数：φ : A ⟶ B；ψ : B ⟶ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapShortComplexH1_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH1 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH1 (MonoidHom.id G) φ ≫ mapShortComplexH1 (MonoidHom.id G) ψ := rfl

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `Z¹(H, A) ⟶ Z¹(G, B)`. -/
/-
**groupCohomology.mapCocycles** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f
)(A) ⟶ B`,
this is induced map `Z¹(H, A) ⟶ Z¹(G, B)`.
-/
noncomputable abbrev mapCocycles₁ :
    ModuleCat.of k (cocycles₁ A) ⟶ ModuleCat.of k (cocycles₁ B) :=
  ShortComplex.cyclesMap' (mapShortComplexH1 f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
/-
**groupCohomology.mapCocycles** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapCocycles₁_comp_i :
    mapCocycles₁ f φ ≫ (shortComplexH1 B).moduleCatLeftHomologyData.i =
      (shortComplexH1 A).moduleCatLeftHomologyData.i ≫ cochainsMap₁ f φ := by
  simp

@[simp]
/-
**groupCohomology.coe_mapCocycles** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mapCocycles₁ (x) :
    ⇑(mapCocycles₁ f φ x) = cochainsMap₁ f φ x := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**groupCohomology.cocyclesMap_comp_isoCocycles** 是 Mathlib 中的一个引理，位于命名空间 `groupC
ohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cocyclesMap_comp_isoCocycles₁_hom :
    cocyclesMap f φ 1 ≫ (isoCocycles₁ B).hom = (isoCocycles₁ A).hom ≫ mapCocycles₁.{u, u} f φ := by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**groupCohomology.mapCocycles** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapCocycles₁_one (φ : res 1 A ⟶ B) :
    mapCocycles₁ 1 φ = 0 := by
  rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i, cyclesMap'_i]
  refine ModuleCat.hom_ext (LinearMap.ext fun _ ↦ funext fun y => ?_)
  simp [mapShortComplexH1, shortComplexH1, Pi.zero_apply y]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**groupCohomology.H1** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomology`。
形式化陈述：H1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma H1π_comp_map :
    H1π A ≫ map f φ 1 = mapCocycles₁ f φ ≫ H1π B := by
  simp [H1π, Iso.inv_comp_eq, ← cocyclesMap_comp_isoCocycles₁_hom_assoc]

@[simp]
/-
**groupCohomology.map** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomology`。
形式化陈述：map (n : Nat) : groupCohomology A n ⟶ groupCohomology B n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₁_one (φ : res 1 A ⟶ B) :
    map 1 φ 1 = 0 := by
  simp [← cancel_epi (H1π _)]

section InfRes

variable (A : Rep k G) (S : Subgroup G) [S.Normal]

/-- The short complex `H¹(G ⧸ S, A^S) ⟶ H¹(G, A) ⟶ H¹(S, A)`. -/
@[simps X₁ X₂ X₃ f g]
/-
**groupCohomology.H1InfRes** 是 Mathlib 中的一个定义，位于命名空间 `groupCohomology`。
形式化陈述：H1InfRes : ShortComplex (ModuleCat k) where X₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex `H¹(G ⧸ S, A^S) ⟶ H¹(G, A) ⟶ H¹(S, A)`.
-/
noncomputable def H1InfRes :
    ShortComplex (ModuleCat k) where
  X₁ := groupCohomology (A.quotientToInvariants S) 1
  X₂ := groupCohomology A 1
  X₃ := groupCohomology (res S.subtype A) 1
  f := map (QuotientGroup.mk' S) (ofHom <| A.ρ.quotientToInvariants_lift S) 1
  g := map S.subtype (𝟙 _) 1
  zero := by rw [← map_comp, Category.comp_id, congr (QuotientGroup.mk'_comp_subtype S)
    (fun f φ => map f φ 1), map₁_one]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inflation map `H¹(G ⧸ S, A^S) ⟶ H¹(G, A)` is a monomorphism. -/
/-
**groupCohomology.** 是 Mathlib 中的一个实例，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inflation map `H¹(G ⧸ S, A^S) ⟶ H¹(G, A)` is a monomorphism.
-/
instance : Mono (H1InfRes A S).f := by
  rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro x hx
  induction x using H1_induction_on with | @h x =>
  simp_all only [H1InfRes_X₂, H1InfRes_X₁, H1InfRes_f, H1π_comp_map_apply (QuotientGroup.mk' S)]
  rcases (H1π_eq_zero_iff _).1 hx with ⟨y, hy⟩
  refine (H1π_eq_zero_iff _).2 ⟨⟨y, fun s => ?_⟩, funext fun g => QuotientGroup.induction_on g
    fun g => Subtype.ext <| by simpa [-SetLike.coe_eq_coe] using! congr_fun hy g⟩
  simpa [coe_mapCocycles₁ (x := x), sub_eq_zero, (QuotientGroup.eq_one_iff s.1).2 s.2] using!
    congr_fun hy s.1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a `G`-representation `A` and a normal subgroup `S ≤ G`, the short complex
`H¹(G ⧸ S, A^S) ⟶ H¹(G, A) ⟶ H¹(S, A)` is exact. -/
/-
**groupCohomology.H1InfRes_exact** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
形式化陈述：H1InfRes_exact : (H1InfRes A S).Exact
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.moduleCat_exact_iff_ker_sub_range`：moduleCat
_exact_iff_ker_sub_range : S.Exact ↔ LinearMap.ker S.g.hom <= LinearMap.range S.
f.hom
· 使用定理 `groupCohomology.H1_induction_on`：H1_induction_on {C : H1 A -> Prop} (x :
 H1 A) (h : forall x : cocycles₁ A, C (H1π A x)) : C x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `groupCohomology.H1π_eq_zero_iff`：H1π_eq_zero_iff (x : cocycles₁ A) : H1π
 A x = 0 ↔ ⇑x in coboundaries₁ A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `groupCohomology.H1π_comp_map_apply`：∀ {k G H : Type u} [inst : CommRing 
k] [inst_1 : Group G] [inst_2 : Group H] {A : Rep.{u, u, u} k H}   {B : Rep.{u, 
u, u} k G} (f : G →* H) …
· 使用定理 `groupCohomology.mem_cocycles₁_iff`：mem_cocycles₁_iff (f : G -> A) : f in
 cocycles₁ A ↔ forall g h : G, f (g * h) = A.ρ g (f h) + f g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_eq_of_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a = 
c + b → a - b = c
· 使用定理 `add_eq_of_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a = 
c - b → a + b = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Representation.self_inv_apply`：self_inv_apply (g : G) (x : V) : ρ g (ρ g
⁻¹ x) = x
· 使用定理 `_private.Mathlib.RepresentationTheory.Homological.GroupCohomology.Functo
riality.0.groupCohomology.H1InfRes_exact._abel_1_2`：∀ {k G : Type u_1} [inst : C
ommRing k] [inst_1 : Group G] (A : Rep.{u_1, u_1, u_1} k G) (S : Subgroup G)   (
x : ↥(groupCohomology.cocycles₁ …
· 使用定理 `eq_sub_of_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G},
 c + a = b → a = b - c
· 使用定理 `Subgroup.Normal.conj_mem'`：conj_mem' (nH : H.Normal) (n : G) (hn : n in 
H) (g : G) : g⁻¹ * n * g in H
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
Given a `G`-representation `A` and a normal subgroup `S ≤ G`, the short complex
`H¹(G ⧸ S, A^S) ⟶ H¹(G, A) ⟶ H¹(S, A)` is exact.
-/
lemma H1InfRes_exact : (H1InfRes A S).Exact := by
  rw [moduleCat_exact_iff_ker_sub_range]
  intro x hx
  induction x using H1_induction_on with | @h x =>
  simp_all only [H1InfRes_X₂, H1InfRes_X₃, H1InfRes_g, H1InfRes_X₁, LinearMap.mem_ker,
    H1π_comp_map_apply S.subtype, H1InfRes_f]
  rcases (H1π_eq_zero_iff _).1 hx with ⟨(y : A), hy⟩
  have h1 := (mem_cocycles₁_iff x).1 x.2
  have h2 : ∀ s ∈ S, x s = A.ρ s y - y :=
    fun s hs => funext_iff.1 hy.symm ⟨s, hs⟩
  refine ⟨H1π _ ⟨fun g => Quotient.liftOn' g (fun g => ⟨x.1 g - A.ρ g y + y, ?_⟩) ?_, ?_⟩, ?_⟩
  · intro s
    calc
      _ = x (s * g) - x s - A.ρ s (A.ρ g y) + (x s + y) := by
        simp [add_eq_of_eq_sub (h2 s s.2), sub_eq_of_eq_add (h1 s g)]
      _ = x (g * (g⁻¹ * s * g)) - A.ρ g (A.ρ (g⁻¹ * s * g) y - y) - A.ρ g y + y := by
        simp only [mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply, map_sub,
          Representation.self_inv_apply]
        abel
      _ = x g - A.ρ g y + y := by
        simp [eq_sub_of_add_eq' (h1 g (g⁻¹ * s * g)).symm,
          h2 (g⁻¹ * s * g) (Subgroup.Normal.conj_mem' ‹_› _ s.2 _)]
  · intro g h hgh
    have := congr(A.ρ g $(h2 (g⁻¹ * h) <| QuotientGroup.leftRel_apply.1 hgh))
    simp_all [← sub_eq_add_neg, sub_eq_sub_iff_sub_eq_sub]
  · rw [mem_cocycles₁_iff]
    intro g h
    induction g using QuotientGroup.induction_on with | @H g =>
    induction h using QuotientGroup.induction_on with | @H h =>
    apply Subtype.ext
    simp [← QuotientGroup.mk_mul, h1 g h, sub_add_eq_add_sub, add_assoc]
  · symm
    simp only [H1π_comp_map_apply, H1π_eq_iff (A := A)]
    use y
    ext g
    simp [coe_mapCocycles₁ (QuotientGroup.mk' S),
      cocycles₁.coe_mk (A := A.quotientToInvariants S), ← sub_sub]

end InfRes
end H1
section H2

set_option backward.isDefEq.respectTransparency false in
/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map from the short complex
`Fun(H, A) --d₁₂--> Fun(H × H, A) --d₂₃--> Fun(H × H × H, A)` to
`Fun(G, B) --d₁₂--> Fun(G × G, B) --d₂₃--> Fun(G × G × G, B)`. -/
@[simps]
/-
**groupCohomology.mapShortComplexH2** 是 Mathlib 中的一个定义，位于命名空间 `groupCohomology`。
形式化陈述：mapShortComplexH2 : shortComplexH2 A ⟶ shortComplexH2 B where τ₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f
)(A) ⟶ B`,
this is the induced map from the short complex
`Fun(H, A) --d₁₂--> Fun(H × H, A) --d₂₃--> Fun(H × H × H, A)` to
`Fun(G, B) --d₁₂--> Fun(G × G, B) --d₂₃--> Fun(G × G × G, B)`.
-/
noncomputable def mapShortComplexH2 :
    shortComplexH2 A ⟶ shortComplexH2 B where
  τ₁ := cochainsMap₁ f φ
  τ₂ := cochainsMap₂ f φ
  τ₃ := cochainsMap₃ f φ
  comm₁₂ := by
    ext x
    funext g
    simp [shortComplexH2, ← hom_comm_apply φ]
  comm₂₃ := by
    ext x
    funext g
    simp [shortComplexH2, ← hom_comm_apply φ]

@[simp]
/-
**groupCohomology.mapShortComplexH2_zero** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomol
ogy`。
形式化陈述：mapShortComplexH2_zero : mapShortComplexH2 (A
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapShortComplexH2_zero :
    mapShortComplexH2 (A := A) (B := B) f 0 = 0 := rfl

@[simp]
/-
**groupCohomology.mapShortComplexH2_id** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomolog
y`。
形式化陈述：mapShortComplexH2_id : mapShortComplexH2 (MonoidHom.id _) (𝟙 A) = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapShortComplexH2_id :
    mapShortComplexH2 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  rfl

@[reassoc]
/-
**groupCohomology.mapShortComplexH2_comp** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomol
ogy`。
形式化陈述：mapShortComplexH2_comp {G H K : Type u} [Group G] [Group H] [Group K] {A :
 Rep k K} {B : Rep k H} {C : Rep k G} (f : H ->* K) (g : G ->* H) (φ : res f A ⟶
 B) (ψ : res g B ⟶ C) : mapShortComplexH2 (f.comp g) ((resFunctor g).map φ ≫ ψ) 
= mapShortComplexH2 f φ ≫ mapShortComplexH2 g ψ
参数：f : H ->* K；g : G ->* H；φ : res f A ⟶ B；ψ : res g B ⟶ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapShortComplexH2_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : res f A ⟶ B) (ψ : res g B ⟶ C) :
    mapShortComplexH2 (f.comp g) ((resFunctor g).map φ ≫ ψ) =
      mapShortComplexH2 f φ ≫ mapShortComplexH2 g ψ := rfl

@[reassoc]
/-
**groupCohomology.mapShortComplexH2_id_comp** 是 Mathlib 中的一个定理，位于命名空间 `groupCoho
mology`。
形式化陈述：mapShortComplexH2_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) : mapS
hortComplexH2 (MonoidHom.id G) (φ ≫ ψ) = mapShortComplexH2 (MonoidHom.id G) φ ≫ 
mapShortComplexH2 (MonoidHom.id G) ψ
参数：φ : A ⟶ B；ψ : B ⟶ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapShortComplexH2_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH2 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH2 (MonoidHom.id G) φ ≫ mapShortComplexH2 (MonoidHom.id G) ψ := rfl

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `Z²(H, A) ⟶ Z²(G, B)`. -/
/-
**groupCohomology.mapCocycles** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f
)(A) ⟶ B`,
this is induced map `Z²(H, A) ⟶ Z²(G, B)`.
-/
noncomputable abbrev mapCocycles₂ :
    ModuleCat.of k (cocycles₂ A) ⟶ ModuleCat.of k (cocycles₂ B) :=
  ShortComplex.cyclesMap' (mapShortComplexH2 f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
/-
**groupCohomology.mapCocycles** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapCocycles₂_comp_i :
    mapCocycles₂ f φ ≫ (shortComplexH2 B).moduleCatLeftHomologyData.i =
      (shortComplexH2 A).moduleCatLeftHomologyData.i ≫ cochainsMap₂ f φ := by
  simp

@[simp]
/-
**groupCohomology.coe_mapCocycles** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mapCocycles₂ (x) :
    ⇑(mapCocycles₂ f φ x) = cochainsMap₂ f φ x := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**groupCohomology.cocyclesMap_comp_isoCocycles** 是 Mathlib 中的一个引理，位于命名空间 `groupC
ohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cocyclesMap_comp_isoCocycles₂_hom :
    cocyclesMap f φ 2 ≫ (isoCocycles₂ B).hom = (isoCocycles₂ A).hom ≫ mapCocycles₂ f φ := by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapShortComplexH2,
    cochainsMap_f_2_comp_cochainsIso₂ f]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**groupCohomology.H2** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomology`。
形式化陈述：H2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma H2π_comp_map :
    H2π A ≫ map f φ 2 = mapCocycles₂ f φ ≫ H2π B := by
  simp [H2π, Iso.inv_comp_eq, ← cocyclesMap_comp_isoCocycles₂_hom_assoc]

end H2

variable (k G)

/-- The functor sending a representation to its complex of inhomogeneous cochains. -/
@[simps]
/-
**groupCohomology.cochainsFunctor** 是 Mathlib 中的一个定义，位于命名空间 `groupCohomology`。
形式化陈述：cochainsFunctor : Rep k G ⥤ CochainComplex (ModuleCat k) Nat where obj A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `groupCohomology.cochainsMap_id`：cochainsMap_id : cochainsMap (MonoidHom.
id _) (𝟙 A) = 𝟙 (inhomogeneousCochains A)

--- 原说明 ---
The functor sending a representation to its complex of inhomogeneous cochains.
-/
noncomputable def cochainsFunctor : Rep k G ⥤ CochainComplex (ModuleCat k) ℕ where
  obj A := inhomogeneousCochains A
  map f := cochainsMap (MonoidHom.id _) f
  map_id _ := cochainsMap_id
  map_comp φ ψ := cochainsMap_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ
/-
**groupCohomology.** 是 Mathlib 中的一个实例，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (cochainsFunctor k G).PreservesZeroMorphisms where
/-
**groupCohomology.** 是 Mathlib 中的一个实例，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (cochainsFunctor k G).Additive where

set_option backward.isDefEq.respectTransparency false in
/-- The functor sending a `G`-representation `A` to `Hⁿ(G, A)`. -/
@[simps]
/-
**groupCohomology.functor** 是 Mathlib 中的一个定义，位于命名空间 `groupCohomology`。
形式化陈述：functor (n : Nat) : Rep k G ⥤ ModuleCat k where obj A
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor sending a `G`-representation `A` to `Hⁿ(G, A)`.
-/
noncomputable def functor (n : ℕ) : Rep k G ⥤ ModuleCat k where
  obj A := groupCohomology A n
  map φ := map (MonoidHom.id _) φ n
  map_id _ := HomologicalComplex.homologyMap_id _ _
  map_comp _ _ := by
    simp only [← HomologicalComplex.homologyMap_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-
**groupCohomology.** 是 Mathlib 中的一个实例，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : (functor k G n).PreservesZeroMorphisms where
  map_zero _ _ := by simp [map]

variable {G}

set_option backward.isDefEq.respectTransparency false in
/-- Given a group homomorphism `f : G →* H`, this is a natural transformation between the functors
sending `A : Rep k H` to `Hⁿ(H, A)` and to `Hⁿ(G, Res(f)(A))`. -/
@[simps]
/-
**groupCohomology.resNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `groupCohomology`。
形式化陈述：resNatTrans (n : Nat) : functor k H n ⟶ resFunctor f ⋙ functor k G n where
 app X
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `f : G →* H`, this is a natural transformation betwee
n the functors
sending `A : Rep k H` to `Hⁿ(H, A)` and to `Hⁿ(G, Res(f)(A))`.
-/
noncomputable def resNatTrans (n : ℕ) :
    functor k H n ⟶ resFunctor f ⋙ functor k G n where
  app X := map f (𝟙 _) n
  naturality {X Y} φ := by
    simp only [functor_map, Functor.comp_map,
      ← cancel_epi (groupCohomology.π _ n), HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_naturality, ← HomologicalComplex.cyclesMap_comp_assoc,
      ← cochainsMap_comp, res_obj_ρ, Category.comp_id]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Given a normal subgroup `S ≤ G`, this is a natural transformation between the functors
sending `A : Rep k G` to `Hⁿ(G ⧸ S, A^S)` and to `Hⁿ(G, A)`. -/
@[simps]
/-
**groupCohomology.infNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `groupCohomology`。
形式化陈述：infNatTrans (S : Subgroup G) [S.Normal] (n : Nat) : quotientToInvariantsFu
nctor k S ⋙ functor k (G ⧸ S) n ⟶ functor k G n where app A
参数：S : Subgroup G；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a normal subgroup `S ≤ G`, this is a natural transformation between the fu
nctors
sending `A : Rep k G` to `Hⁿ(G ⧸ S, A^S)` and to `Hⁿ(G, A)`.
-/
noncomputable def infNatTrans (S : Subgroup G) [S.Normal] (n : ℕ) :
    quotientToInvariantsFunctor k S ⋙ functor k (G ⧸ S) n ⟶ functor k G n where
  app A := map (QuotientGroup.mk' S) (ofHom <| A.ρ.quotientToInvariants_lift S) n
  naturality {X Y} φ := by
    simp only [Functor.comp_map, functor_map, ← cancel_epi (groupCohomology.π _ n),
      HomologicalComplex.homologyπ_naturality_assoc, HomologicalComplex.homologyπ_naturality,
      ← HomologicalComplex.cyclesMap_comp_assoc, ← cochainsMap_comp]
    congr 1

end groupCohomology

