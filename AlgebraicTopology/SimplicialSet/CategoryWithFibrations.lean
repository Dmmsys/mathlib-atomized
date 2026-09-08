/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Cofibrations and fibrations in the category of simplicial sets

We endow `SSet` with `CategoryWithCofibrations` and `CategoryWithFibrations`
instances. Cofibrations are monomorphisms, and fibrations are morphisms
having the right lifting property with respect to horn inclusions.

We have an instance `mono_of_cofibration` (but only a lemma `cofibration_of_mono`).
Then, when stating lemmas about cofibrations of simplicial sets, it is advisable
to use the assumption `[Mono f]` instead of `[Cofibration f]`.

-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra MorphismProperty Simplicial

universe u

namespace SSet

namespace modelCategoryQuillen

/-- The generating cofibrations: this is the family of morphisms in `SSet`
which consists of boundary inclusions `∂Δ[n].ι : ∂Δ[n] ⟶ Δ[n]`. -/
/-
**SSet.modelCategoryQuillen.I** 是 Mathlib 中的一个定义，位于命名空间 `SSet.modelCategoryQuill
en`。
形式化陈述：I : MorphismProperty SSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The generating cofibrations: this is the family of morphisms in `SSet`
which consists of boundary inclusions `∂Δ[n].ι : ∂Δ[n] ⟶ Δ[n]`.
-/
def I : MorphismProperty SSet.{u} :=
  .ofHoms (fun n ↦ ∂Δ[n].ι)
/-
**SSet.modelCategoryQuillen.boundary_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.modelCateg
oryQuillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma boundary_ι_mem_I (n : ℕ) :
    I (boundary.{u} n).ι := by constructor

/-- The generating trivial cofibrations: this is the family of morphisms in `SSet`
which consists of horn inclusions `Λ[n, i].ι : Λ[n, i] ⟶ Δ[n]` (for positive `n`). -/
/-
**SSet.modelCategoryQuillen.J** 是 Mathlib 中的一个定义，位于命名空间 `SSet.modelCategoryQuill
en`。
形式化陈述：J : MorphismProperty SSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The generating trivial cofibrations: this is the family of morphisms in `SSet`
which consists of horn inclusions `Λ[n, i].ι : Λ[n, i] ⟶ Δ[n]` (for positive `n`
).
-/
def J : MorphismProperty SSet.{u} :=
  ⨆ n, .ofHoms (fun (i : Fin (n + 2)) ↦ Λ[n + 1, i].ι)
/-
**SSet.modelCategoryQuillen.horn_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.modelCategoryQ
uillen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma horn_ι_mem_J (n : ℕ) [NeZero n] (i : Fin (n + 1)) :
    J (horn.{u} n i).ι := by
  obtain _ | n := n
  · exact (NeZero.ne 0 rfl).elim
  · simp only [J, iSup_iff]
    exact ⟨n, ⟨i⟩⟩
/-
**SSet.modelCategoryQuillen.I_le_monomorphisms** 是 Mathlib 中的一个引理，位于命名空间 `SSet.m
odelCategoryQuillen`。
形式化陈述：I_le_monomorphisms : I.{u} <= monomorphisms _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.monomorphisms.infer_property`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [hf : Categ
oryTheory.Mono f],   CategoryTheory.MorphismProper…
· 使用定理 `SSet.Subcomplex.instMonoι`：∀ {X : _root_.SSet} (A : X.Subcomplex), Categ
oryTheory.Mono A.ι
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma I_le_monomorphisms : I.{u} ≤ monomorphisms _ := by
  rintro _ _ _ ⟨n⟩
  exact monomorphisms.infer_property _
/-
**SSet.modelCategoryQuillen.J_le_monomorphisms** 是 Mathlib 中的一个引理，位于命名空间 `SSet.m
odelCategoryQuillen`。
形式化陈述：J_le_monomorphisms : J.{u} <= monomorphisms _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.monomorphisms.infer_property`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [hf : Categ
oryTheory.Mono f],   CategoryTheory.MorphismProper…
· 使用定理 `SSet.Subcomplex.instMonoι`：∀ {X : _root_.SSet} (A : X.Subcomplex), Categ
oryTheory.Mono A.ι
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma J_le_monomorphisms : J.{u} ≤ monomorphisms _ := by
  rintro _ _ _ h
  simp only [J, iSup_iff] at h
  obtain ⟨n, ⟨i⟩⟩ := h
  exact monomorphisms.infer_property _

/-- The cofibrations for the Quillen model category structure (TODO)
on `SSet` are monomorphisms. -/
/-
**SSet.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.modelCategoryQuille
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofibrations for the Quillen model category structure (TODO)
on `SSet` are monomorphisms.
-/
scoped instance : CategoryWithCofibrations SSet.{u} where
  cofibrations := .monomorphisms _

/-- The fibrations for the Quillen model category structure (TODO)
on `SSet` are the morphisms which have the right lifting property
with respect to horn inclusions. -/
/-
**SSet.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.modelCategoryQuille
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fibrations for the Quillen model category structure (TODO)
on `SSet` are the morphisms which have the right lifting property
with respect to horn inclusions.
-/
scoped instance : CategoryWithFibrations SSet.{u} where
  fibrations := J.rlp
/-
**SSet.modelCategoryQuillen.cofibrations_eq** 是 Mathlib 中的一个引理，位于命名空间 `SSet.mode
lCategoryQuillen`。
形式化陈述：cofibrations_eq : cofibrations SSet.{u} = monomorphisms _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cofibrations_eq : cofibrations SSet.{u} = monomorphisms _ := rfl
/-
**SSet.modelCategoryQuillen.fibrations_eq** 是 Mathlib 中的一个引理，位于命名空间 `SSet.modelC
ategoryQuillen`。
形式化陈述：fibrations_eq : fibrations SSet.{u} = J.rlp
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fibrations_eq : fibrations SSet.{u} = J.rlp := rfl

section

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/-
**SSet.modelCategoryQuillen.cofibration_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.mode
lCategoryQuillen`。
形式化陈述：cofibration_iff : Cofibration f ↔ Mono f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomotopicalAlgebra.cofibration_iff`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Catego
ryWithCofibrations C],  …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma cofibration_iff : Cofibration f ↔ Mono f := by
  rw [HomotopicalAlgebra.cofibration_iff]
  rfl
/-
**SSet.modelCategoryQuillen.fibration_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.modelC
ategoryQuillen`。
形式化陈述：fibration_iff : Fibration f ↔ J.rlp f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomotopicalAlgebra.fibration_iff`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Category
WithFibrations C],   H…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma fibration_iff : Fibration f ↔ J.rlp f := by
  rw [HomotopicalAlgebra.fibration_iff]
  rfl
/-
**SSet.modelCategoryQuillen.mono_of_cofibration** 是 Mathlib 中的一个实例，位于命名空间 `SSet.
modelCategoryQuillen`。
形式化陈述：mono_of_cofibration [Cofibration f] : Mono f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.modelCategoryQuillen.cofibration_iff`：cofibration_iff : Cofibration
 f ↔ Mono f
-/
instance mono_of_cofibration [Cofibration f] : Mono f := by rwa [← cofibration_iff]
/-
**SSet.modelCategoryQuillen.cofibration_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `SSet.
modelCategoryQuillen`。
形式化陈述：cofibration_of_mono [Mono f] : Cofibration f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.modelCategoryQuillen.cofibration_iff`：cofibration_iff : Cofibration
 f ↔ Mono f
-/
lemma cofibration_of_mono [Mono f] : Cofibration f := by rwa [cofibration_iff]
/-
**SSet.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.modelCategoryQuille
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hf : Fibration f] {n : ℕ} (i : Fin (n + 2)) :
    HasLiftingProperty (horn (n + 1) i).ι f := by
  rw [fibration_iff] at hf
  exact hf _ (horn_ι_mem_J _ _)
/-
**SSet.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.modelCategoryQuille
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (fibrations SSet.{u}).IsMultiplicative := by
  rw [fibrations_eq]
  infer_instance
/-
**SSet.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.modelCategoryQuille
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (fibrations SSet.{u}).IsStableUnderRetracts := by
  rw [fibrations_eq]
  infer_instance
/-
**SSet.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.modelCategoryQuille
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (cofibrations SSet.{u}).IsMultiplicative := by
  rw [cofibrations_eq]
  infer_instance
/-
**SSet.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.modelCategoryQuille
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (cofibrations SSet.{u}).IsStableUnderRetracts := by
  rw [cofibrations_eq]
  infer_instance
/-
**SSet.modelCategoryQuillen.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.modelCategoryQuille
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] : Fibration f := by
  rw [fibration_iff]
  apply rlp_of_isIso

end

end modelCategoryQuillen

open modelCategoryQuillen in
/-
**SSet.rlp_monomorphisms** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：rlp_monomorphisms : (MorphismProperty.monomorphisms SSet.{u}).rlp = I.rlp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.MorphismProperty.antitone_rlp`：antitone_rlp : Antitone (r
lp : MorphismProperty C -> _)
· 使用引理 `SSet.modelCategoryQuillen.I_le_monomorphisms`：I_le_monomorphisms : I.{u}
 <= monomorphisms _
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_pushouts_
coproducts_le_llp_rlp`：transfiniteCompositionsOfShape_pushouts_coproducts_le_llp
_rlp : (coproducts.{t} W).pushouts.transfiniteCompositionsOfShape J <= W.rlp.llp
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
-/
lemma rlp_monomorphisms :
    (MorphismProperty.monomorphisms SSet.{u}).rlp = I.rlp :=
  le_antisymm (antitone_rlp I_le_monomorphisms)
    (fun _ _ _ hp _ _ i _ ↦
      transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp.{u} I ℕ i
        ⟨(relativeCellComplexOfMono i).transfiniteCompositionOfShape' (fun _ ↦ ⟨_⟩)⟩  _ hp)

namespace horn.IsCompatible

open modelCategoryQuillen

variable {X : SSet.{u}} {n : ℕ}
  {i : Fin (n + 2)} {f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X}
  (hf : horn.IsCompatible f) {Y : SSet.{u}} (p : X ⟶ Y) [Fibration p]
  (b : Δ[n + 1] ⟶ Y)
  (comm : ∀ (j : Fin (n + 2)) (hj : j ≠ i), f j hj ≫ p = stdSimplex.δ j ≫ b)

include hf comm in
/-
**SSet.horn.IsCompatible.exists_lift** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn.IsComp
atible`。
形式化陈述：exists_lift : exists (φ : Δ[n + 1] ⟶ X), (forall (j : Fin (n + 2)) (hj : j
 != i), stdSimplex.δ j ≫ φ = f j hj) ∧ φ ≫ p = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.horn.hom_ext'`：hom_ext' {i : Fin (n + 2)} {f g : (Λ[n + 1, i] : SSe
t) ⟶ X} (h : forall (j : Fin (n + 2)) (hj : j != i), horn.ι i j hj ≫ f = horn.ι 
i j hj ≫…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.horn.IsCompatible.ι_desc_assoc`：∀ {n : ℕ} {X : _root_.SSet} {i : Fi
n (n + 2)} {f : (j : Fin (n + 2)) → j ≠ i → (SSet.stdSimplex.obj { len := n } ⟶ 
X)}   (hf : SSet.horn.IsC…
· 使用定理 `SSet.horn.ι_ι_assoc`：∀ {n : ℕ} (i j : Fin (n + 2)) (hij : j ≠ i) {Z : _r
oot_.SSet} (h : SSet.stdSimplex.obj { len := n + 1 } ⟶ Z),   CategoryTheory.Cate
goryStruc…
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `SSet.modelCategoryQuillen.instHasLiftingPropertyιHornHAddNatOfNatOfFibra
tion`：∀ {X Y : _root_.SSet} (f : X ⟶ Y) [hf : HomotopicalAlgebra.Fibration f] {n
 : ℕ} (i : Fin (n + 2)),   CategoryTheory.HasLiftingProperty (SSet…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommSq.fac_left`：fac_left [hsq : HasLift sq] : i ≫ sq.lif
t = f
· 使用引理 `SSet.horn.IsCompatible.ι_desc`：ι_desc (hf : horn.IsCompatible f) (j : Fi
n (n + 2)) (hj : j != i) : horn.ι i j hj ≫ hf.desc = f j hj
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CommSq.fac_right`：∀ {C : Type u_1} [inst : CategoryTheory
.Category.{v_1, u_1} C] {A B X Y : C} {f : X ⟶ A} {i : B ⟶ A} {p : Y ⟶ X}   {g :
 Y ⟶ B} (sq : Categor…
-/
lemma exists_lift :
    ∃ (φ : Δ[n + 1] ⟶ X),
      (∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj) ∧
      φ ≫ p = b := by
  have sq : CommSq hf.desc Λ[n + 1, i].ι p b :=
    ⟨horn.hom_ext' (fun j hj ↦ by simpa using comm j hj)⟩
  exact ⟨sq.lift, fun j hj ↦ by simp [← ι_ι_assoc i j hj], by simp⟩

/-- If `f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X` is a compatible family
of morphisms (which defines a morphism `Λ[n + 1, i] ⟶ X`), `p : X ⟶ Y` a Kan fibration
and `b : Δ[n + 1] ⟶ Y` such that for all `j ≠ i`, `f j _ ≫ p = stdSimplex.δ j ≫ b`,
then this is a lifting `Δ[n + 1] ⟶ X`. -/
@[no_expose]
/-
**SSet.horn.IsCompatible.lift** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn.IsCompatible`
。
形式化陈述：lift : Δ[n + 1] ⟶ X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.horn.IsCompatible.exists_lift`：exists_lift : exists (φ : Δ[n + 1] ⟶
 X), (forall (j : Fin (n + 2)) (hj : j != i), stdSimplex.δ j ≫ φ = f j hj) ∧ φ ≫
 p = b

--- 原说明 ---
If `f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X` is a compatible family
of morphisms (which defines a morphism `Λ[n + 1, i] ⟶ X`), `p : X ⟶ Y` a Kan fib
ration
and `b : Δ[n + 1] ⟶ Y` such that for all `j ≠ i`, `f j _ ≫ p = stdSimplex.δ j ≫ 
b`,
then this is a lifting `Δ[n + 1] ⟶ X`.
-/
noncomputable def lift : Δ[n + 1] ⟶ X := (hf.exists_lift p b comm).choose

@[reassoc]
/-
**SSet.horn.IsCompatible.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn.IsCompatible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_lift (j : Fin (n + 2)) (hj : j ≠ i := by grind) :
    stdSimplex.δ j ≫ hf.lift p b comm = f j hj :=
  ((hf.exists_lift p b comm).choose_spec).1 j hj

@[reassoc (attr := simp)]
/-
**SSet.horn.IsCompatible.lift_comp** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn.IsCompat
ible`。
形式化陈述：lift_comp : hf.lift p b comm ≫ p = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `SSet.horn.IsCompatible.exists_lift`：exists_lift : exists (φ : Δ[n + 1] ⟶
 X), (forall (j : Fin (n + 2)) (hj : j != i), stdSimplex.δ j ≫ φ = f j hj) ∧ φ ≫
 p = b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma lift_comp : hf.lift p b comm ≫ p = b :=
  ((hf.exists_lift p b comm).choose_spec).2

end horn.IsCompatible

end SSet

