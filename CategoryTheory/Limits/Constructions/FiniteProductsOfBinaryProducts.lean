/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Constructing finite products from binary products and terminal.

If a category has binary products and a terminal object then it has finite products.
If a functor preserves binary products and the terminal object then it preserves finite products.

## TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/

@[expose] public section


universe v v' u u'

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

variable {J : Type v} [SmallCategory J]
variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

/--
Given `n+1` objects of `C`, a fan for the last `n` with point `c₁.pt` and
a binary fan on `c₁.pt` and `f 0`, we can build a fan for all `n+1`.

In `extendFanIsLimit` we show that if the two given fans are limits, then this fan is also a
limit.
-/
@[simps!]
/-
**CategoryTheory.extendFan** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：extendFan {n : Nat} {f : Fin (n + 1) -> C} (c₁ : Fan fun i : Fin n => f i.
succ) (c₂ : BinaryFan (f 0) c₁.pt) : Fan f
参数：n + 1；c₁ : Fan fun i : Fin n => f i.succ；c₂ : BinaryFan (f 0) c₁.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `n+1` objects of `C`, a fan for the last `n` with point `c₁.pt` and
a binary fan on `c₁.pt` and `f 0`, we can build a fan for all `n+1`.

In `extendFanIsLimit` we show that if the two given fans are limits, then this f
an is also a
limit.
-/
def extendFan {n : ℕ} {f : Fin (n + 1) → C} (c₁ : Fan fun i : Fin n => f i.succ)
    (c₂ : BinaryFan (f 0) c₁.pt) : Fan f :=
  Fan.mk c₂.pt
    (by
      refine Fin.cases ?_ ?_
      · apply c₂.fst
      · intro i
        apply c₂.snd ≫ c₁.π.app ⟨i⟩)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Show that if the two given fans in `extendFan` are limits, then the constructed fan is also a
limit.
-/
/-
**CategoryTheory.extendFanIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：extendFanIsLimit {n : Nat} (f : Fin (n + 1) -> C) {c₁ : Fan fun i : Fin n 
=> f i.succ} {c₂ : BinaryFan (f 0) c₁.pt} (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) : 
IsLimit (extendFan c₁ c₂) where lift s
参数：f : Fin (n + 1) -> C；f 0；t₁ : IsLimit c₁；t₂ : IsLimit c₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show that if the two given fans in `extendFan` are limits, then the constructed 
fan is also a
limit.
-/
def extendFanIsLimit {n : ℕ} (f : Fin (n + 1) → C) {c₁ : Fan fun i : Fin n => f i.succ}
    {c₂ : BinaryFan (f 0) c₁.pt} (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) :
    IsLimit (extendFan c₁ c₂) where
  lift s := by
    apply (BinaryFan.IsLimit.lift' t₂ (s.π.app ⟨0⟩) _).1
    apply t₁.lift ⟨_, Discrete.natTrans fun ⟨i⟩ => s.π.app ⟨i.succ⟩⟩
  fac := fun s ⟨j⟩ => by
    refine Fin.inductionOn j ?_ ?_
    · apply (BinaryFan.IsLimit.lift' t₂ _ _).2.1
    · rintro i -
      dsimp only [extendFan_π_app]
      rw [Fin.cases_succ, ← assoc, (BinaryFan.IsLimit.lift' t₂ _ _).2.2, t₁.fac]
      rfl
  uniq s m w := by
    apply BinaryFan.IsLimit.hom_ext t₂
    · rw [(BinaryFan.IsLimit.lift' t₂ _ _).2.1]
      apply w ⟨0⟩
    · rw [(BinaryFan.IsLimit.lift' t₂ _ _).2.2]
      apply t₁.uniq ⟨_, _⟩
      rintro ⟨j⟩
      rw [assoc]
      dsimp only [Discrete.natTrans_app]
      rw [← w ⟨j.succ⟩]
      dsimp only [extendFan_π_app]
      rw [Fin.cases_succ]

section

variable [HasBinaryProducts C] [HasTerminal C]

/-- If `C` has a terminal object and binary products, then it has a product for objects indexed by
`Fin n`.
This is a helper lemma for `hasFiniteProducts_of_has_binary_and_terminal`, which is more general
than this.
-/
/-
**CategoryTheory.hasProduct_fin** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` has a terminal object and binary products, then it has a product for obje
cts indexed by
`Fin n`.
This is a helper lemma for `hasFiniteProducts_of_has_binary_and_terminal`, which
 is more general
than this.
-/
private theorem hasProduct_fin : ∀ (n : ℕ) (f : Fin n → C), HasProduct f
  | 0 => fun _ =>
    letI : HasLimitsOfShape (Discrete (Fin 0)) C :=
      hasLimitsOfShape_of_equivalence (Discrete.equivalence.{0} finZeroEquiv'.symm)
    inferInstance
  | n + 1 => fun f =>
    haveI := hasProduct_fin n
    HasLimit.mk ⟨_, extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)⟩

/-- If `C` has a terminal object and binary products, then it has finite products. -/
/-
**CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory`。
形式化陈述：hasFiniteProducts_of_has_binary_and_terminal : HasFiniteProducts C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.hasLimit_iff_of_iso`：hasLimit_iff_of_iso {F G : J 
⥤ C} (α : F ≅ G) : HasLimit F ↔ HasLimit G
· 使用定理 `_private.Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBin
aryProducts.0.CategoryTheory.hasProduct_fin`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [CategoryTheory.Limits.HasBinaryProducts C]   [CategoryThe
ory.Limits.HasTerminal C]…

--- 原说明 ---
If `C` has a terminal object and binary products, then it has finite products.
-/
theorem hasFiniteProducts_of_has_binary_and_terminal : HasFiniteProducts C :=
  ⟨fun n => ⟨fun K => by
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨_⟩ => Iso.refl _
    rw [← hasLimit_iff_of_iso that]
    apply hasProduct_fin⟩⟩


end

section Preserves

variable (F : C ⥤ D)
variable [PreservesLimitsOfShape (Discrete WalkingPair) F]
variable [PreservesLimitsOfShape (Discrete.{0} PEmpty) F]
variable [HasFiniteProducts.{v} C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F` preserves the terminal object and binary products, then it preserves products indexed by
`Fin n` for any `n`.
-/
/-
**CategoryTheory.preservesFinOfPreservesBinaryAndTerminal** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory`。
形式化陈述：preservesFinOfPreservesBinaryAndTerminal : forall (n : Nat) (f : Fin n -> 
C), PreservesLimit (Discrete.functor f) F | 0 => fun f => by let : PreservesLimi
tsOfShape (Discrete (Fin 0)) F
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` preserves the terminal object and binary products, then it preserves prod
ucts indexed by
`Fin n` for any `n`.
-/
lemma preservesFinOfPreservesBinaryAndTerminal :
    ∀ (n : ℕ) (f : Fin n → C), PreservesLimit (Discrete.functor f) F
  | 0 => fun f => by
    let : PreservesLimitsOfShape (Discrete (Fin 0)) F :=
      preservesLimitsOfShape_of_equiv.{0, 0} (Discrete.equivalence finZeroEquiv'.symm) _
    infer_instance
  | n + 1 => by
    have := preservesFinOfPreservesBinaryAndTerminal n
    intro f
    apply
      preservesLimit_of_preserves_limit_cone
        (extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)) _
    apply (isLimitMapConeFanMkEquiv _ _ _).symm _
    let :=
      extendFanIsLimit (fun i => F.obj (f i)) (isLimitOfHasProductOfPreservesLimit F _)
        (isLimitOfHasBinaryProductOfPreservesLimit F _ _)
    refine IsLimit.ofIsoLimit this ?_
    apply Cone.ext _ _
    · apply Iso.refl _
    rintro ⟨j⟩
    refine Fin.inductionOn j ?_ ?_
    · apply (Category.id_comp _).symm
    · rintro i _
      dsimp [extendFan_π_app, Iso.refl_hom, Fan.mk_π_app]
      change F.map _ ≫ _ = 𝟙 _ ≫ _
      simp only [id_comp, ← F.map_comp]
      rfl

/-- If `F` preserves the terminal object and binary products then it preserves finite products. -/
/-
**CategoryTheory.Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal
** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.PreservesFiniteProducts`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   (F : CategoryTheory.Functor C D)   
[CategoryTheory.Limits.PreservesLimitsOfShape (CategoryTheory.Discrete CategoryT
heory.Limits.WalkingPair) F]   [CategoryTheory.Limits.PreservesLimitsOfShape (Ca
tegoryTheory.Discrete PEmpty.{1}) F]   [CategoryTheory.Limits.HasFiniteProducts 
C], CategoryTheory.Limits.PreservesFiniteProducts F
参数：F : CategoryTheory.Functor C D；CategoryTheory.Discrete CategoryTheory.Limits.
WalkingPair；CategoryTheory.Discrete PEmpty.{1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.preservesFinOfPreservesBinaryAndTerminal`：preservesFinOfP
reservesBinaryAndTerminal : forall (n : Nat) (f : Fin n -> C), PreservesLimit (D
iscrete.functor f) F | 0 => fun f => by let :…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t

--- 原说明 ---
If `F` preserves the terminal object and binary products then it preserves finit
e products.
-/
lemma Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal :
    PreservesFiniteProducts F where
  preserves n := by
    refine ⟨fun {K} ↦ ?_⟩
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
    have := preservesFinOfPreservesBinaryAndTerminal F n fun n => K.obj ⟨n⟩
    apply preservesLimit_of_iso_diagram F that

end Preserves

/-- Given `n+1` objects of `C`, a cofan for the last `n` with point `c₁.pt`
and a binary cofan on `c₁.X` and `f 0`, we can build a cofan for all `n+1`.

In `extendCofanIsColimit` we show that if the two given cofans are colimits,
then this cofan is also a colimit.
-/
@[simps!]
/-
**CategoryTheory.extendCofan** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：extendCofan {n : Nat} {f : Fin (n + 1) -> C} (c₁ : Cofan fun i : Fin n => 
f i.succ) (c₂ : BinaryCofan (f 0) c₁.pt) : Cofan f
参数：n + 1；c₁ : Cofan fun i : Fin n => f i.succ；c₂ : BinaryCofan (f 0) c₁.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `n+1` objects of `C`, a cofan for the last `n` with point `c₁.pt`
and a binary cofan on `c₁.X` and `f 0`, we can build a cofan for all `n+1`.

In `extendCofanIsColimit` we show that if the two given cofans are colimits,
then this cofan is also a colimit.
-/
def extendCofan {n : ℕ} {f : Fin (n + 1) → C} (c₁ : Cofan fun i : Fin n => f i.succ)
    (c₂ : BinaryCofan (f 0) c₁.pt) : Cofan f :=
  Cofan.mk c₂.pt
    (by
      refine Fin.cases ?_ ?_
      · apply c₂.inl
      · intro i
        apply c₁.ι.app ⟨i⟩ ≫ c₂.inr)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Show that if the two given cofans in `extendCofan` are colimits,
then the constructed cofan is also a colimit.
-/
/-
**CategoryTheory.extendCofanIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：extendCofanIsColimit {n : Nat} (f : Fin (n + 1) -> C) {c₁ : Cofan fun i : 
Fin n => f i.succ} {c₂ : BinaryCofan (f 0) c₁.pt} (t₁ : IsColimit c₁) (t₂ : IsCo
limit c₂) : IsColimit (extendCofan c₁ c₂) where desc s
参数：f : Fin (n + 1) -> C；f 0；t₁ : IsColimit c₁；t₂ : IsColimit c₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show that if the two given cofans in `extendCofan` are colimits,
then the constructed cofan is also a colimit.
-/
def extendCofanIsColimit {n : ℕ} (f : Fin (n + 1) → C) {c₁ : Cofan fun i : Fin n => f i.succ}
    {c₂ : BinaryCofan (f 0) c₁.pt} (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) :
    IsColimit (extendCofan c₁ c₂) where
  desc s := by
    apply (BinaryCofan.IsColimit.desc' t₂ (s.ι.app ⟨0⟩) _).1
    apply t₁.desc ⟨_, Discrete.natTrans fun i => s.ι.app ⟨i.as.succ⟩⟩
  fac s := by
    rintro ⟨j⟩
    refine Fin.inductionOn j ?_ ?_
    · apply (BinaryCofan.IsColimit.desc' t₂ _ _).2.1
    · rintro i -
      dsimp only [extendCofan_ι_app]
      rw [Fin.cases_succ, assoc, (BinaryCofan.IsColimit.desc' t₂ _ _).2.2, t₁.fac]
      rfl
  uniq s m w := by
    apply BinaryCofan.IsColimit.hom_ext t₂
    · rw [(BinaryCofan.IsColimit.desc' t₂ _ _).2.1]
      apply w ⟨0⟩
    · rw [(BinaryCofan.IsColimit.desc' t₂ _ _).2.2]
      apply t₁.uniq ⟨_, _⟩
      rintro ⟨j⟩
      dsimp only [Discrete.natTrans_app]
      rw [← w ⟨j.succ⟩]
      dsimp only [extendCofan_ι_app]
      rw [Fin.cases_succ, assoc]

section

variable [HasBinaryCoproducts C] [HasInitial C]

/--
If `C` has an initial object and binary coproducts, then it has a coproduct for objects indexed by
`Fin n`.
This is a helper lemma for `hasFiniteCoproducts_of_has_binary_and_initial`, which is more general
than this.
-/
/-
**CategoryTheory.hasCoproduct_fin** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` has an initial object and binary coproducts, then it has a coproduct for 
objects indexed by
`Fin n`.
This is a helper lemma for `hasFiniteCoproducts_of_has_binary_and_initial`, whic
h is more general
than this.
-/
private theorem hasCoproduct_fin : ∀ (n : ℕ) (f : Fin n → C), HasCoproduct f
  | 0 => fun _ =>
    letI : HasColimitsOfShape (Discrete (Fin 0)) C :=
      hasColimitsOfShape_of_equivalence (Discrete.equivalence.{0} finZeroEquiv'.symm)
    inferInstance
  | n + 1 => fun f =>
    haveI := hasCoproduct_fin n
    HasColimit.mk ⟨_, extendCofanIsColimit f (colimit.isColimit _) (colimit.isColimit _)⟩

/-- If `C` has an initial object and binary coproducts, then it has finite coproducts. -/
/-
**CategoryTheory.hasFiniteCoproducts_of_has_binary_and_initial** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory`。
形式化陈述：hasFiniteCoproducts_of_has_binary_and_initial : HasFiniteCoproducts C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.hasColimit_iff_of_iso`：∀ {J : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.
{v, u} C]   {F G : CategoryTheory…
· 使用定理 `_private.Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBin
aryProducts.0.CategoryTheory.hasCoproduct_fin`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [CategoryTheory.Limits.HasBinaryCoproducts C]   [Categor
yTheory.Limits.HasInitial C…

--- 原说明 ---
If `C` has an initial object and binary coproducts, then it has finite coproduct
s.
-/
theorem hasFiniteCoproducts_of_has_binary_and_initial : HasFiniteCoproducts C :=
  ⟨fun n => ⟨fun K => by
    let that : K ≅ Discrete.functor fun n => K.obj ⟨n⟩ := Discrete.natIso fun ⟨_⟩ => Iso.refl _
    rw [hasColimit_iff_of_iso that]
    apply hasCoproduct_fin⟩⟩

end

section Preserves

variable (F : C ⥤ D)
variable [PreservesColimitsOfShape (Discrete WalkingPair) F]
variable [PreservesColimitsOfShape (Discrete.{0} PEmpty) F]
variable [HasFiniteCoproducts.{v} C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F` preserves the initial object and binary coproducts, then it preserves products indexed by
`Fin n` for any `n`.
-/
/-
**CategoryTheory.preserves_fin_of_preserves_binary_and_initial** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory`。
形式化陈述：preserves_fin_of_preserves_binary_and_initial : forall (n : Nat) (f : Fin 
n -> C), PreservesColimit (Discrete.functor f) F | 0 => fun f => by let : Preser
vesColimitsOfShape (Discrete (Fin 0)) F
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` preserves the initial object and binary coproducts, then it preserves pro
ducts indexed by
`Fin n` for any `n`.
-/
lemma preserves_fin_of_preserves_binary_and_initial :
    ∀ (n : ℕ) (f : Fin n → C), PreservesColimit (Discrete.functor f) F
  | 0 => fun f => by
    let : PreservesColimitsOfShape (Discrete (Fin 0)) F :=
      preservesColimitsOfShape_of_equiv.{0, 0} (Discrete.equivalence finZeroEquiv'.symm) _
    infer_instance
  | n + 1 => by
    have := preserves_fin_of_preserves_binary_and_initial n
    intro f
    apply
      preservesColimit_of_preserves_colimit_cocone
        (extendCofanIsColimit f (colimit.isColimit _) (colimit.isColimit _)) _
    apply (isColimitMapCoconeCofanMkEquiv _ _ _).symm _
    let :=
      extendCofanIsColimit (fun i => F.obj (f i))
        (isColimitOfHasCoproductOfPreservesColimit F _)
        (isColimitOfHasBinaryCoproductOfPreservesColimit F _ _)
    refine IsColimit.ofIsoColimit this ?_
    apply Cocone.ext _ _
    · apply Iso.refl _
    rintro ⟨j⟩
    refine Fin.inductionOn j ?_ ?_
    · apply Category.comp_id
    · rintro i _
      dsimp [extendCofan_ι_app, Iso.refl_hom, Cofan.mk_ι_app]
      rw [comp_id, ← F.map_comp]
      rfl

/-- If `F` preserves the initial object and binary coproducts, then it preserves colimits of shape
`Discrete (Fin n)`.
-/
/-
**CategoryTheory.preservesShape_fin_of_preserves_binary_and_initial** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：preservesShape_fin_of_preserves_binary_and_initial (n : Nat) : PreservesCo
limitsOfShape (Discrete (Fin n)) F where preservesColimit {K}
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.preserves_fin_of_preserves_binary_and_initial`：preserves_
fin_of_preserves_binary_and_initial : forall (n : Nat) (f : Fin n -> C), Preserv
esColimit (Discrete.functor f) F | 0 => fun f => b…
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_iso_diagram`：preservesColimit_
of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F]
 : PreservesColimit K₂ F where preserves {c…

--- 原说明 ---
If `F` preserves the initial object and binary coproducts, then it preserves col
imits of shape
`Discrete (Fin n)`.
-/
lemma preservesShape_fin_of_preserves_binary_and_initial (n : ℕ) :
    PreservesColimitsOfShape (Discrete (Fin n)) F where
  preservesColimit {K} := by
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
    have := preserves_fin_of_preserves_binary_and_initial F n fun n => K.obj ⟨n⟩
    apply preservesColimit_of_iso_diagram F that

/-- If `F` preserves the initial object and binary coproducts then it preserves finite products. -/
/-
**CategoryTheory.PreservesFiniteCoproducts.of_preserves_binary_and_initial** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.PreservesFiniteCoproducts`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   (F : CategoryTheory.Functor C D)   
[CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete Categor
yTheory.Limits.WalkingPair) F]   [CategoryTheory.Limits.PreservesColimitsOfShape
 (CategoryTheory.Discrete PEmpty.{1}) F]   [CategoryTheory.Limits.HasFiniteCopro
ducts C] (J : Type u_1) [Finite J],   CategoryTheory.Limits.PreservesColimitsOfS
hape (CategoryTheory.Discrete J) F
参数：F : CategoryTheory.Functor C D；CategoryTheory.Discrete CategoryTheory.Limits.
WalkingPair；CategoryTheory.Discrete PEmpty.{1}；J : Type u_1；CategoryTheory.Discr
ete J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用引理 `CategoryTheory.preservesShape_fin_of_preserves_binary_and_initial`：prese
rvesShape_fin_of_preserves_binary_and_initial (n : Nat) : PreservesColimitsOfSha
pe (Discrete (Fin n)) F where preservesColimit {K}
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_equiv`：preservesColimi
tsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [
PreservesColimitsOfShape J F] : PreservesColi…

--- 原说明 ---
If `F` preserves the initial object and binary coproducts then it preserves fini
te products.
-/
lemma PreservesFiniteCoproducts.of_preserves_binary_and_initial (J : Type*) [Finite J] :
    PreservesColimitsOfShape (Discrete J) F :=
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := preservesShape_fin_of_preserves_binary_and_initial F n
  preservesColimitsOfShape_of_equiv (Discrete.equivalence e).symm _

@[deprecated (since := "2026-03-10")]
alias preservesFiniteCoproductsOfPreservesBinaryAndInitial :=
  PreservesFiniteCoproducts.of_preserves_binary_and_initial

end Preserves

end CategoryTheory

