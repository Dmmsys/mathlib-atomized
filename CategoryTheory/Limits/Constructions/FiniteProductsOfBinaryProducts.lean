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
/--
Definition of `extendFan` / `extendFan` 的定义

English:
definition extendFan
  signature: {n : Nat} {f : Fin (n + 1) -> C} (c₁ : Fan fun i : Fin n => f i.succ)
  body: Fan.mk c₂.pt
    (by
      refine Fin.cases ?_ ?_
      · apply c₂.fst
      · intro i
        apply c₂.snd ≫ c₁.π.app ⟨i⟩)

中文:
定义 extendFan
  签名: {n : 自然数} {f : 有限集 (n + 1) -> C} (c₁ : Fan fun i : 有限集 n => f i.succ)
  定义体: Fan.mk c₂.pt
    (by
      refine Fin.cases ?_ ?_
      · apply c₂.fst
      · intro i
        apply c₂.snd ≫ c₁.π.app ⟨i⟩)

Depends on / 依赖: Fan.mk, Fin.cases
-/
def extendFan {n : Nat} {f : Fin (n + 1) -> C} (c₁ : Fan fun i : Fin n => f i.succ)
    (c₂ : BinaryFan (f 0) c₁.pt) : Fan f :=
  Fan.mk c₂.pt
    (by
      refine Fin.cases ?_ ?_
      · apply c₂.fst
      · intro i
        apply c₂.snd ≫ c₁.π.app ⟨i⟩)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `extendFanIsLimit` / `extendFanIsLimit` 的定义

English:
definition extendFanIsLimit
  signature: {n : Nat} (f : Fin (n + 1) -> C) {c₁ : Fan fun i : Fin n => f i.succ}
  body: by
    apply (BinaryFan.IsLimit.lift' t₂ (s.π.app ⟨0⟩) _).1
    apply t₁.lift ⟨_, Discrete.natTrans fun ⟨i⟩ => s.π.app ⟨i.succ⟩⟩
  fac := fun s ⟨j⟩ => by
    refine Fin.inductionOn j ?_ ?_
    · apply (BinaryFan.IsLimit.lift' t₂ _ _).2.1
    · rintro i -
      dsimp only [extendFan_π_app]
      rw [

中文:
定义 extendFanIsLimit
  签名: {n : 自然数} (f : 有限集 (n + 1) -> C) {c₁ : Fan fun i : 有限集 n => f i.succ}
  定义体: by
    apply (BinaryFan.IsLimit.lift' t₂ (s.π.app ⟨0⟩) _).1
    apply t₁.lift ⟨_, Discrete.natTrans fun ⟨i⟩ => s.π.app ⟨i.succ⟩⟩
  fac := fun s ⟨j⟩ => by
    refine Fin.inductionOn j ?_ ?_
    · apply (BinaryFan.IsLimit.lift' t₂ _ _).2.1
    · rintro i -
      dsimp only [extendFan_π_app]
      rw [

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.hom_ext, BinaryFan.IsLimit.lift, Discrete, Discrete.natTrans, Fin.cases_succ, Fin.inductionOn, IsLimit, cases_succ, hom_ext, i.succ, inductionOn, natTrans
-/
def extendFanIsLimit {n : Nat} (f : Fin (n + 1) -> C) {c₁ : Fan fun i : Fin n => f i.succ}
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
      rw [Fin.cases_succ]; rw [← assoc]; rw [(BinaryFan.IsLimit.lift' t₂ _ _).2.2]; rw [t₁.fac]
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

/--
theorem `hasProduct_fin` / 定理 `hasProduct_fin`

English:
theorem hasProduct_fin
  statement: forall (n : Nat) (f : Fin n -> C), HasProduct f
  proof: hasLimitsOfShape_of_equivalence (Discrete.equivalence.{0} finZeroEquiv'.symm)
    inferInstance
  | n + 1 => fun f =>
    haveI := hasProduct_fin n
    HasLimit.mk ⟨_, extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)⟩

中文:
定理 hasProduct_fin
  结论: 对任意 (n : 自然数) (f : 有限集 n -> C), HasProduct f
  证明: hasLimitsOfShape_of_equivalence (Discrete.equivalence.{0} finZeroEquiv'.symm)
    inferInstance
  | n + 1 => fun f =>
    haveI := hasProduct_fin n
    HasLimit.mk ⟨_, extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)⟩
-/
private theorem hasProduct_fin : forall (n : Nat) (f : Fin n -> C), HasProduct f
  | 0 => fun _ =>
    letI : HasLimitsOfShape (Discrete (Fin 0)) C :=
      hasLimitsOfShape_of_equivalence (Discrete.equivalence.{0} finZeroEquiv'.symm)
    inferInstance
  | n + 1 => fun f =>
    haveI := hasProduct_fin n
    HasLimit.mk ⟨_, extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)⟩

/--
theorem `hasFiniteProducts_of_has_binary_and_terminal` / 定理 `hasFiniteProducts_of_has_binary_and_terminal`

English:
theorem hasFiniteProducts_of_has_binary_and_terminal
  statement: HasFiniteProducts C
  proof: ⟨fun n => ⟨fun K => by
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨_⟩ => Iso.refl _
    rw [← hasLimit_iff_of_iso that]
    apply hasProduct_fin⟩⟩

中文:
定理 hasFiniteProducts_of_has_binary_and_terminal
  结论: 有FiniteProducts C
  证明: ⟨fun n => ⟨fun K => by
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨_⟩ => Iso.refl _
    rw [← hasLimit_iff_of_iso that]
    apply hasProduct_fin⟩⟩

Depends on / 依赖: Discrete, Discrete.functor, Discrete.natIso, Iso.refl, K.obj, functor, hasLimit_iff_of_iso, hasProduct_fin, natIso
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
/--
lemma `preservesFinOfPreservesBinaryAndTerminal` / 引理 `preservesFinOfPreservesBinaryAndTerminal`

English:
lemma preservesFinOfPreservesBinaryAndTerminal
  proof: preservesLimitsOfShape_of_equiv.{0, 0} (Discrete.equivalence finZeroEquiv'.symm) _
    infer_instance
  | n + 1 => by
    have := preservesFinOfPreservesBinaryAndTerminal n
    intro f
    apply
      preservesLimit_of_preserves_limit_cone
        (extendFanIsLimit f (limit.isLimit _) (limit.isLimit

中文:
引理 preservesFinOfPreservesBinaryAndTerminal
  证明: preservesLimitsOfShape_of_equiv.{0, 0} (Discrete.equivalence finZeroEquiv'.symm) _
    infer_instance
  | n + 1 => by
    have := preservesFinOfPreservesBinaryAndTerminal n
    intro f
    apply
      preservesLimit_of_preserves_limit_cone
        (extendFanIsLimit f (limit.isLimit _) (limit.isLimit

Depends on / 依赖: Discrete, Discrete.equivalence, F.obj, IsLimit, IsLimit.ofIsoLimit, equivalence, extendFanIsLimit, finZeroEquiv, infer_instance, isLimit, isLimitMapConeFanMkEquiv, isLimitOfHasBinaryProductOfPreservesLimit, isLimitOfHasProductOfPreservesLimit, limit.isLimit, ofIsoLimit, preservesFinOfPreservesBinaryAndTerminal, preservesLimit_of_preserves_limit_cone, preservesLimitsOfShape_of_equiv
-/
lemma preservesFinOfPreservesBinaryAndTerminal :
    forall (n : Nat) (f : Fin n -> C), PreservesLimit (Discrete.functor f) F
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

/--
lemma `Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal` / 引理 `Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal`

English:
lemma Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal
  proof: by
    refine ⟨fun {K} => ?_⟩
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
    have := preservesFinOfPreservesBinaryAndTerminal F n fun n => K.obj ⟨n⟩
    apply preservesLimit_of_iso_diagram F that

中文:
引理 Limits.保持FiniteProducts.of_preserves_binary_and_terminal
  证明: by
    refine ⟨fun {K} => ?_⟩
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
    have := preservesFinOfPreservesBinaryAndTerminal F n fun n => K.obj ⟨n⟩
    apply preservesLimit_of_iso_diagram F that

Depends on / 依赖: Discrete, Discrete.functor, Discrete.natIso, Iso.refl, K.obj, functor, natIso, preservesFinOfPreservesBinaryAndTerminal, preservesLimit_of_iso_diagram
-/
lemma Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal :
    PreservesFiniteProducts F where
  preserves n := by
    refine ⟨fun {K} => ?_⟩
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
/--
Definition of `extendCofan` / `extendCofan` 的定义

English:
definition extendCofan
  signature: {n : Nat} {f : Fin (n + 1) -> C} (c₁ : Cofan fun i : Fin n => f i.succ)
  body: Cofan.mk c₂.pt
    (by
      refine Fin.cases ?_ ?_
      · apply c₂.inl
      · intro i
        apply c₁.ι.app ⟨i⟩ ≫ c₂.inr)

中文:
定义 extendCofan
  签名: {n : 自然数} {f : 有限集 (n + 1) -> C} (c₁ : Cofan fun i : 有限集 n => f i.succ)
  定义体: Cofan.mk c₂.pt
    (by
      refine Fin.cases ?_ ?_
      · apply c₂.inl
      · intro i
        apply c₁.ι.app ⟨i⟩ ≫ c₂.inr)

Depends on / 依赖: Cofan.mk, Fin.cases
-/
def extendCofan {n : Nat} {f : Fin (n + 1) -> C} (c₁ : Cofan fun i : Fin n => f i.succ)
    (c₂ : BinaryCofan (f 0) c₁.pt) : Cofan f :=
  Cofan.mk c₂.pt
    (by
      refine Fin.cases ?_ ?_
      · apply c₂.inl
      · intro i
        apply c₁.ι.app ⟨i⟩ ≫ c₂.inr)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `extendCofanIsColimit` / `extendCofanIsColimit` 的定义

English:
definition extendCofanIsColimit
  signature: {n : Nat} (f : Fin (n + 1) -> C) {c₁ : Cofan fun i : Fin n => f i.succ}
  body: by
    apply (BinaryCofan.IsColimit.desc' t₂ (s.ι.app ⟨0⟩) _).1
    apply t₁.desc ⟨_, Discrete.natTrans fun i => s.ι.app ⟨i.as.succ⟩⟩
  fac s := by
    rintro ⟨j⟩
    refine Fin.inductionOn j ?_ ?_
    · apply (BinaryCofan.IsColimit.desc' t₂ _ _).2.1
    · rintro i -
      dsimp only [extendCofan_ι_

中文:
定义 extendCofanIsColimit
  签名: {n : 自然数} (f : 有限集 (n + 1) -> C) {c₁ : Cofan fun i : 有限集 n => f i.succ}
  定义体: by
    apply (BinaryCofan.IsColimit.desc' t₂ (s.ι.app ⟨0⟩) _).1
    apply t₁.desc ⟨_, Discrete.natTrans fun i => s.ι.app ⟨i.as.succ⟩⟩
  fac s := by
    rintro ⟨j⟩
    refine Fin.inductionOn j ?_ ?_
    · apply (BinaryCofan.IsColimit.desc' t₂ _ _).2.1
    · rintro i -
      dsimp only [extendCofan_ι_

Depends on / 依赖: BinaryCo, BinaryCofan, BinaryCofan.IsColimit.desc, BinaryCofan.IsColimit.hom_ext, Discrete, Discrete.natTrans, Fin.cases_succ, Fin.inductionOn, IsColimit, cases_succ, hom_ext, i.as.succ, inductionOn, natTrans
-/
def extendCofanIsColimit {n : Nat} (f : Fin (n + 1) -> C) {c₁ : Cofan fun i : Fin n => f i.succ}
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
      rw [Fin.cases_succ]; rw [assoc]; rw [(BinaryCofan.IsColimit.desc' t₂ _ _).2.2]; rw [t₁.fac]
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
      rw [Fin.cases_succ]; rw [assoc]

section

variable [HasBinaryCoproducts C] [HasInitial C]

/--
theorem `hasCoproduct_fin` / 定理 `hasCoproduct_fin`

English:
theorem hasCoproduct_fin
  statement: forall (n : Nat) (f : Fin n -> C), HasCoproduct f
  proof: hasColimitsOfShape_of_equivalence (Discrete.equivalence.{0} finZeroEquiv'.symm)
    inferInstance
  | n + 1 => fun f =>
    haveI := hasCoproduct_fin n
    HasColimit.mk ⟨_, extendCofanIsColimit f (colimit.isColimit _) (colimit.isColimit _)⟩

中文:
定理 hasCoproduct_fin
  结论: 对任意 (n : 自然数) (f : 有限集 n -> C), HasCoproduct f
  证明: hasColimitsOfShape_of_equivalence (Discrete.equivalence.{0} finZeroEquiv'.symm)
    inferInstance
  | n + 1 => fun f =>
    haveI := hasCoproduct_fin n
    HasColimit.mk ⟨_, extendCofanIsColimit f (colimit.isColimit _) (colimit.isColimit _)⟩
-/
private theorem hasCoproduct_fin : forall (n : Nat) (f : Fin n -> C), HasCoproduct f
  | 0 => fun _ =>
    letI : HasColimitsOfShape (Discrete (Fin 0)) C :=
      hasColimitsOfShape_of_equivalence (Discrete.equivalence.{0} finZeroEquiv'.symm)
    inferInstance
  | n + 1 => fun f =>
    haveI := hasCoproduct_fin n
    HasColimit.mk ⟨_, extendCofanIsColimit f (colimit.isColimit _) (colimit.isColimit _)⟩

/--
theorem `hasFiniteCoproducts_of_has_binary_and_initial` / 定理 `hasFiniteCoproducts_of_has_binary_and_initial`

English:
theorem hasFiniteCoproducts_of_has_binary_and_initial
  statement: HasFiniteCoproducts C
  proof: ⟨fun n => ⟨fun K => by
    let that : K ≅ Discrete.functor fun n => K.obj ⟨n⟩ := Discrete.natIso fun ⟨_⟩ => Iso.refl _
    rw [hasColimit_iff_of_iso that]
    apply hasCoproduct_fin⟩⟩

中文:
定理 hasFiniteCoproducts_of_has_binary_and_initial
  结论: 有FiniteCoproducts C
  证明: ⟨fun n => ⟨fun K => by
    let that : K ≅ Discrete.functor fun n => K.obj ⟨n⟩ := Discrete.natIso fun ⟨_⟩ => Iso.refl _
    rw [hasColimit_iff_of_iso that]
    apply hasCoproduct_fin⟩⟩

Depends on / 依赖: Discrete, Discrete.functor, Discrete.natIso, Iso.refl, K.obj, functor, hasColimit_iff_of_iso, hasCoproduct_fin, natIso
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
/--
lemma `preserves_fin_of_preserves_binary_and_initial` / 引理 `preserves_fin_of_preserves_binary_and_initial`

English:
lemma preserves_fin_of_preserves_binary_and_initial
  proof: preservesColimitsOfShape_of_equiv.{0, 0} (Discrete.equivalence finZeroEquiv'.symm) _
    infer_instance
  | n + 1 => by
    have := preserves_fin_of_preserves_binary_and_initial n
    intro f
    apply
      preservesColimit_of_preserves_colimit_cocone
        (extendCofanIsColimit f (colimit.isColi

中文:
引理 preserves_fin_of_preserves_binary_and_initial
  证明: preservesColimitsOfShape_of_equiv.{0, 0} (Discrete.equivalence finZeroEquiv'.symm) _
    infer_instance
  | n + 1 => by
    have := preserves_fin_of_preserves_binary_and_initial n
    intro f
    apply
      preservesColimit_of_preserves_colimit_cocone
        (extendCofanIsColimit f (colimit.isColi

Depends on / 依赖: Discrete, Discrete.equivalence, F.obj, colimit, colimit.isColimit, equivalence, extendCofanIsColimit, finZeroEquiv, infer_instance, isColimit, isColimitMapCoconeCofanMkEquiv, isColimitOfHasBinaryCoproductOfPreservesColimit, isColimitOfHasCoproductOfPreservesColimit, preservesColimit_of_preserves_colimit_cocone, preservesColimitsOfShape_of_equiv, preserves_fin_of_preserves_binary_and_initial
-/
lemma preserves_fin_of_preserves_binary_and_initial :
    forall (n : Nat) (f : Fin n -> C), PreservesColimit (Discrete.functor f) F
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
      rw [comp_id]; rw [← F.map_comp]
      rfl

/--
lemma `preservesShape_fin_of_preserves_binary_and_initial` / 引理 `preservesShape_fin_of_preserves_binary_and_initial`

English:
lemma preservesShape_fin_of_preserves_binary_and_initial
  given: (n : Nat)
  proof: by
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
    have := preserves_fin_of_preserves_binary_and_initial F n fun n => K.obj ⟨n⟩
    apply preservesColimit_of_iso_diagram F that

中文:
引理 preservesShape_fin_of_preserves_binary_and_initial
  条件: (n : 自然数)
  证明: by
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
    have := preserves_fin_of_preserves_binary_and_initial F n fun n => K.obj ⟨n⟩
    apply preservesColimit_of_iso_diagram F that

Depends on / 依赖: Discrete, Discrete.functor, Discrete.natIso, Iso.refl, K.obj, functor, natIso, preservesColimit_of_iso_diagram, preserves_fin_of_preserves_binary_and_initial
-/
lemma preservesShape_fin_of_preserves_binary_and_initial (n : Nat) :
    PreservesColimitsOfShape (Discrete (Fin n)) F where
  preservesColimit {K} := by
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
    have := preserves_fin_of_preserves_binary_and_initial F n fun n => K.obj ⟨n⟩
    apply preservesColimit_of_iso_diagram F that

/--
lemma `PreservesFiniteCoproducts.of_preserves_binary_and_initial` / 引理 `PreservesFiniteCoproducts.of_preserves_binary_and_initial`

English:
lemma PreservesFiniteCoproducts.of_preserves_binary_and_initial
  given: (J : Type*) [Finite J]
  proof: let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := preservesShape_fin_of_preserves_binary_and_initial F n
  preservesColimitsOfShape_of_equiv (Discrete.equivalence e).symm _

@[deprecated (since := "2026-03-10")]
alias preservesFiniteCoproductsOfPreservesBinaryAndInitial :=
  PreservesFiniteCoprodu

中文:
引理 保持FiniteCoproducts.of_preserves_binary_and_initial
  条件: (J : 类型) [有限 J]
  证明: let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := preservesShape_fin_of_preserves_binary_and_initial F n
  preservesColimitsOfShape_of_equiv (Discrete.equivalence e).symm _

@[deprecated (since := "2026-03-10")]
alias preservesFiniteCoproductsOfPreservesBinaryAndInitial :=
  PreservesFiniteCoprodu

Depends on / 依赖: Discrete, Discrete.equivalence, Finite, Finite.exists_equiv_fin, equivalence, exists_equiv_fin, preservesColimitsOfShape_of_equiv, preservesShape_fin_of_preserves_binary_and_initial
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
