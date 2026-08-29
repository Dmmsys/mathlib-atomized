/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.SetTheory.Cardinal.Regular

/-!
# The property of being of cardinality less than a cardinal

Given `X : Type u` and `κ : Cardinal.{v}`, we introduce a predicate
`HasCardinalLT X κ` expressing that
`Cardinal.lift.{v} (Cardinal.mk X) < Cardinal.lift κ`.

-/

@[expose] public section

universe w v u u'

/--
Definition of `HasCardinalLT` / `HasCardinalLT` 的定义

English:
definition HasCardinalLT
  signature: (X : Type u) (κ : Cardinal.{v})
  body: Cardinal.lift.{v} (Cardinal.mk X) < Cardinal.lift κ

中文:
定义 HasCardinalLT
  签名: (X : 类型u) (κ : 基数.{v})
  定义体: Cardinal.lift.{v} (Cardinal.mk X) < Cardinal.lift κ

Depends on / 依赖: Cardinal, Cardinal.lift, Cardinal.mk
-/
def HasCardinalLT (X : Type u) (κ : Cardinal.{v}) : Prop :=
  Cardinal.lift.{v} (Cardinal.mk X) < Cardinal.lift κ

/--
lemma `hasCardinalLT_iff_cardinal_mk_lt` / 引理 `hasCardinalLT_iff_cardinal_mk_lt`

English:
lemma hasCardinalLT_iff_cardinal_mk_lt
  given: (X : Type u) (κ : Cardinal.{u})
  proof: by
  simp [HasCardinalLT]

中文:
引理 hasCardinalLT_iff_cardinal_mk_lt
  条件: (X : 类型u) (κ : 基数.{u})
  证明: by
  simp [HasCardinalLT]

Depends on / 依赖: HasCardinalLT
-/
lemma hasCardinalLT_iff_cardinal_mk_lt (X : Type u) (κ : Cardinal.{u}) :
    HasCardinalLT X κ ↔ Cardinal.mk X < κ := by
  simp [HasCardinalLT]

namespace HasCardinalLT

section

variable {X : Type u} {κ : Cardinal.{v}} (h : HasCardinalLT X κ)

include h

/--
lemma `small` / 引理 `small`

English:
lemma small
  statement: Small.{v} X
  proof: by
  dsimp [HasCardinalLT] at h
  rw [← Cardinal.lift_lt.{_]; rw [v + 1}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift] at h
  simpa only [Cardinal.small_iff_lift_mk_lt_univ] using h.trans (Cardinal.lift_lt_univ' κ)

中文:
引理 small
  结论: Small.{v} X
  证明: by
  dsimp [HasCardinalLT] at h
  rw [← Cardinal.lift_lt.{_]; rw [v + 1}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift] at h
  simpa only [Cardinal.small_iff_lift_mk_lt_univ] using h.trans (Cardinal.lift_lt_univ' κ)

Depends on / 依赖: Cardinal, Cardinal.lift_lift, Cardinal.lift_lt, Cardinal.lift_lt_univ, Cardinal.small_iff_lift_mk_lt_univ, HasCardinalLT, h.trans, lift_lift, lift_lt, lift_lt_univ, small_iff_lift_mk_lt_univ
-/
lemma small : Small.{v} X := by
  dsimp [HasCardinalLT] at h
  rw [← Cardinal.lift_lt.{_]; rw [v + 1}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift] at h
  simpa only [Cardinal.small_iff_lift_mk_lt_univ] using h.trans (Cardinal.lift_lt_univ' κ)

/--
lemma `of_le` / 引理 `of_le`

English:
lemma of_le
  given: {κ' : Cardinal.{v}} (hκ' : κ <= κ')
  proof: lt_of_lt_of_le h (by simpa only [Cardinal.lift_le] using hκ')

中文:
引理 of_le
  条件: {κ' : 基数.{v}} (hκ' : κ <= κ')
  证明: lt_of_lt_of_le h (by simpa only [Cardinal.lift_le] using hκ')

Depends on / 依赖: Cardinal, Cardinal.lift_le, lift_le, lt_of_lt_of_le
-/
lemma of_le {κ' : Cardinal.{v}} (hκ' : κ <= κ') :
    HasCardinalLT X κ' :=
  lt_of_lt_of_le h (by simpa only [Cardinal.lift_le] using hκ')

variable {Y : Type u'}

/--
lemma `of_injective` / 引理 `of_injective`

English:
lemma of_injective
  given: (f : Y -> X) (hf : Function.Injective f)
  proof: by
  dsimp [HasCardinalLT] at h ⊢
  rw [← Cardinal.lift_lt.{_]; rw [u}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift]
  rw [← Cardinal.lift_lt.{_]; rw [u'}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift] at h
  exact lt_of_le_of_lt (Cardinal.mk_le_of_injective
    (Function.Injective.comp ULi

中文:
引理 of_injective
  条件: (f : Y -> X) (hf : 函数.单射 f)
  证明: by
  dsimp [HasCardinalLT] at h ⊢
  rw [← Cardinal.lift_lt.{_]; rw [u}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift]
  rw [← Cardinal.lift_lt.{_]; rw [u'}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift] at h
  exact lt_of_le_of_lt (Cardinal.mk_le_of_injective
    (Function.Injective.comp ULi

Depends on / 依赖: Cardinal, Cardinal.lift_lift, Cardinal.lift_lt, Cardinal.mk_le_of_injective, Function, Function.Injective.comp, HasCardinalLT, Injective, ULift.down_injective, ULift.up_injective, down_injective, lift_lift, lift_lt, lt_of_le_of_lt, mk_le_of_injective, up_injective
-/
lemma of_injective (f : Y -> X) (hf : Function.Injective f) :
    HasCardinalLT Y κ := by
  dsimp [HasCardinalLT] at h ⊢
  rw [← Cardinal.lift_lt.{_]; rw [u}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift]
  rw [← Cardinal.lift_lt.{_]; rw [u'}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift] at h
  exact lt_of_le_of_lt (Cardinal.mk_le_of_injective
    (Function.Injective.comp ULift.up_injective
      (Function.Injective.comp hf ULift.down_injective))) h

/--
lemma `of_surjective` / 引理 `of_surjective`

English:
lemma of_surjective
  given: (f : X -> Y) (hf : Function.Surjective f)
  proof: by
  dsimp [HasCardinalLT] at h ⊢
  rw [← Cardinal.lift_lt.{_]; rw [u}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift]
  rw [← Cardinal.lift_lt.{_]; rw [u'}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift] at h
  exact lt_of_le_of_lt (Cardinal.mk_le_of_surjective
    (Function.Surjective.comp U

中文:
引理 of_surjective
  条件: (f : X -> Y) (hf : 函数.满射 f)
  证明: by
  dsimp [HasCardinalLT] at h ⊢
  rw [← Cardinal.lift_lt.{_]; rw [u}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift]
  rw [← Cardinal.lift_lt.{_]; rw [u'}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift] at h
  exact lt_of_le_of_lt (Cardinal.mk_le_of_surjective
    (Function.Surjective.comp U

Depends on / 依赖: Cardinal, Cardinal.lift_lift, Cardinal.lift_lt, Cardinal.mk_le_of_surjective, Function, Function.Surjective.comp, HasCardinalLT, Surjective, ULift.down_surjective, ULift.up_surjective, down_surjective, lift_lift, lift_lt, lt_of_le_of_lt, mk_le_of_surjective, up_surjective
-/
lemma of_surjective (f : X -> Y) (hf : Function.Surjective f) :
    HasCardinalLT Y κ := by
  dsimp [HasCardinalLT] at h ⊢
  rw [← Cardinal.lift_lt.{_]; rw [u}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift]
  rw [← Cardinal.lift_lt.{_]; rw [u'}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift] at h
  exact lt_of_le_of_lt (Cardinal.mk_le_of_surjective
    (Function.Surjective.comp ULift.up_surjective (Function.Surjective.comp hf
      ULift.down_surjective))) h

end

end HasCardinalLT

/--
lemma `hasCardinalLT_iff_of_equiv` / 引理 `hasCardinalLT_iff_of_equiv`

English:
lemma hasCardinalLT_iff_of_equiv
  given: {X : Type u} {Y : Type u'} (e : X ≃ Y) (κ : Cardinal.{v})
  proof: ⟨fun h => h.of_injective _ e.symm.injective,
    fun h => h.of_injective _ e.injective⟩

@[simp]

中文:
引理 hasCardinalLT_iff_of_equiv
  条件: {X : 类型u} {Y : 类型u'} (e : X ≃ Y) (κ : 基数.{v})
  证明: ⟨fun h => h.of_injective _ e.symm.injective,
    fun h => h.of_injective _ e.injective⟩

@[simp]

Depends on / 依赖: Decidable, Iff.rfl, Subtype, Subtype.val, continuous_subtype_val, continuous_subtype_val.restrictPreimage, decidable_of_iff, e.injective, e.symm.injective, h.of_injective, injective, of_injective, piecewise, piecewise_apply_left, restrictPreimage
-/
lemma hasCardinalLT_iff_of_equiv {X : Type u} {Y : Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) :
    HasCardinalLT X κ ↔ HasCardinalLT Y κ :=
  ⟨fun h => h.of_injective _ e.symm.injective,
    fun h => h.of_injective _ e.injective⟩

@[simp]
/--
lemma `hasCardinalLT_aleph0_iff` / 引理 `hasCardinalLT_aleph0_iff`

English:
lemma hasCardinalLT_aleph0_iff
  given: (X : Type u)
  proof: by
  simpa [HasCardinalLT] using Cardinal.mk_lt_aleph0_iff

中文:
引理 hasCardinalLT_aleph0_iff
  条件: (X : 类型u)
  证明: by
  simpa [HasCardinalLT] using Cardinal.mk_lt_aleph0_iff

Depends on / 依赖: Cardinal, Cardinal.mk_lt_aleph0_iff, Decidable, HasCardinalLT, Iff.rfl, Subtype, Subtype.val, continuous_subtype_val, continuous_subtype_val.restrictPreimage, decidable_of_iff, mk_lt_aleph0_iff, piecewise, piecewise_apply_right, restrictPreimage
-/
lemma hasCardinalLT_aleph0_iff (X : Type u) :
    HasCardinalLT X Cardinal.aleph0.{v} ↔ Finite X := by
  simpa [HasCardinalLT] using Cardinal.mk_lt_aleph0_iff

/--
lemma `hasCardinalLT_of_finite` / 引理 `hasCardinalLT_of_finite`

English:
lemma hasCardinalLT_of_finite
  proof: .of_le (by rwa [hasCardinalLT_aleph0_iff]) hκ

@[simp]

中文:
引理 hasCardinalLT_of_finite
  证明: .of_le (by rwa [hasCardinalLT_aleph0_iff]) hκ

@[simp]

Depends on / 依赖: hasCardinalLT_aleph0_iff, of_le
-/
lemma hasCardinalLT_of_finite
    (X : Type*) [Finite X] (κ : Cardinal) (hκ : Cardinal.aleph0 <= κ) :
    HasCardinalLT X κ :=
  .of_le (by rwa [hasCardinalLT_aleph0_iff]) hκ

@[simp]
/--
lemma `hasCardinalLT_lift_iff` / 引理 `hasCardinalLT_lift_iff`

English:
lemma hasCardinalLT_lift_iff
  given: (X : Type v) (κ : Cardinal.{w})
  proof: by
  simp [HasCardinalLT, ← (Cardinal.lift_strictMono.{max v w, max u}).lt_iff_lt]

@[simp]

中文:
引理 hasCardinalLT_lift_iff
  条件: (X : 类型v) (κ : 基数.{w})
  证明: by
  simp [HasCardinalLT, ← (Cardinal.lift_strictMono.{max v w, max u}).lt_iff_lt]

@[simp]

Depends on / 依赖: Cardinal, Cardinal.lift_strictMono, HasCardinalLT, lift_strictMono, lt_iff_lt
-/
lemma hasCardinalLT_lift_iff (X : Type v) (κ : Cardinal.{w}) :
    HasCardinalLT X (Cardinal.lift.{u} κ) ↔ HasCardinalLT X κ := by
  simp [HasCardinalLT, ← (Cardinal.lift_strictMono.{max v w, max u}).lt_iff_lt]

@[simp]
/--
lemma `hasCardinalLT_ulift_iff` / 引理 `hasCardinalLT_ulift_iff`

English:
lemma hasCardinalLT_ulift_iff
  given: (X : Type v) (κ : Cardinal.{w})
  proof: hasCardinalLT_iff_of_equiv Equiv.ulift κ

中文:
引理 hasCardinalLT_ulift_iff
  条件: (X : 类型v) (κ : 基数.{w})
  证明: hasCardinalLT_iff_of_equiv Equiv.ulift κ

Depends on / 依赖: Equiv.ulift, hasCardinalLT_iff_of_equiv
-/
lemma hasCardinalLT_ulift_iff (X : Type v) (κ : Cardinal.{w}) :
    HasCardinalLT (ULift.{u} X) κ ↔ HasCardinalLT X κ :=
  hasCardinalLT_iff_of_equiv Equiv.ulift κ

/--
lemma `hasCardinalLT_sum_iff` / 引理 `hasCardinalLT_sum_iff`

English:
lemma hasCardinalLT_sum_iff
  statement: (X : Type u) (Y : Type u') (κ : Cardinal.{w})
  proof: by
  constructor
  · intro h
    exact ⟨h.of_injective _ Sum.inl_injective,
      h.of_injective _ Sum.inr_injective⟩
  · rintro ⟨hX, hY⟩
    dsimp [HasCardinalLT] at hX hY ⊢
    rw [← Cardinal.lift_lt.{_]; rw [u'}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift] at hX
    rw [← Cardinal.lift_lt.{

中文:
引理 hasCardinalLT_sum_iff
  结论: (X : 类型u) (Y : 类型u') (κ : 基数.{w})
  证明: by
  constructor
  · intro h
    exact ⟨h.of_injective _ Sum.inl_injective,
      h.of_injective _ Sum.inr_injective⟩
  · rintro ⟨hX, hY⟩
    dsimp [HasCardinalLT] at hX hY ⊢
    rw [← Cardinal.lift_lt.{_]; rw [u'}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift] at hX
    rw [← Cardinal.lift_lt.{

Depends on / 依赖: Cardinal, Cardinal.add_lt_of_lt, Cardinal.lift_add, Cardinal.lift_lift, Cardinal.lift_lt, Cardinal.mk_sum, HasCardinalLT, Sum.inl_injective, Sum.inr_injective, add_lt_of_lt, h.of_injective, inl_injective, inr_injective, lift_add, lift_lift, lift_lt, mk_sum, of_injective
-/
lemma hasCardinalLT_sum_iff (X : Type u) (Y : Type u') (κ : Cardinal.{w})
    (hκ : Cardinal.aleph0 <= κ) :
    HasCardinalLT (X oplus Y) κ ↔ HasCardinalLT X κ ∧ HasCardinalLT Y κ := by
  constructor
  · intro h
    exact ⟨h.of_injective _ Sum.inl_injective,
      h.of_injective _ Sum.inr_injective⟩
  · rintro ⟨hX, hY⟩
    dsimp [HasCardinalLT] at hX hY ⊢
    rw [← Cardinal.lift_lt.{_]; rw [u'}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift] at hX
    rw [← Cardinal.lift_lt.{_]; rw [u}]; rw [Cardinal.lift_lift]; rw [Cardinal.lift_lift] at hY
    simp only [Cardinal.mk_sum, Cardinal.lift_add, Cardinal.lift_lift]
    exact Cardinal.add_lt_of_lt (by simpa using hκ) hX hY

/--
lemma `hasCardinalLT_option_iff` / 引理 `hasCardinalLT_option_iff`

English:
lemma hasCardinalLT_option_iff
  statement: (X : Type u) (κ : Cardinal.{w})
  proof: by
  rw [hasCardinalLT_iff_of_equiv (Equiv.optionEquivSumPUnit.{0} X)]; rw [hasCardinalLT_sum_iff _ _ _ hκ]; rw [and_iff_left_iff_imp]
  refine fun _ => HasCardinalLT.of_le ?_ hκ
  rw [hasCardinalLT_aleph0_iff]
  infer_instance

中文:
引理 hasCardinalLT_option_iff
  结论: (X : 类型u) (κ : 基数.{w})
  证明: by
  rw [hasCardinalLT_iff_of_equiv (Equiv.optionEquivSumPUnit.{0} X)]; rw [hasCardinalLT_sum_iff _ _ _ hκ]; rw [and_iff_left_iff_imp]
  refine fun _ => HasCardinalLT.of_le ?_ hκ
  rw [hasCardinalLT_aleph0_iff]
  infer_instance

Depends on / 依赖: Equiv.optionEquivSumPUnit, HasCardinalLT, HasCardinalLT.of_le, and_iff_left_iff_imp, hasCardinalLT_aleph0_iff, hasCardinalLT_iff_of_equiv, hasCardinalLT_sum_iff, infer_instance, of_le, optionEquivSumPUnit
-/
lemma hasCardinalLT_option_iff (X : Type u) (κ : Cardinal.{w})
    (hκ : Cardinal.aleph0 <= κ) :
    HasCardinalLT (Option X) κ ↔ HasCardinalLT X κ := by
  rw [hasCardinalLT_iff_of_equiv (Equiv.optionEquivSumPUnit.{0} X)]; rw [hasCardinalLT_sum_iff _ _ _ hκ]; rw [and_iff_left_iff_imp]
  refine fun _ => HasCardinalLT.of_le ?_ hκ
  rw [hasCardinalLT_aleph0_iff]
  infer_instance

/--
lemma `hasCardinalLT_subtype_max` / 引理 `hasCardinalLT_subtype_max`

English:
lemma hasCardinalLT_subtype_max
  proof: by
  have : HasCardinalLT (Subtype P₁ oplus Subtype P₂) κ := by
    rw [hasCardinalLT_sum_iff _ _ _ hκ]
    exact ⟨h₁, h₂⟩
  refine this.of_surjective (Sum.elim (fun x => ⟨x.1, Or.inl x.2⟩)
    (fun x => ⟨x.1, Or.inr x.2⟩)) ?_
  rintro ⟨x, hx | hx⟩
  · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
  · exact ⟨Sum.inr

中文:
引理 hasCardinalLT_subtype_max
  证明: by
  have : HasCardinalLT (Subtype P₁ oplus Subtype P₂) κ := by
    rw [hasCardinalLT_sum_iff _ _ _ hκ]
    exact ⟨h₁, h₂⟩
  refine this.of_surjective (Sum.elim (fun x => ⟨x.1, Or.inl x.2⟩)
    (fun x => ⟨x.1, Or.inr x.2⟩)) ?_
  rintro ⟨x, hx | hx⟩
  · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
  · exact ⟨Sum.inr

Depends on / 依赖: HasCardinalLT, Or.inl, Or.inr, Subtype, Sum.elim, Sum.inl, Sum.inr, hasCardinalLT_sum_iff, of_surjective, this.of_surjective
-/
lemma hasCardinalLT_subtype_max
    {X : Type*} {P₁ P₂ : X -> Prop} {κ : Cardinal} (hκ : Cardinal.aleph0 <= κ)
    (h₁ : HasCardinalLT (Subtype P₁) κ) (h₂ : HasCardinalLT (Subtype P₂) κ) :
    HasCardinalLT (Subtype (P₁ ⊔ P₂)) κ := by
  have : HasCardinalLT (Subtype P₁ oplus Subtype P₂) κ := by
    rw [hasCardinalLT_sum_iff _ _ _ hκ]
    exact ⟨h₁, h₂⟩
  refine this.of_surjective (Sum.elim (fun x => ⟨x.1, Or.inl x.2⟩)
    (fun x => ⟨x.1, Or.inr x.2⟩)) ?_
  rintro ⟨x, hx | hx⟩
  · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
  · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩

/--
lemma `hasCardinalLT_union` / 引理 `hasCardinalLT_union`

English:
lemma hasCardinalLT_union
  proof: hasCardinalLT_subtype_max hκ h₁ h₂

中文:
引理 hasCardinalLT_union
  证明: hasCardinalLT_subtype_max hκ h₁ h₂

Depends on / 依赖: hasCardinalLT_subtype_max
-/
lemma hasCardinalLT_union
    {X : Type*} {S₁ S₂ : Set X} {κ : Cardinal} (hκ : Cardinal.aleph0 <= κ)
    (h₁ : HasCardinalLT S₁ κ) (h₂ : HasCardinalLT S₂ κ) :
    HasCardinalLT (S₁ union S₂ : Set _) κ :=
  hasCardinalLT_subtype_max hκ h₁ h₂

/--
lemma `hasCardinalLT_sigma'` / 引理 `hasCardinalLT_sigma'`

English:
lemma hasCardinalLT_sigma'
  statement: {ι : Type w} (α : ι -> Type w) (κ : Cardinal.{w}) [Fact κ.IsRegular]
  proof: by
  simp only [hasCardinalLT_iff_cardinal_mk_lt] at hι hα ⊢
  rw [Cardinal.mk_sigma]
  exact Cardinal.sum_lt_lift_of_isRegular.{w, w} Fact.out (by simpa) hα

中文:
引理 hasCardinalLT_sigma'
  结论: {ι : 类型 w} (α : ι -> 类型 w) (κ : 基数.{w}) [Fact κ.是正则]
  证明: by
  simp only [hasCardinalLT_iff_cardinal_mk_lt] at hι hα ⊢
  rw [Cardinal.mk_sigma]
  exact Cardinal.sum_lt_lift_of_isRegular.{w, w} Fact.out (by simpa) hα

Depends on / 依赖: Cardinal, Cardinal.mk_sigma, Cardinal.sum_lt_lift_of_isRegular, Fact.out, hasCardinalLT_iff_cardinal_mk_lt, mk_sigma, sum_lt_lift_of_isRegular
-/
lemma hasCardinalLT_sigma' {ι : Type w} (α : ι -> Type w) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hα : forall i, HasCardinalLT (α i) κ) :
    HasCardinalLT (Σ i, α i) κ := by
  simp only [hasCardinalLT_iff_cardinal_mk_lt] at hι hα ⊢
  rw [Cardinal.mk_sigma]
  exact Cardinal.sum_lt_lift_of_isRegular.{w, w} Fact.out (by simpa) hα

/--
lemma `hasCardinalLT_sigma` / 引理 `hasCardinalLT_sigma`

English:
lemma hasCardinalLT_sigma
  statement: {ι : Type u} (α : ι -> Type v) (κ : Cardinal.{w}) [Fact κ.IsRegular]
  proof: by
  have : Fact (Cardinal.lift.{max u v} κ).IsRegular := ⟨Cardinal.IsRegular.lift Fact.out⟩
  have := hasCardinalLT_sigma'
    (fun (i : ULift.{max v w} ι) => ULift.{max u w} (α (ULift.down i)))
    (Cardinal.lift.{max u v} κ) (by simpa)
    (fun i => by simpa using hα (ULift.down i))
  rw [hasCard

中文:
引理 hasCardinalLT_sigma
  结论: {ι : 类型u} (α : ι -> 类型v) (κ : 基数.{w}) [Fact κ.是正则]
  证明: by
  have : Fact (Cardinal.lift.{max u v} κ).IsRegular := ⟨Cardinal.IsRegular.lift Fact.out⟩
  have := hasCardinalLT_sigma'
    (fun (i : ULift.{max v w} ι) => ULift.{max u w} (α (ULift.down i)))
    (Cardinal.lift.{max u v} κ) (by simpa)
    (fun i => by simpa using hα (ULift.down i))
  rw [hasCard

Depends on / 依赖: Cardinal, Cardinal.IsRegular.lift, Cardinal.lift, Fact.out, IsRegular, ULift.down, ULift.up, hasCardinalLT_lift_iff, hasCardinalLT_sigma, of_surjective, this.of_surjective
-/
lemma hasCardinalLT_sigma {ι : Type u} (α : ι -> Type v) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hα : forall i, HasCardinalLT (α i) κ) :
    HasCardinalLT (Σ i, α i) κ := by
  have : Fact (Cardinal.lift.{max u v} κ).IsRegular := ⟨Cardinal.IsRegular.lift Fact.out⟩
  have := hasCardinalLT_sigma'
    (fun (i : ULift.{max v w} ι) => ULift.{max u w} (α (ULift.down i)))
    (Cardinal.lift.{max u v} κ) (by simpa)
    (fun i => by simpa using hα (ULift.down i))
  rw [hasCardinalLT_lift_iff] at this
  exact this.of_surjective (fun ⟨i, a⟩ => ⟨ULift.down i, ULift.down a⟩)
    (fun ⟨i, a⟩ => ⟨⟨ULift.up i, ULift.up a⟩, rfl⟩)

/--
lemma `hasCardinalLT_subtype_iSup` / 引理 `hasCardinalLT_subtype_iSup`

English:
lemma hasCardinalLT_subtype_iSup
  proof: (hasCardinalLT_sigma (fun i => Subtype (P i)) κ hι hP).of_surjective
    (fun ⟨i, x, hx⟩ => ⟨x, by simp only [iSup_apply, iSup_Prop_eq]; exact ⟨i, hx⟩⟩) (by
    rintro ⟨_, h⟩
    simp only [iSup_apply, iSup_Prop_eq] at h
    obtain ⟨i, hi⟩ := h
    exact ⟨⟨i, _, hi⟩, rfl⟩)

中文:
引理 hasCardinalLT_subtype_iSup
  证明: (hasCardinalLT_sigma (fun i => Subtype (P i)) κ hι hP).of_surjective
    (fun ⟨i, x, hx⟩ => ⟨x, by simp only [iSup_apply, iSup_Prop_eq]; exact ⟨i, hx⟩⟩) (by
    rintro ⟨_, h⟩
    simp only [iSup_apply, iSup_Prop_eq] at h
    obtain ⟨i, hi⟩ := h
    exact ⟨⟨i, _, hi⟩, rfl⟩)

Depends on / 依赖: Subtype, hasCardinalLT_sigma, iSup_Prop_eq, iSup_apply, of_surjective
-/
lemma hasCardinalLT_subtype_iSup
    {ι : Type*} {X : Type*} (P : ι -> X -> Prop) {κ : Cardinal} [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hP : forall i, HasCardinalLT (Subtype (P i)) κ) :
    HasCardinalLT (Subtype (⨆ i, P i)) κ :=
  (hasCardinalLT_sigma (fun i => Subtype (P i)) κ hι hP).of_surjective
    (fun ⟨i, x, hx⟩ => ⟨x, by simp only [iSup_apply, iSup_Prop_eq]; exact ⟨i, hx⟩⟩) (by
    rintro ⟨_, h⟩
    simp only [iSup_apply, iSup_Prop_eq] at h
    obtain ⟨i, hi⟩ := h
    exact ⟨⟨i, _, hi⟩, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasCardinalLT_iUnion` / 引理 `hasCardinalLT_iUnion`

English:
lemma hasCardinalLT_iUnion
  proof: by
  convert! show HasCardinalLT (Set.ofPred ((⨆ i, S i))) κ from hasCardinalLT_subtype_iSup S hι hS
  aesop

中文:
引理 hasCardinalLT_iUnion
  证明: by
  convert! show HasCardinalLT (Set.ofPred ((⨆ i, S i))) κ from hasCardinalLT_subtype_iSup S hι hS
  aesop

Depends on / 依赖: HasCardinalLT, Set.ofPred, convert, hasCardinalLT_subtype_iSup, ofPred
-/
lemma hasCardinalLT_iUnion
    {ι : Type*} {X : Type*} (S : ι -> Set X) {κ : Cardinal} [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hS : forall i, HasCardinalLT (S i) κ) :
    HasCardinalLT (⋃ i, S i) κ := by
  convert! show HasCardinalLT (Set.ofPred ((⨆ i, S i))) κ from hasCardinalLT_subtype_iSup S hι hS
  aesop

/--
lemma `hasCardinalLT_prod'` / 引理 `hasCardinalLT_prod'`

English:
lemma hasCardinalLT_prod'
  statement: {T₁ T₂ : Type w} {κ : Cardinal.{w}} (hκ : Cardinal.aleph0 <= κ)
  proof: by
  rw [hasCardinalLT_iff_cardinal_mk_lt] at h₁ h₂ ⊢
  simpa using Cardinal.mul_lt_of_lt hκ h₁ h₂

中文:
引理 hasCardinalLT_prod'
  结论: {T₁ T₂ : 类型 w} {κ : 基数.{w}} (hκ : 基数.aleph0 <= κ)
  证明: by
  rw [hasCardinalLT_iff_cardinal_mk_lt] at h₁ h₂ ⊢
  simpa using Cardinal.mul_lt_of_lt hκ h₁ h₂

Depends on / 依赖: Cardinal, Cardinal.mul_lt_of_lt, hasCardinalLT_iff_cardinal_mk_lt, mul_lt_of_lt
-/
lemma hasCardinalLT_prod' {T₁ T₂ : Type w} {κ : Cardinal.{w}} (hκ : Cardinal.aleph0 <= κ)
    (h₁ : HasCardinalLT T₁ κ) (h₂ : HasCardinalLT T₂ κ) :
    HasCardinalLT (T₁ × T₂) κ := by
  rw [hasCardinalLT_iff_cardinal_mk_lt] at h₁ h₂ ⊢
  simpa using Cardinal.mul_lt_of_lt hκ h₁ h₂

/--
lemma `hasCardinalLT_prod` / 引理 `hasCardinalLT_prod`

English:
lemma hasCardinalLT_prod
  statement: {T₁ : Type u} {T₂ : Type u'}
  proof: by
  have := hasCardinalLT_prod' (T₁ := ULift.{max u' w} T₁) (T₂ := ULift.{max u w} T₂)
    (κ := Cardinal.lift.{max u u'} κ) (by simpa) (by simpa) (by simpa)
  simp only [hasCardinalLT_lift_iff] at this
  exact this.of_surjective (fun ⟨x₁, x₂⟩ => ⟨ULift.down x₁, ULift.down x₂⟩) (fun ⟨x₁, x₂⟩ =>
   

中文:
引理 hasCardinalLT_prod
  结论: {T₁ : 类型u} {T₂ : 类型u'}
  证明: by
  have := hasCardinalLT_prod' (T₁ := ULift.{max u' w} T₁) (T₂ := ULift.{max u w} T₂)
    (κ := Cardinal.lift.{max u u'} κ) (by simpa) (by simpa) (by simpa)
  simp only [hasCardinalLT_lift_iff] at this
  exact this.of_surjective (fun ⟨x₁, x₂⟩ => ⟨ULift.down x₁, ULift.down x₂⟩) (fun ⟨x₁, x₂⟩ =>
   

Depends on / 依赖: Cardinal, Cardinal.lift, ULift.down, ULift.up, hasCardinalLT_lift_iff, hasCardinalLT_prod, of_surjective, this.of_surjective
-/
lemma hasCardinalLT_prod {T₁ : Type u} {T₂ : Type u'}
    {κ : Cardinal.{w}} (hκ : Cardinal.aleph0 <= κ)
    (h₁ : HasCardinalLT T₁ κ) (h₂ : HasCardinalLT T₂ κ) :
    HasCardinalLT (T₁ × T₂) κ := by
  have := hasCardinalLT_prod' (T₁ := ULift.{max u' w} T₁) (T₂ := ULift.{max u w} T₂)
    (κ := Cardinal.lift.{max u u'} κ) (by simpa) (by simpa) (by simpa)
  simp only [hasCardinalLT_lift_iff] at this
  exact this.of_surjective (fun ⟨x₁, x₂⟩ => ⟨ULift.down x₁, ULift.down x₂⟩) (fun ⟨x₁, x₂⟩ =>
    ⟨⟨ULift.up x₁, ULift.up x₂⟩, rfl⟩)

namespace HasCardinalLT

/--
lemma `exists_regular_cardinal` / 引理 `exists_regular_cardinal`

English:
lemma exists_regular_cardinal
  given: (X : Type u) [Small.{w} X]
  proof: ⟨Order.succ (max (Cardinal.mk (Shrink.{w} X)) .aleph0),
    Cardinal.isRegular_succ (le_max_right _ _), by
      simp [hasCardinalLT_iff_of_equiv (equivShrink.{w} X),
        hasCardinalLT_iff_cardinal_mk_lt]⟩

中文:
引理 存在_regular_cardinal
  条件: (X : 类型u) [Small.{w} X]
  证明: ⟨Order.succ (max (Cardinal.mk (Shrink.{w} X)) .aleph0),
    Cardinal.isRegular_succ (le_max_right _ _), by
      simp [hasCardinalLT_iff_of_equiv (equivShrink.{w} X),
        hasCardinalLT_iff_cardinal_mk_lt]⟩

Depends on / 依赖: Cardinal, Cardinal.isRegular_succ, Cardinal.mk, Order.succ, Shrink, aleph0, equivShrink, hasCardinalLT_iff_cardinal_mk_lt, hasCardinalLT_iff_of_equiv, isRegular_succ, le_max_right
-/
lemma exists_regular_cardinal (X : Type u) [Small.{w} X] :
    exists (κ : Cardinal.{w}), κ.IsRegular ∧ HasCardinalLT X κ :=
  ⟨Order.succ (max (Cardinal.mk (Shrink.{w} X)) .aleph0),
    Cardinal.isRegular_succ (le_max_right _ _), by
      simp [hasCardinalLT_iff_of_equiv (equivShrink.{w} X),
        hasCardinalLT_iff_cardinal_mk_lt]⟩

/--
lemma `exists_regular_cardinal_forall` / 引理 `exists_regular_cardinal_forall`

English:
lemma exists_regular_cardinal_forall
  statement: {ι : Type v} (X : ι -> Type u) [Small.{w} ι]
  proof: by
  obtain ⟨κ, hκ, h⟩ := exists_regular_cardinal.{w} (Sigma X)
  exact ⟨κ, hκ, fun i => h.of_injective _ sigma_mk_injective⟩

中文:
引理 存在_regular_cardinal_对任意
  结论: {ι : 类型v} (X : ι -> 类型u) [Small.{w} ι]
  证明: by
  obtain ⟨κ, hκ, h⟩ := exists_regular_cardinal.{w} (Sigma X)
  exact ⟨κ, hκ, fun i => h.of_injective _ sigma_mk_injective⟩

Depends on / 依赖: exists_regular_cardinal, h.of_injective, of_injective, sigma_mk_injective
-/
lemma exists_regular_cardinal_forall {ι : Type v} (X : ι -> Type u) [Small.{w} ι]
    [forall i, Small.{w} (X i)] :
    exists (κ : Cardinal.{w}), κ.IsRegular ∧ forall (i : ι), HasCardinalLT (X i) κ := by
  obtain ⟨κ, hκ, h⟩ := exists_regular_cardinal.{w} (Sigma X)
  exact ⟨κ, hκ, fun i => h.of_injective _ sigma_mk_injective⟩

end HasCardinalLT
