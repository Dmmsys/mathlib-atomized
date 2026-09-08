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

/-- The property that the cardinal of a type `X : Type u` is less than `κ : Cardinal.{v}`. -/
/-
**HasCardinalLT** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasCardinalLT (X : Type u) (κ : Cardinal.{v}) : Prop
参数：X : Type u；κ : Cardinal.{v}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that the cardinal of a type `X : Type u` is less than `κ : Cardinal
.{v}`.
-/
def HasCardinalLT (X : Type u) (κ : Cardinal.{v}) : Prop :=
  Cardinal.lift.{v} (Cardinal.mk X) < Cardinal.lift κ
/-
**hasCardinalLT_iff_cardinal_mk_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_iff_cardinal_mk_lt (X : Type u) (κ : Cardinal.{u}) : HasCard
inalLT X κ ↔ Cardinal.mk X < κ
参数：X : Type u；κ : Cardinal.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma hasCardinalLT_iff_cardinal_mk_lt (X : Type u) (κ : Cardinal.{u}) :
    HasCardinalLT X κ ↔ Cardinal.mk X < κ := by
  simp [HasCardinalLT]

namespace HasCardinalLT

section

variable {X : Type u} {κ : Cardinal.{v}} (h : HasCardinalLT X κ)

include h

/-
**HasCardinalLT.small** 是 Mathlib 中的一个引理，位于命名空间 `HasCardinalLT`。
形式化陈述：small : Small.{v} X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Cardinal.lift_lt_univ'`：lift_lt_univ' (c : Cardinal) : lift.{max (u + 1)
 v, u} c < univ.{u, v}
-/
lemma small : Small.{v} X := by
  dsimp [HasCardinalLT] at h
  rw [← Cardinal.lift_lt.{_, v + 1}, Cardinal.lift_lift, Cardinal.lift_lift] at h
  simpa only [Cardinal.small_iff_lift_mk_lt_univ] using h.trans (Cardinal.lift_lt_univ' κ)
/-
**HasCardinalLT.of_le** 是 Mathlib 中的一个引理，位于命名空间 `HasCardinalLT`。
形式化陈述：of_le {κ' : Cardinal.{v}} (hκ' : κ <= κ') : HasCardinalLT X κ'
参数：hκ' : κ <= κ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
lemma of_le {κ' : Cardinal.{v}} (hκ' : κ ≤ κ') :
    HasCardinalLT X κ' :=
  lt_of_lt_of_le h (by simpa only [Cardinal.lift_le] using hκ')

variable {Y : Type u'}
/-
**HasCardinalLT.of_injective** 是 Mathlib 中的一个引理，位于命名空间 `HasCardinalLT`。
形式化陈述：of_injective (f : Y -> X) (hf : Function.Injective f) : HasCardinalLT Y κ
参数：f : Y -> X；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Cardinal.mk_le_of_injective`：mk_le_of_injective {α β : Type u} {f : α ->
 β} (hf : Injective f) : #α <= #β
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `ULift.up_injective`：up_injective : Injective (@up α)
· 使用定理 `ULift.down_injective`：∀ {α : Type u_1}, Function.Injective ULift.down
-/
lemma of_injective (f : Y → X) (hf : Function.Injective f) :
    HasCardinalLT Y κ := by
  dsimp [HasCardinalLT] at h ⊢
  rw [← Cardinal.lift_lt.{_, u}, Cardinal.lift_lift, Cardinal.lift_lift]
  rw [← Cardinal.lift_lt.{_, u'}, Cardinal.lift_lift, Cardinal.lift_lift] at h
  exact lt_of_le_of_lt (Cardinal.mk_le_of_injective
    (Function.Injective.comp ULift.up_injective
      (Function.Injective.comp hf ULift.down_injective))) h
/-
**HasCardinalLT.of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `HasCardinalLT`。
形式化陈述：of_surjective (f : X -> Y) (hf : Function.Surjective f) : HasCardinalLT Y 
κ
参数：f : X -> Y；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Cardinal.mk_le_of_surjective`：mk_le_of_surjective {α β : Type u} {f : α 
-> β} (hf : Surjective f) : #β <= #α
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `ULift.up_surjective`：up_surjective : Surjective (@up α)
· 使用定理 `ULift.down_surjective`：down_surjective : Surjective (@down α)
-/
lemma of_surjective (f : X → Y) (hf : Function.Surjective f) :
    HasCardinalLT Y κ := by
  dsimp [HasCardinalLT] at h ⊢
  rw [← Cardinal.lift_lt.{_, u}, Cardinal.lift_lift, Cardinal.lift_lift]
  rw [← Cardinal.lift_lt.{_, u'}, Cardinal.lift_lift, Cardinal.lift_lift] at h
  exact lt_of_le_of_lt (Cardinal.mk_le_of_surjective
    (Function.Surjective.comp ULift.up_surjective (Function.Surjective.comp hf
      ULift.down_surjective))) h

end

end HasCardinalLT

/-
**hasCardinalLT_iff_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_iff_of_equiv {X : Type u} {Y : Type u'} (e : X ≃ Y) (κ : Car
dinal.{v}) : HasCardinalLT X κ ↔ HasCardinalLT Y κ
参数：e : X ≃ Y；κ : Cardinal.{v}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasCardinalLT.of_injective`：of_injective (f : Y -> X) (hf : Function.Inj
ective f) : HasCardinalLT Y κ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma hasCardinalLT_iff_of_equiv {X : Type u} {Y : Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) :
    HasCardinalLT X κ ↔ HasCardinalLT Y κ :=
  ⟨fun h ↦ h.of_injective _ e.symm.injective,
    fun h ↦ h.of_injective _ e.injective⟩

@[simp]
/-
**hasCardinalLT_aleph0_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_aleph0_iff (X : Type u) : HasCardinalLT X Cardinal.aleph0.{v
} ↔ Finite X
参数：X : Type u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用引理 `Cardinal.mk_lt_aleph0_iff`：mk_lt_aleph0_iff : #α < ℵ₀ ↔ Finite α
-/
lemma hasCardinalLT_aleph0_iff (X : Type u) :
    HasCardinalLT X Cardinal.aleph0.{v} ↔ Finite X := by
  simpa [HasCardinalLT] using Cardinal.mk_lt_aleph0_iff
/-
**hasCardinalLT_of_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_of_finite (X : Type*) [Finite X] (κ : Cardinal) (hκ : Cardin
al.aleph0 <= κ) : HasCardinalLT X κ
参数：X : Type*；κ : Cardinal；hκ : Cardinal.aleph0 <= κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasCardinalLT.of_le`：of_le {κ' : Cardinal.{v}} (hκ' : κ <= κ') : HasCard
inalLT X κ'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `hasCardinalLT_aleph0_iff`：hasCardinalLT_aleph0_iff (X : Type u) : HasCar
dinalLT X Cardinal.aleph0.{v} ↔ Finite X
-/
lemma hasCardinalLT_of_finite
    (X : Type*) [Finite X] (κ : Cardinal) (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT X κ :=
  .of_le (by rwa [hasCardinalLT_aleph0_iff]) hκ

@[simp]
/-
**hasCardinalLT_lift_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_lift_iff (X : Type v) (κ : Cardinal.{w}) : HasCardinalLT X (
Cardinal.lift.{u} κ) ↔ HasCardinalLT X κ
参数：X : Type v；κ : Cardinal.{w}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Cardinal.lift_strictMono`：lift_strictMono : StrictMono lift
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma hasCardinalLT_lift_iff (X : Type v) (κ : Cardinal.{w}) :
    HasCardinalLT X (Cardinal.lift.{u} κ) ↔ HasCardinalLT X κ := by
  simp [HasCardinalLT, ← (Cardinal.lift_strictMono.{max v w, max u}).lt_iff_lt]

@[simp]
/-
**hasCardinalLT_ulift_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_ulift_iff (X : Type v) (κ : Cardinal.{w}) : HasCardinalLT (U
Lift.{u} X) κ ↔ HasCardinalLT X κ
参数：X : Type v；κ : Cardinal.{w}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasCardinalLT_iff_of_equiv`：hasCardinalLT_iff_of_equiv {X : Type u} {Y :
 Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) : HasCardinalLT X κ ↔ HasCardinalLT Y κ
-/
lemma hasCardinalLT_ulift_iff (X : Type v) (κ : Cardinal.{w}) :
    HasCardinalLT (ULift.{u} X) κ ↔ HasCardinalLT X κ :=
  hasCardinalLT_iff_of_equiv Equiv.ulift κ
/-
**hasCardinalLT_sum_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_sum_iff (X : Type u) (Y : Type u') (κ : Cardinal.{w}) (hκ : 
Cardinal.aleph0 <= κ) : HasCardinalLT (X oplus Y) κ ↔ HasCardinalLT X κ ∧ HasCar
dinalLT Y κ
参数：X : Type u；Y : Type u'；κ : Cardinal.{w}；hκ : Cardinal.aleph0 <= κ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasCardinalLT.of_injective`：of_injective (f : Y -> X) (hf : Function.Inj
ective f) : HasCardinalLT Y κ
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.add_lt_of_lt`：add_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ <= c) (h
1 : a < c) (h2 : b < c) : a + b < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
-/
lemma hasCardinalLT_sum_iff (X : Type u) (Y : Type u') (κ : Cardinal.{w})
    (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT (X ⊕ Y) κ ↔ HasCardinalLT X κ ∧ HasCardinalLT Y κ := by
  constructor
  · intro h
    exact ⟨h.of_injective _ Sum.inl_injective,
      h.of_injective _ Sum.inr_injective⟩
  · rintro ⟨hX, hY⟩
    dsimp [HasCardinalLT] at hX hY ⊢
    rw [← Cardinal.lift_lt.{_, u'}, Cardinal.lift_lift, Cardinal.lift_lift] at hX
    rw [← Cardinal.lift_lt.{_, u}, Cardinal.lift_lift, Cardinal.lift_lift] at hY
    simp only [Cardinal.mk_sum, Cardinal.lift_add, Cardinal.lift_lift]
    exact Cardinal.add_lt_of_lt (by simpa using hκ) hX hY
/-
**hasCardinalLT_option_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_option_iff (X : Type u) (κ : Cardinal.{w}) (hκ : Cardinal.al
eph0 <= κ) : HasCardinalLT (Option X) κ ↔ HasCardinalLT X κ
参数：X : Type u；κ : Cardinal.{w}；hκ : Cardinal.aleph0 <= κ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `hasCardinalLT_iff_of_equiv`：hasCardinalLT_iff_of_equiv {X : Type u} {Y :
 Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) : HasCardinalLT X κ ↔ HasCardinalLT Y κ
· 使用引理 `hasCardinalLT_sum_iff`：hasCardinalLT_sum_iff (X : Type u) (Y : Type u') 
(κ : Cardinal.{w}) (hκ : Cardinal.aleph0 <= κ) : HasCardinalLT (X oplus Y) κ ↔ H
asCardinalL…
· 使用定理 `and_iff_left_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ a) ↔ a → b
· 使用引理 `HasCardinalLT.of_le`：of_le {κ' : Cardinal.{v}} (hκ' : κ <= κ') : HasCard
inalLT X κ'
· 使用引理 `hasCardinalLT_aleph0_iff`：hasCardinalLT_aleph0_iff (X : Type u) : HasCar
dinalLT X Cardinal.aleph0.{v} ↔ Finite X
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma hasCardinalLT_option_iff (X : Type u) (κ : Cardinal.{w})
    (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT (Option X) κ ↔ HasCardinalLT X κ := by
  rw [hasCardinalLT_iff_of_equiv (Equiv.optionEquivSumPUnit.{0} X),
    hasCardinalLT_sum_iff _ _ _ hκ, and_iff_left_iff_imp]
  refine fun _ ↦ HasCardinalLT.of_le ?_ hκ
  rw [hasCardinalLT_aleph0_iff]
  infer_instance
/-
**hasCardinalLT_subtype_max** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_subtype_max {X : Type*} {P₁ P₂ : X -> Prop} {κ : Cardinal} (
hκ : Cardinal.aleph0 <= κ) (h₁ : HasCardinalLT (Subtype P₁) κ) (h₂ : HasCardinal
LT (Subtype P₂) κ) : HasCardinalLT (Subtype (P₁ ⊔ P₂)) κ
参数：hκ : Cardinal.aleph0 <= κ；h₁ : HasCardinalLT (Subtype P₁) κ；h₂ : HasCardinalL
T (Subtype P₂) κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `hasCardinalLT_sum_iff`：hasCardinalLT_sum_iff (X : Type u) (Y : Type u') 
(κ : Cardinal.{w}) (hκ : Cardinal.aleph0 <= κ) : HasCardinalLT (X oplus Y) κ ↔ H
asCardinalL…
· 使用引理 `HasCardinalLT.of_surjective`：of_surjective (f : X -> Y) (hf : Function.S
urjective f) : HasCardinalLT Y κ
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma hasCardinalLT_subtype_max
    {X : Type*} {P₁ P₂ : X → Prop} {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (h₁ : HasCardinalLT (Subtype P₁) κ) (h₂ : HasCardinalLT (Subtype P₂) κ) :
    HasCardinalLT (Subtype (P₁ ⊔ P₂)) κ := by
  have : HasCardinalLT (Subtype P₁ ⊕ Subtype P₂) κ := by
    rw [hasCardinalLT_sum_iff _ _ _ hκ]
    exact ⟨h₁, h₂⟩
  refine this.of_surjective (Sum.elim (fun x ↦ ⟨x.1, Or.inl x.2⟩)
    (fun x ↦ ⟨x.1, Or.inr x.2⟩)) ?_
  rintro ⟨x, hx | hx⟩
  · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
  · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
/-
**hasCardinalLT_union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_union {X : Type*} {S₁ S₂ : Set X} {κ : Cardinal} (hκ : Cardi
nal.aleph0 <= κ) (h₁ : HasCardinalLT S₁ κ) (h₂ : HasCardinalLT S₂ κ) : HasCardin
alLT (S₁ union S₂ : Set _) κ
参数：hκ : Cardinal.aleph0 <= κ；h₁ : HasCardinalLT S₁ κ；h₂ : HasCardinalLT S₂ κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasCardinalLT_subtype_max`：hasCardinalLT_subtype_max {X : Type*} {P₁ P₂ 
: X -> Prop} {κ : Cardinal} (hκ : Cardinal.aleph0 <= κ) (h₁ : HasCardinalLT (Sub
type P₁) κ) (h₂…
-/
lemma hasCardinalLT_union
    {X : Type*} {S₁ S₂ : Set X} {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (h₁ : HasCardinalLT S₁ κ) (h₂ : HasCardinalLT S₂ κ) :
    HasCardinalLT (S₁ ∪ S₂ : Set _) κ :=
  hasCardinalLT_subtype_max hκ h₁ h₂

/-- The particular case of `hasCardinalLT_sigma` when all the inputs are in the
same universe `w`. It is used to prove the general case. -/
/-
**hasCardinalLT_sigma'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_sigma' {ι : Type w} (α : ι -> Type w) (κ : Cardinal.{w}) [Fa
ct κ.IsRegular] (hι : HasCardinalLT ι κ) (hα : forall i, HasCardinalLT (α i) κ) 
: HasCardinalLT (Σ i, α i) κ
参数：α : ι -> Type w；κ : Cardinal.{w}；hι : HasCardinalLT ι κ；hα : forall i, HasCar
dinalLT (α i) κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
· 使用定理 `Cardinal.sum_lt_lift_of_isRegular`：sum_lt_lift_of_isRegular {ι : Type u}
 {f : ι -> Cardinal} (hc : IsRegular c) (hι : Cardinal.lift.{v, u} #ι < c) (hf :
 forall i, f i < c) : s…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
The particular case of `hasCardinalLT_sigma` when all the inputs are in the
same universe `w`. It is used to prove the general case.
-/
lemma hasCardinalLT_sigma' {ι : Type w} (α : ι → Type w) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hα : ∀ i, HasCardinalLT (α i) κ) :
    HasCardinalLT (Σ i, α i) κ := by
  simp only [hasCardinalLT_iff_cardinal_mk_lt] at hι hα ⊢
  rw [Cardinal.mk_sigma]
  exact Cardinal.sum_lt_lift_of_isRegular.{w, w} Fact.out (by simpa) hα
/-
**hasCardinalLT_sigma** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_sigma {ι : Type u} (α : ι -> Type v) (κ : Cardinal.{w}) [Fac
t κ.IsRegular] (hι : HasCardinalLT ι κ) (hα : forall i, HasCardinalLT (α i) κ) :
 HasCardinalLT (Σ i, α i) κ
参数：α : ι -> Type v；κ : Cardinal.{w}；hι : HasCardinalLT ι κ；hα : forall i, HasCar
dinalLT (α i) κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.IsRegular.lift`：∀ {κ : Cardinal.{v}}, κ.IsRegular → (Cardinal.l
ift.{u, v} κ).IsRegular
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `hasCardinalLT_sigma'`：hasCardinalLT_sigma' {ι : Type w} (α : ι -> Type w
) (κ : Cardinal.{w}) [Fact κ.IsRegular] (hι : HasCardinalLT ι κ) (hα : forall i,
 HasCardin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `HasCardinalLT.of_surjective`：of_surjective (f : X -> Y) (hf : Function.S
urjective f) : HasCardinalLT Y κ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `hasCardinalLT_lift_iff`：hasCardinalLT_lift_iff (X : Type v) (κ : Cardina
l.{w}) : HasCardinalLT X (Cardinal.lift.{u} κ) ↔ HasCardinalLT X κ
-/
lemma hasCardinalLT_sigma {ι : Type u} (α : ι → Type v) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hα : ∀ i, HasCardinalLT (α i) κ) :
    HasCardinalLT (Σ i, α i) κ := by
  have : Fact (Cardinal.lift.{max u v} κ).IsRegular := ⟨Cardinal.IsRegular.lift Fact.out⟩
  have := hasCardinalLT_sigma'
    (fun (i : ULift.{max v w} ι) ↦ ULift.{max u w} (α (ULift.down i)))
    (Cardinal.lift.{max u v} κ) (by simpa)
    (fun i ↦ by simpa using hα (ULift.down i))
  rw [hasCardinalLT_lift_iff] at this
  exact this.of_surjective (fun ⟨i, a⟩ ↦ ⟨ULift.down i, ULift.down a⟩)
    (fun ⟨i, a⟩ ↦ ⟨⟨ULift.up i, ULift.up a⟩, rfl⟩)
/-
**hasCardinalLT_subtype_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_subtype_iSup {ι : Type*} {X : Type*} (P : ι -> X -> Prop) {κ
 : Cardinal} [Fact κ.IsRegular] (hι : HasCardinalLT ι κ) (hP : forall i, HasCard
inalLT (Subtype (P i)) κ) : HasCardinalLT (Subtype (⨆ i, P i)) κ
参数：P : ι -> X -> Prop；hι : HasCardinalLT ι κ；hP : forall i, HasCardinalLT (Subty
pe (P i)) κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasCardinalLT.of_surjective`：of_surjective (f : X -> Y) (hf : Function.S
urjective f) : HasCardinalLT Y κ
· 使用引理 `hasCardinalLT_sigma`：hasCardinalLT_sigma {ι : Type u} (α : ι -> Type v) 
(κ : Cardinal.{w}) [Fact κ.IsRegular] (hι : HasCardinalLT ι κ) (hα : forall i, H
asCardina…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `iSup_Prop_eq`：iSup_Prop_eq {p : ι -> Prop} : ⨆ i, p i = exists i, p i
-/
lemma hasCardinalLT_subtype_iSup
    {ι : Type*} {X : Type*} (P : ι → X → Prop) {κ : Cardinal} [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hP : ∀ i, HasCardinalLT (Subtype (P i)) κ) :
    HasCardinalLT (Subtype (⨆ i, P i)) κ :=
  (hasCardinalLT_sigma (fun i ↦ Subtype (P i)) κ hι hP).of_surjective
    (fun ⟨i, x, hx⟩ ↦ ⟨x, by simp only [iSup_apply, iSup_Prop_eq]; exact ⟨i, hx⟩⟩) (by
    rintro ⟨_, h⟩
    simp only [iSup_apply, iSup_Prop_eq] at h
    obtain ⟨i, hi⟩ := h
    exact ⟨⟨i, _, hi⟩, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
/-
**hasCardinalLT_iUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_iUnion {ι : Type*} {X : Type*} (S : ι -> Set X) {κ : Cardina
l} [Fact κ.IsRegular] (hι : HasCardinalLT ι κ) (hS : forall i, HasCardinalLT (S 
i) κ) : HasCardinalLT (⋃ i, S i) κ
参数：S : ι -> Set X；hι : HasCardinalLT ι κ；hS : forall i, HasCardinalLT (S i) κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `iSup_Prop_eq`：iSup_Prop_eq {p : ι -> Prop} : ⨆ i, p i = exists i, p i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `hasCardinalLT_subtype_iSup`：hasCardinalLT_subtype_iSup {ι : Type*} {X : 
Type*} (P : ι -> X -> Prop) {κ : Cardinal} [Fact κ.IsRegular] (hι : HasCardinalL
T ι κ) (hP : for…
-/
lemma hasCardinalLT_iUnion
    {ι : Type*} {X : Type*} (S : ι → Set X) {κ : Cardinal} [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hS : ∀ i, HasCardinalLT (S i) κ) :
    HasCardinalLT (⋃ i, S i) κ := by
  convert! show HasCardinalLT (Set.ofPred ((⨆ i, S i))) κ from hasCardinalLT_subtype_iSup S hι hS
  aesop

/-- The particular case of `hasCardinalLT_prod` when all the inputs are in the
same universe `w`. It is used to prove the general case. -/
/-
**hasCardinalLT_prod'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_prod' {T₁ T₂ : Type w} {κ : Cardinal.{w}} (hκ : Cardinal.ale
ph0 <= κ) (h₁ : HasCardinalLT T₁ κ) (h₂ : HasCardinalLT T₂ κ) : HasCardinalLT (T
₁ × T₂) κ
参数：hκ : Cardinal.aleph0 <= κ；h₁ : HasCardinalLT T₁ κ；h₂ : HasCardinalLT T₂ κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `hasCardinalLT_iff_cardinal_mk_lt`：hasCardinalLT_iff_cardinal_mk_lt (X : 
Type u) (κ : Cardinal.{u}) : HasCardinalLT X κ ↔ Cardinal.mk X < κ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.mul_lt_of_lt`：mul_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ <= c) (h
a : a < c) (hb : b < c) : a * b < c

--- 原说明 ---
The particular case of `hasCardinalLT_prod` when all the inputs are in the
same universe `w`. It is used to prove the general case.
-/
lemma hasCardinalLT_prod' {T₁ T₂ : Type w} {κ : Cardinal.{w}} (hκ : Cardinal.aleph0 ≤ κ)
    (h₁ : HasCardinalLT T₁ κ) (h₂ : HasCardinalLT T₂ κ) :
    HasCardinalLT (T₁ × T₂) κ := by
  rw [hasCardinalLT_iff_cardinal_mk_lt] at h₁ h₂ ⊢
  simpa using Cardinal.mul_lt_of_lt hκ h₁ h₂
/-
**hasCardinalLT_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasCardinalLT_prod {T₁ : Type u} {T₂ : Type u'} {κ : Cardinal.{w}} (hκ : C
ardinal.aleph0 <= κ) (h₁ : HasCardinalLT T₁ κ) (h₂ : HasCardinalLT T₂ κ) : HasCa
rdinalLT (T₁ × T₂) κ
参数：hκ : Cardinal.aleph0 <= κ；h₁ : HasCardinalLT T₁ κ；h₂ : HasCardinalLT T₂ κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasCardinalLT_prod'`：hasCardinalLT_prod' {T₁ T₂ : Type w} {κ : Cardinal.
{w}} (hκ : Cardinal.aleph0 <= κ) (h₁ : HasCardinalLT T₁ κ) (h₂ : HasCardinalLT T
₂ κ) : Ha…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `HasCardinalLT.of_surjective`：of_surjective (f : X -> Y) (hf : Function.S
urjective f) : HasCardinalLT Y κ
-/
lemma hasCardinalLT_prod {T₁ : Type u} {T₂ : Type u'}
    {κ : Cardinal.{w}} (hκ : Cardinal.aleph0 ≤ κ)
    (h₁ : HasCardinalLT T₁ κ) (h₂ : HasCardinalLT T₂ κ) :
    HasCardinalLT (T₁ × T₂) κ := by
  have := hasCardinalLT_prod' (T₁ := ULift.{max u' w} T₁) (T₂ := ULift.{max u w} T₂)
    (κ := Cardinal.lift.{max u u'} κ) (by simpa) (by simpa) (by simpa)
  simp only [hasCardinalLT_lift_iff] at this
  exact this.of_surjective (fun ⟨x₁, x₂⟩ ↦ ⟨ULift.down x₁, ULift.down x₂⟩) (fun ⟨x₁, x₂⟩ ↦
    ⟨⟨ULift.up x₁, ULift.up x₂⟩, rfl⟩)

namespace HasCardinalLT

/-- For any `w`-small type `X`, there exists a regular cardinal `κ : Cardinal.{w}`
such that `HasCardinalLT X κ`. -/
/-
**HasCardinalLT.exists_regular_cardinal** 是 Mathlib 中的一个引理，位于命名空间 `HasCardinalLT
`。
形式化陈述：exists_regular_cardinal (X : Type u) [Small.{w} X] : exists (κ : Cardinal.
{w}), κ.IsRegular ∧ HasCardinalLT X κ
参数：X : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.isRegular_succ`：isRegular_succ {c : Cardinal} (hc : ℵ₀ <= c) : 
IsRegular (succ c)
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `hasCardinalLT_iff_of_equiv`：hasCardinalLT_iff_of_equiv {X : Type u} {Y :
 Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) : HasCardinalLT X κ ↔ HasCardinalLT Y κ
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}

--- 原说明 ---
For any `w`-small type `X`, there exists a regular cardinal `κ : Cardinal.{w}`
such that `HasCardinalLT X κ`.
-/
lemma exists_regular_cardinal (X : Type u) [Small.{w} X] :
    ∃ (κ : Cardinal.{w}), κ.IsRegular ∧ HasCardinalLT X κ :=
  ⟨Order.succ (max (Cardinal.mk (Shrink.{w} X)) .aleph0),
    Cardinal.isRegular_succ (le_max_right _ _), by
      simp [hasCardinalLT_iff_of_equiv (equivShrink.{w} X),
        hasCardinalLT_iff_cardinal_mk_lt]⟩

/-- For any `w`-small family `X : ι → Type u` of `w`-small types, there exists
a regular cardinal `κ : Cardinal.{w}` such that `HasCardinalLT (X i) κ` for all `i : ι`. -/
/-
**HasCardinalLT.exists_regular_cardinal_forall** 是 Mathlib 中的一个引理，位于命名空间 `HasCar
dinalLT`。
形式化陈述：exists_regular_cardinal_forall {ι : Type v} (X : ι -> Type u) [Small.{w} ι
] [forall i, Small.{w} (X i)] : exists (κ : Cardinal.{w}), κ.IsRegular ∧ forall 
(i : ι), HasCardinalLT (X i) κ
参数：X : ι -> Type u；X i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasCardinalLT.exists_regular_cardinal`：exists_regular_cardinal (X : Type
 u) [Small.{w} X] : exists (κ : Cardinal.{w}), κ.IsRegular ∧ HasCardinalLT X κ
· 使用引理 `HasCardinalLT.of_injective`：of_injective (f : Y -> X) (hf : Function.Inj
ective f) : HasCardinalLT Y κ
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)

--- 原说明 ---
For any `w`-small family `X : ι → Type u` of `w`-small types, there exists
a regular cardinal `κ : Cardinal.{w}` such that `HasCardinalLT (X i) κ` for all 
`i : ι`.
-/
lemma exists_regular_cardinal_forall {ι : Type v} (X : ι → Type u) [Small.{w} ι]
    [∀ i, Small.{w} (X i)] :
    ∃ (κ : Cardinal.{w}), κ.IsRegular ∧ ∀ (i : ι), HasCardinalLT (X i) κ := by
  obtain ⟨κ, hκ, h⟩ := exists_regular_cardinal.{w} (Sigma X)
  exact ⟨κ, hκ, fun i ↦ h.of_injective _ sigma_mk_injective⟩

end HasCardinalLT

