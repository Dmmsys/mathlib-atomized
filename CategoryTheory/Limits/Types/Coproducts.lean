/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# Coproducts in `Type`

If `F : J → Type max v u` (with `J : Type v`), we show that the coproduct
of `F` exists in `Type max v u` and identifies to the sigma type `Σ j, F j`.
Similarly, the binary coproduct of two types `X` and `Y` identifies to
`X ⊕ Y`, and the initial object of `Type u` if `PEmpty`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

namespace Limits

variable {C : Type u} (F : C → Type v)

/-- Given a functor `F : Discrete C ⥤ Type v`, this is a "cofan" for `F`,
but we allow the point to be in `Type w` for an arbitrary universe `w`. -/
/-
**CategoryTheory.Limits.CofanTypes** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：CofanTypes
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : Discrete C ⥤ Type v`, this is a "cofan" for `F`,
but we allow the point to be in `Type w` for an arbitrary universe `w`.
-/
abbrev CofanTypes := Functor.CoconeTypes.{w} (Discrete.functor F)

variable {F}

namespace CofanTypes

/-- The injection map for a cofan of a functor to types. -/
/-
**CategoryTheory.Limits.CofanTypes.inj** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Limits.CofanTypes`。
形式化陈述：inj (c : CofanTypes.{w} F) (i : C) : F i -> c.pt
参数：c : CofanTypes.{w} F；i : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The injection map for a cofan of a functor to types.
-/
abbrev inj (c : CofanTypes.{w} F) (i : C) : F i → c.pt := c.ι ⟨i⟩

variable (F) in
/-- The cofan given by a sigma type. -/
@[simps]
/-
**CategoryTheory.Limits.CofanTypes.sigma** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.CofanTypes`。
形式化陈述：sigma : CofanTypes F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofan given by a sigma type.
-/
def sigma : CofanTypes F where
  pt := Σ (i : C), F i
  ι := fun ⟨i⟩ x ↦ ⟨i, x⟩
  ι_naturality := by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain rfl : i = j := by simpa using Discrete.eq_of_hom f
    rfl

@[simp]
/-
**CategoryTheory.Limits.CofanTypes.sigma_inj** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Limits.CofanTypes`。
形式化陈述：sigma_inj (i : C) (x : F i) : (sigma F).inj i x = ⟨i, x⟩
参数：i : C；x : F i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sigma_inj (i : C) (x : F i) :
    (sigma F).inj i x = ⟨i, x⟩ := rfl
/-
**CategoryTheory.Limits.CofanTypes.isColimit_mk** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits.CofanTypes`。
形式化陈述：isColimit_mk (c : CofanTypes.{w} F) (h₁ : forall (x : c.pt), exists (i : C
) (y : F i), c.inj i y = x) (h₂ : forall (i : C), Function.Injective (c.inj i)) 
(h₃ : forall (i j : C) (x : F i) (y : F j), c.inj i x = c.inj j y -> i = j) : Fu
nctor.CoconeTypes.IsColimit c where bijective
参数：c : CofanTypes.{w} F；h₁ : forall (x : c.pt), exists (i : C) (y : F i), c.inj 
i y = x；h₂ : forall (i : C), Function.Injective (c.inj i)；h₃ : forall (i j : C) 
(x : F i) (y : F j), c.inj i x = c.inj j y -> i = j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ιColimitType_jointly_surjective`：ιColimitType_joi
ntly_surjective (t : F.ColimitType) : exists j x, F.ιColimitType j x = t
-/
lemma isColimit_mk (c : CofanTypes.{w} F)
    (h₁ : ∀ (x : c.pt), ∃ (i : C) (y : F i), c.inj i y = x)
    (h₂ : ∀ (i : C), Function.Injective (c.inj i))
    (h₃ : ∀ (i j : C) (x : F i) (y : F j), c.inj i x = c.inj j y → i = j) :
    Functor.CoconeTypes.IsColimit c where
  bijective := by
    constructor
    · intro x y h
      obtain ⟨⟨i⟩, x, rfl⟩ := (Discrete.functor F).ιColimitType_jointly_surjective x
      obtain ⟨⟨j⟩, y, rfl⟩ := (Discrete.functor F).ιColimitType_jointly_surjective y
      obtain rfl := h₃ _ _ _ _ h
      obtain rfl := h₂ _ h
      rfl
    · intro x
      obtain ⟨i, y, rfl⟩ := h₁ x
      exact ⟨(Discrete.functor F).ιColimitType ⟨i⟩ y, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-
**CategoryTheory.Limits.CofanTypes.isColimit_sigma** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits.CofanTypes`。
形式化陈述：isColimit_sigma : Functor.CoconeTypes.IsColimit (sigma F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CofanTypes.isColimit_mk`：isColimit_mk (c : CofanTy
pes.{w} F) (h₁ : forall (x : c.pt), exists (i : C) (y : F i), c.inj i y = x) (h₂
 : forall (i : C), Function.Injecti…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Sigma.ext_iff`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x = y ↔ 
x.fst = y.fst ∧ x.snd ≍ y.snd
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma isColimit_sigma : Functor.CoconeTypes.IsColimit (sigma F) :=
  isColimit_mk _ (by aesop)
    (fun _ _ _ h ↦ by rw [Sigma.ext_iff] at h; simpa using h)
    (fun _ _ _ _ h ↦ congr_arg Sigma.fst h)

variable (F) in
/-- Given a cofan of a functor to types, this is a canonical map
from the Sigma type to the point of the cofan. -/
@[simp]
/-
**CategoryTheory.Limits.CofanTypes.fromSigma** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.CofanTypes`。
形式化陈述：fromSigma (c : CofanTypes.{w} F) (x : Σ (i : C), F i) : c.pt
参数：c : CofanTypes.{w} F；x : Σ (i : C), F i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cofan of a functor to types, this is a canonical map
from the Sigma type to the point of the cofan.
-/
def fromSigma (c : CofanTypes.{w} F) (x : Σ (i : C), F i) : c.pt :=
  c.inj x.1 x.2

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.CofanTypes.isColimit_iff_bijective_fromSigma** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Limits.CofanTypes`。
形式化陈述：isColimit_iff_bijective_fromSigma (c : CofanTypes.{w} F) : c.IsColimit ↔ F
unction.Bijective c.fromSigma
参数：c : CofanTypes.{w} F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.CoconeTypes.IsColimit.iff_bijective`：iff_bijectiv
e {c' : CoconeTypes.{w₂} F} (f : c.pt -> c'.pt) (hf : forall j x, c'.ι j x = f (
c.ι j x)) : c'.IsColimit ↔ Function.Bijective f
· 使用引理 `CategoryTheory.Limits.CofanTypes.isColimit_sigma`：isColimit_sigma : Func
tor.CoconeTypes.IsColimit (sigma F)
· 使用定理 `CategoryTheory.Limits.CofanTypes.sigma_ι_snd`：∀ {C : Type u} (F : C → Ty
pe v) (x : CategoryTheory.Discrete C) (x_1 : (CategoryTheory.Discrete.functor F)
.obj x),   ((CategoryTheory.Limits…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isColimit_iff_bijective_fromSigma (c : CofanTypes.{w} F) :
    c.IsColimit ↔ Function.Bijective c.fromSigma := by
  rw [(isColimit_sigma F).iff_bijective]
  aesop

section

variable {c : CofanTypes.{w} F} (hc : Functor.CoconeTypes.IsColimit c)

include hc

/-
**CategoryTheory.Limits.CofanTypes.bijective_fromSigma_of_isColimit** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Limits.CofanTypes`。
形式化陈述：bijective_fromSigma_of_isColimit : Function.Bijective c.fromSigma
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Limits.CofanTypes.isColimit_iff_bijective_fromSigma`：isCo
limit_iff_bijective_fromSigma (c : CofanTypes.{w} F) : c.IsColimit ↔ Function.Bi
jective c.fromSigma
-/
lemma bijective_fromSigma_of_isColimit :
    Function.Bijective c.fromSigma := by
  rwa [← isColimit_iff_bijective_fromSigma]

/-- The bijection from the sigma type to the point of a colimit cofan
of a functor to types. -/
/-
**CategoryTheory.Limits.CofanTypes.equivOfIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.CofanTypes`。
形式化陈述：equivOfIsColimit : (Σ (i : C), F i) ≃ c.pt
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CofanTypes.bijective_fromSigma_of_isColimit`：bijec
tive_fromSigma_of_isColimit : Function.Bijective c.fromSigma

--- 原说明 ---
The bijection from the sigma type to the point of a colimit cofan
of a functor to types.
-/
noncomputable def equivOfIsColimit :
    (Σ (i : C), F i) ≃ c.pt :=
  Equiv.ofBijective _ (bijective_fromSigma_of_isColimit hc)

@[simp]
/-
**CategoryTheory.Limits.CofanTypes.equivOfIsColimit_apply** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits.CofanTypes`。
形式化陈述：equivOfIsColimit_apply (i : C) (x : F i) : equivOfIsColimit hc ⟨i, x⟩ = c.
inj i x
参数：i : C；x : F i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivOfIsColimit_apply (i : C) (x : F i) :
    equivOfIsColimit hc ⟨i, x⟩ = c.inj i x := rfl

@[simp]
/-
**CategoryTheory.Limits.CofanTypes.equivOfIsColimit_symm_apply** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Limits.CofanTypes`。
形式化陈述：equivOfIsColimit_symm_apply (i : C) (x : F i) : (equivOfIsColimit hc).symm
 (c.inj i x) = ⟨i, x⟩
参数：i : C；x : F i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivOfIsColimit_symm_apply (i : C) (x : F i) :
    (equivOfIsColimit hc).symm (c.inj i x) = ⟨i, x⟩ :=
  (equivOfIsColimit hc).injective (by simp)
/-
**CategoryTheory.Limits.CofanTypes.inj_jointly_surjective_of_isColimit** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Limits.CofanTypes`。
形式化陈述：inj_jointly_surjective_of_isColimit (x : c.pt) : exists (i : C) (y : F i),
 c.inj i y = x
参数：x : c.pt。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.CoconeTypes.IsColimit.ι_jointly_surjective`：ι_joi
ntly_surjective (y : c.pt) : exists j x, c.ι j x = y
-/
lemma inj_jointly_surjective_of_isColimit (x : c.pt) :
    ∃ (i : C) (y : F i), c.inj i y = x := by
  obtain ⟨⟨i⟩, y, rfl⟩ := hc.ι_jointly_surjective x
  exact ⟨i, y, rfl⟩
/-
**CategoryTheory.Limits.CofanTypes.inj_injective_of_isColimit** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Limits.CofanTypes`。
形式化陈述：inj_injective_of_isColimit (i : C) : Function.Injective (c.inj i)
参数：i : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma inj_injective_of_isColimit (i : C) :
    Function.Injective (c.inj i) := by
  intro y₁ y₂ h
  simpa using (equivOfIsColimit hc).injective (a₁ := ⟨i, y₁⟩) (a₂ := ⟨i, y₂⟩) h
/-
**CategoryTheory.Limits.CofanTypes.eq_of_inj_apply_eq_of_isColimit** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Limits.CofanTypes`。
形式化陈述：eq_of_inj_apply_eq_of_isColimit {i₁ i₂ : C} (y₁ : F i₁) (y₂ : F i₂) (h : c
.inj i₁ y₁ = c.inj i₂ y₂) : i₁ = i₂
参数：y₁ : F i₁；y₂ : F i₂；h : c.inj i₁ y₁ = c.inj i₂ y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma eq_of_inj_apply_eq_of_isColimit
    {i₁ i₂ : C} (y₁ : F i₁) (y₂ : F i₂) (h : c.inj i₁ y₁ = c.inj i₂ y₂) :
    i₁ = i₂ :=
  congr_arg Sigma.fst ((equivOfIsColimit hc).injective (a₁ := ⟨i₁, y₁⟩) (a₂ := ⟨i₂, y₂⟩) h)
/-
**CategoryTheory.Limits.CofanTypes.inj_apply_eq_iff_of_isColimit** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Limits.CofanTypes`。
形式化陈述：inj_apply_eq_iff_of_isColimit {i₁ i₂ : C} (y₁ : F i₁) (y₂ : F i₂) : c.inj 
i₁ y₁ = c.inj i₂ y₂ ↔ exists (h : i₁ = i₂), y₂ = cast (by rw [h]) y₁
参数：y₁ : F i₁；y₂ : F i₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Limits.CofanTypes.inj_injective_of_isColimit`：inj_injecti
ve_of_isColimit (i : C) : Function.Injective (c.inj i)
· 使用引理 `CategoryTheory.Limits.CofanTypes.eq_of_inj_apply_eq_of_isColimit`：eq_of_
inj_apply_eq_of_isColimit {i₁ i₂ : C} (y₁ : F i₁) (y₂ : F i₂) (h : c.inj i₁ y₁ =
 c.inj i₂ y₂) : i₁ = i₂
-/
lemma inj_apply_eq_iff_of_isColimit
    {i₁ i₂ : C} (y₁ : F i₁) (y₂ : F i₂) :
    c.inj i₁ y₁ = c.inj i₂ y₂ ↔ ∃ (h : i₁ = i₂), y₂ = cast (by rw [h]) y₁ := by
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ↦ by subst h₁ h₂; rfl⟩
  obtain rfl := eq_of_inj_apply_eq_of_isColimit hc _ _ h
  exact ⟨rfl, (inj_injective_of_isColimit hc i₁ h).symm⟩

end

end CofanTypes

namespace Cofan

variable {C : Type u} {F : C → Type v} (c : Cofan F)

/-- If `F : C → Type v`, then the data of a "type-theoretic" cofan of `F`
with a point in `Type v` is the same as the data of a cocone (in a categorical sense). -/
@[simps]
/-
**CategoryTheory.Limits.Cofan.cofanTypes** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.Cofan`。
形式化陈述：cofanTypes : CofanTypes.{v} F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C → Type v`, then the data of a "type-theoretic" cofan of `F`
with a point in `Type v` is the same as the data of a cocone (in a categorical s
ense).
-/
def cofanTypes :
    CofanTypes.{v} F where
  pt := c.pt
  ι := fun ⟨j⟩ ↦ c.inj j
  ι_naturality := by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain rfl : i = j := by simpa using Discrete.eq_of_hom f
    rfl
/-
**CategoryTheory.Limits.Cofan.isColimit_cofanTypes_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits.Cofan`。
形式化陈述：isColimit_cofanTypes_iff : c.cofanTypes.IsColimit ↔ Nonempty (IsColimit c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.CoconeTypes.isColimit_iff`：∀ {J : Type v} [inst :
 CategoryTheory.Category.{w, v} J] {F : CategoryTheory.Functor J (Type u)} (c : 
F.CoconeTypes),   c.IsColimit ↔ Nonemp…
-/
lemma isColimit_cofanTypes_iff :
    c.cofanTypes.IsColimit ↔ Nonempty (IsColimit c) :=
  Functor.CoconeTypes.isColimit_iff _
/-
**CategoryTheory.Limits.Cofan.nonempty_isColimit_iff_bijective_fromSigma** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.Cofan`。
形式化陈述：nonempty_isColimit_iff_bijective_fromSigma : Nonempty (IsColimit c) ↔ Func
tion.Bijective c.cofanTypes.fromSigma
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Limits.Cofan.isColimit_cofanTypes_iff`：isColimit_cofanTyp
es_iff : c.cofanTypes.IsColimit ↔ Nonempty (IsColimit c)
· 使用引理 `CategoryTheory.Limits.CofanTypes.isColimit_iff_bijective_fromSigma`：isCo
limit_iff_bijective_fromSigma (c : CofanTypes.{w} F) : c.IsColimit ↔ Function.Bi
jective c.fromSigma
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nonempty_isColimit_iff_bijective_fromSigma :
    Nonempty (IsColimit c) ↔ Function.Bijective c.cofanTypes.fromSigma := by
  rw [← isColimit_cofanTypes_iff, CofanTypes.isColimit_iff_bijective_fromSigma]

variable {c}
/-
**CategoryTheory.Limits.Cofan.inj_jointly_surjective_of_isColimit** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Limits.Cofan`。
形式化陈述：inj_jointly_surjective_of_isColimit (hc : IsColimit c) (x : c.pt) : exists
 (i : C) (y : F i), c.inj i y = x
参数：hc : IsColimit c；x : c.pt。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CofanTypes.inj_jointly_surjective_of_isColimit`：in
j_jointly_surjective_of_isColimit (x : c.pt) : exists (i : C) (y : F i), c.inj i
 y = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Limits.Cofan.isColimit_cofanTypes_iff`：isColimit_cofanTyp
es_iff : c.cofanTypes.IsColimit ↔ Nonempty (IsColimit c)
-/
lemma inj_jointly_surjective_of_isColimit (hc : IsColimit c) (x : c.pt) :
    ∃ (i : C) (y : F i), c.inj i y = x :=
  CofanTypes.inj_jointly_surjective_of_isColimit
    ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) x
/-
**CategoryTheory.Limits.Cofan.inj_injective_of_isColimit** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits.Cofan`。
形式化陈述：inj_injective_of_isColimit (hc : IsColimit c) (i : C) : Function.Injective
 (c.inj i)
参数：hc : IsColimit c；i : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CofanTypes.inj_injective_of_isColimit`：inj_injecti
ve_of_isColimit (i : C) : Function.Injective (c.inj i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Limits.Cofan.isColimit_cofanTypes_iff`：isColimit_cofanTyp
es_iff : c.cofanTypes.IsColimit ↔ Nonempty (IsColimit c)
-/
lemma inj_injective_of_isColimit (hc : IsColimit c) (i : C) :
    Function.Injective (c.inj i) :=
  CofanTypes.inj_injective_of_isColimit ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) i
/-
**CategoryTheory.Limits.Cofan.eq_of_inj_apply_eq_of_isColimit** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Limits.Cofan`。
形式化陈述：eq_of_inj_apply_eq_of_isColimit (hc : IsColimit c) {i₁ i₂ : C} (y₁ : F i₁)
 (y₂ : F i₂) (h : c.inj i₁ y₁ = c.inj i₂ y₂) : i₁ = i₂
参数：hc : IsColimit c；y₁ : F i₁；y₂ : F i₂；h : c.inj i₁ y₁ = c.inj i₂ y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CofanTypes.eq_of_inj_apply_eq_of_isColimit`：eq_of_
inj_apply_eq_of_isColimit {i₁ i₂ : C} (y₁ : F i₁) (y₂ : F i₂) (h : c.inj i₁ y₁ =
 c.inj i₂ y₂) : i₁ = i₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Limits.Cofan.isColimit_cofanTypes_iff`：isColimit_cofanTyp
es_iff : c.cofanTypes.IsColimit ↔ Nonempty (IsColimit c)
-/
lemma eq_of_inj_apply_eq_of_isColimit (hc : IsColimit c)
    {i₁ i₂ : C} (y₁ : F i₁) (y₂ : F i₂) (h : c.inj i₁ y₁ = c.inj i₂ y₂) :
    i₁ = i₂ :=
  CofanTypes.eq_of_inj_apply_eq_of_isColimit ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) _ _ h
/-
**CategoryTheory.Limits.Cofan.inj_apply_eq_iff_of_isColimit** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits.Cofan`。
形式化陈述：inj_apply_eq_iff_of_isColimit (hc : IsColimit c) {i j : C} (x : F i) (y : 
F j) : c.inj i x = c.inj j y ↔ exists (hij : i = j), y = cast (by rw [hij]) x
参数：hc : IsColimit c；x : F i；y : F j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CofanTypes.inj_apply_eq_iff_of_isColimit`：inj_appl
y_eq_iff_of_isColimit {i₁ i₂ : C} (y₁ : F i₁) (y₂ : F i₂) : c.inj i₁ y₁ = c.inj 
i₂ y₂ ↔ exists (h : i₁ = i₂), y₂ = cast (by rw [h]) …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Limits.Cofan.isColimit_cofanTypes_iff`：isColimit_cofanTyp
es_iff : c.cofanTypes.IsColimit ↔ Nonempty (IsColimit c)
-/
lemma inj_apply_eq_iff_of_isColimit (hc : IsColimit c) {i j : C} (x : F i) (y : F j) :
    c.inj i x = c.inj j y ↔ ∃ (hij : i = j), y = cast (by rw [hij]) x :=
  CofanTypes.inj_apply_eq_iff_of_isColimit ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) _ _

end Cofan

namespace Types

/-- The category of types has `PEmpty` as an initial object. -/
/-
**CategoryTheory.Limits.Types.initialColimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.Types`。
形式化陈述：initialColimitCocone : Limits.ColimitCocone (Functor.empty (Type u)) where
 -- Porting note: tidy was able to fill the structure automatically cocone
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of types has `PEmpty` as an initial object.
-/
def initialColimitCocone : Limits.ColimitCocone (Functor.empty (Type u)) where
  -- Porting note: tidy was able to fill the structure automatically
  cocone :=
    { pt := PEmpty
      ι := (Functor.uniqueFromEmpty _).inv }
  isColimit :=
    { desc := fun _ => ↾fun x => x.elim
      fac := fun _ => by rintro ⟨⟨⟩⟩
      uniq := fun _ _ _ => by ext x; cases x }

/-- The initial object in `Type u` is `PEmpty`. -/
/-
**CategoryTheory.Limits.Types.initialIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.Types`。
形式化陈述：initialIso : ⊥_ Type u ≅ PEmpty
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial object in `Type u` is `PEmpty`.
-/
noncomputable def initialIso : ⊥_ Type u ≅ PEmpty :=
  colimit.isoColimitCocone initialColimitCocone.{u, 0}

/-- The initial object in `Type u` is `PEmpty`. -/
/-
**CategoryTheory.Limits.Types.isInitialPEmpty** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.Types`。
形式化陈述：isInitialPEmpty : IsInitial (PEmpty : Type u)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial object in `Type u` is `PEmpty`.
-/
noncomputable def isInitialPEmpty : IsInitial (PEmpty : Type u) :=
  initialIsInitial.ofIso initialIso

@[deprecated (since := "2026-02-08")] alias isInitialPunit := isInitialPEmpty

/-- An object in `Type u` is initial if and only if it is empty. -/
/-
**CategoryTheory.Limits.Types.initial_iff_empty** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits.Types`。
形式化陈述：initial_iff_empty (X : Type u) : Nonempty (IsInitial X) ↔ IsEmpty X
参数：X : Type u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α

--- 原说明 ---
An object in `Type u` is initial if and only if it is empty.
-/
lemma initial_iff_empty (X : Type u) : Nonempty (IsInitial X) ↔ IsEmpty X := by
  constructor
  · intro ⟨h⟩
    exact Function.isEmpty (IsInitial.to h PEmpty)
  · intro h
    exact ⟨IsInitial.ofIso Types.isInitialPEmpty <| Equiv.toIso <| Equiv.equivOfIsEmpty PEmpty X⟩


/-- The sum type `X ⊕ Y` forms a cocone for the binary coproduct of `X` and `Y`. -/
@[simps!]
/-
**CategoryTheory.Limits.Types.binaryCoproductCocone** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.Types`。
形式化陈述：binaryCoproductCocone (X Y : Type u) : Cocone (pair X Y)
参数：X Y : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum type `X ⊕ Y` forms a cocone for the binary coproduct of `X` and `Y`.
-/
def binaryCoproductCocone (X Y : Type u) : Cocone (pair X Y) :=
  BinaryCofan.mk (↾Sum.inl) (↾Sum.inr)

open CategoryTheory.Limits.WalkingPair

/-- The sum type `X ⊕ Y` is a binary coproduct for `X` and `Y`. -/
@[simps]
/-
**CategoryTheory.Limits.Types.binaryCoproductColimit** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.Types`。
形式化陈述：binaryCoproductColimit (X Y : Type u) : IsColimit (binaryCoproductCocone X
 Y) where desc
参数：X Y : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum type `X ⊕ Y` is a binary coproduct for `X` and `Y`.
-/
def binaryCoproductColimit (X Y : Type u) : IsColimit (binaryCoproductCocone X Y) where
  desc := fun s : BinaryCofan X Y => ↾(Sum.elim s.inl s.inr)
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := by
    ext ⟨⟩
    exacts [ConcreteCategory.congr_hom (w ⟨left⟩) _, ConcreteCategory.congr_hom (w ⟨right⟩) _]

/-- The category of types has `X ⊕ Y`,
as the binary coproduct of `X` and `Y`.
-/
/-
**CategoryTheory.Limits.Types.binaryCoproductColimitCocone** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：binaryCoproductColimitCocone (X Y : Type u) : Limits.ColimitCocone (pair X
 Y)
参数：X Y : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of types has `X ⊕ Y`,
as the binary coproduct of `X` and `Y`.
-/
def binaryCoproductColimitCocone (X Y : Type u) : Limits.ColimitCocone (pair X Y) :=
  ⟨_, binaryCoproductColimit X Y⟩

/-- The categorical binary coproduct in `Type u` is the sum `X ⊕ Y`. -/
/-
**CategoryTheory.Limits.Types.binaryCoproductIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.Types`。
形式化陈述：binaryCoproductIso (X Y : Type u) : Limits.coprod X Y ≅ X oplus Y
参数：X Y : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical binary coproduct in `Type u` is the sum `X ⊕ Y`.
-/
noncomputable def binaryCoproductIso (X Y : Type u) : Limits.coprod X Y ≅ X ⊕ Y :=
  colimit.isoColimitCocone (binaryCoproductColimitCocone X Y)

--open CategoryTheory.Type

@[elementwise (attr := simp)]
/-
**CategoryTheory.Limits.Types.binaryCoproductIso_inl_comp_hom** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：binaryCoproductIso_inl_comp_hom (X Y : Type u) : Limits.coprod.inl ≫ (bina
ryCoproductIso X Y).hom = ↾Sum.inl
参数：X Y : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem binaryCoproductIso_inl_comp_hom (X Y : Type u) :
    Limits.coprod.inl ≫ (binaryCoproductIso X Y).hom = ↾Sum.inl :=
  colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]
/-
**CategoryTheory.Limits.Types.binaryCoproductIso_inr_comp_hom** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：binaryCoproductIso_inr_comp_hom (X Y : Type u) : Limits.coprod.inr ≫ (bina
ryCoproductIso X Y).hom = ↾Sum.inr
参数：X Y : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem binaryCoproductIso_inr_comp_hom (X Y : Type u) :
    Limits.coprod.inr ≫ (binaryCoproductIso X Y).hom = ↾Sum.inr :=
  colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩

@[elementwise (attr := simp)]
/-
**CategoryTheory.Limits.Types.binaryCoproductIso_inl_comp_inv** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：binaryCoproductIso_inl_comp_inv (X Y : Type u) : ↾Sum.inl ≫ (binaryCoprodu
ctIso X Y).inv = Limits.coprod.inl
参数：X Y : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_inv`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem binaryCoproductIso_inl_comp_inv (X Y : Type u) :
    ↾Sum.inl ≫ (binaryCoproductIso X Y).inv = Limits.coprod.inl :=
  colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]
/-
**CategoryTheory.Limits.Types.binaryCoproductIso_inr_comp_inv** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits.Types`。
形式化陈述：binaryCoproductIso_inr_comp_inv (X Y : Type u) : ↾Sum.inr ≫ (binaryCoprodu
ctIso X Y).inv = Limits.coprod.inr
参数：X Y : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_inv`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem binaryCoproductIso_inr_comp_inv (X Y : Type u) :
    ↾Sum.inr ≫ (binaryCoproductIso X Y).inv = Limits.coprod.inr :=
  colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩

open Function (Injective)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.Types.binaryCofan_isColimit_iff** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.Types`。
形式化陈述：binaryCofan_isColimit_iff {X Y : Type u} (c : BinaryCofan X Y) : Nonempty 
(IsColimit c) ↔ Injective c.inl ∧ Injective c.inr ∧ IsCompl (Set.range c.inl) (S
et.range c.inr)
参数：c : BinaryCofan X Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_inv`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `CategoryTheory.types_comp`：types_comp {X Y Z : Type u} (f : X ⟶ Y) (g : 
Y ⟶ Z) : ConcreteCategory.hom (f ≫ g) = g ∘ f
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `eq_compl_iff_isCompl`：eq_compl_iff_isCompl : x = yᶜ ↔ IsCompl x y
· 使用定理 `Set.image_compl_eq`：image_compl_eq {f : α -> β} {s : Set α} (H : Bijecti
ve f) : f '' sᶜ = (f '' s)ᶜ
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.compl_range_inr`：compl_range_inr : (range (Sum.inr : β -> α oplus β)
)ᶜ = range (Sum.inl : α -> α oplus β)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `or_not`：or_not {p : Prop} : p ∨ ¬p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
（共 39 条，此处仅展示前 30 条）
-/
theorem binaryCofan_isColimit_iff {X Y : Type u} (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔
      Injective c.inl ∧ Injective c.inr ∧ IsCompl (Set.range c.inl) (Set.range c.inr) := by
  classical
    constructor
    · rintro ⟨h⟩
      rw [← show _ = c.inl from
          h.comp_coconePointUniqueUpToIso_inv (binaryCoproductColimit X Y) ⟨WalkingPair.left⟩,
        ← show _ = c.inr from
          h.comp_coconePointUniqueUpToIso_inv (binaryCoproductColimit X Y) ⟨WalkingPair.right⟩]
      dsimp [binaryCoproductCocone]
      refine
        ⟨(h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inl_injective,
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inr_injective, ?_⟩
      rw [types_comp, Set.range_comp, ← eq_compl_iff_isCompl, types_comp]
      dsimp
      rw [Set.range_comp _ Sum.inr, ← dsimp% [Iso.toEquiv] Set.image_compl_eq
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.bijective]
      simp
    · rintro ⟨h₁, h₂, h₃⟩
      have : ∀ x, x ∈ Set.range c.inl ∨ x ∈ Set.range c.inr := by
        rw [eq_compl_iff_isCompl.mpr h₃.symm]
        exact fun _ => or_not
      refine ⟨BinaryCofan.IsColimit.mk _ ?_ ?_ ?_ ?_⟩
      · intro T f g
        refine ↾fun x => ?_
        exact
          if h : x ∈ Set.range c.inl then f ((Equiv.ofInjective _ h₁).symm ⟨x, h⟩)
          else g ((Equiv.ofInjective _ h₂).symm ⟨x, (this x).resolve_left h⟩)
      · intro T f g
        ext x
        simp
      · intro T f g
        ext x
        dsimp
        simp only [Set.mem_range, Equiv.ofInjective_symm_apply, dite_eq_right_iff,
          forall_exists_index]
        intro y e
        have : c.inr x ∈ Set.range c.inl ⊓ Set.range c.inr := ⟨⟨_, e⟩, ⟨_, rfl⟩⟩
        rw [disjoint_iff.mp h₃.1] at this
        exact this.elim
      · rintro T _ _ m rfl rfl
        ext x
        simp only [TypeCat.Fun.toFun_apply, Functor.const_obj_obj, pair_obj_left, Set.mem_range,
          comp_apply, pair_obj_right, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
        split_ifs <;> exact congr_arg _ (Equiv.apply_ofInjective_symm _ ⟨_, _⟩).symm

/-- Any monomorphism in `Type` is a coproduct injection. -/
/-
**CategoryTheory.Limits.Types.isCoprodOfMono** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.Types`。
形式化陈述：isCoprodOfMono {X Y : Type u} (f : X ⟶ Y) [Mono f] : IsColimit (BinaryCofa
n.mk f (↾(Subtype.val : ↑(Set.range f)ᶜ -> Y)))
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any monomorphism in `Type` is a coproduct injection.
-/
noncomputable def isCoprodOfMono {X Y : Type u} (f : X ⟶ Y) [Mono f] :
    IsColimit (BinaryCofan.mk f (↾(Subtype.val : ↑(Set.range f)ᶜ → Y))) := by
  apply Nonempty.some
  rw [binaryCofan_isColimit_iff]
  refine ⟨(mono_iff_injective f).mp inferInstance, Subtype.val_injective, ?_⟩
  symm
  rw [← eq_compl_iff_isCompl]
  exact Subtype.range_val

/-- The category of types has `Σ j, f j` as the coproduct of a type family `f : J → Type`.
-/
/-
**CategoryTheory.Limits.Types.coproductColimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.Types`。
形式化陈述：coproductColimitCocone {J : Type v} (F : J -> Type (max v u)) : Limits.Col
imitCocone (Discrete.functor F) where cocone
参数：F : J -> Type (max v u)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of types has `Σ j, f j` as the coproduct of a type family `f : J → 
Type`.
-/
def coproductColimitCocone {J : Type v} (F : J → Type (max v u)) :
    Limits.ColimitCocone (Discrete.functor F) where
  cocone :=
    { pt := Σ j, F j
      ι := Discrete.natTrans (fun ⟨j⟩ => ↾fun x => ⟨j, x⟩) }
  isColimit :=
    { desc := fun s => ↾fun x => s.ι.app ⟨x.1⟩ x.2
      uniq := fun s m w => by
        ext ⟨j, x⟩
        exact ConcreteCategory.congr_hom (w ⟨j⟩) x }

/-- The categorical coproduct in `Type u` is the type-theoretic coproduct `Σ j, F j`. -/
/-
**CategoryTheory.Limits.Types.coproductIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Types`。
形式化陈述：coproductIso {J : Type v} (F : J -> Type (max v u)) : ∐ F ≅ (Σ j, F j)
参数：F : J -> Type (max v u)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical coproduct in `Type u` is the type-theoretic coproduct `Σ j, F j`
.
-/
noncomputable def coproductIso {J : Type v} (F : J → Type (max v u)) :
    ∐ F ≅ (Σ j, F j) :=
  colimit.isoColimitCocone (coproductColimitCocone F)

@[elementwise (attr := simp)]
/-
**CategoryTheory.Limits.Types.coproductIso_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coproductIso_ι_comp_hom {J : Type v} (F : J → Type (max v u)) (j : J) :
    Sigma.ι F j ≫ (coproductIso F).hom = ↾fun x => ⟨j, x⟩ :=
  colimit.isoColimitCocone_ι_hom (coproductColimitCocone F) ⟨j⟩

@[elementwise (attr := simp)]
/-
**CategoryTheory.Limits.Types.coproductIso_mk_comp_inv** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.Types`。
形式化陈述：coproductIso_mk_comp_inv {J : Type v} (F : J -> Type (max v u)) (j : J) : 
(↾fun x => ⟨j, x⟩) ≫ (coproductIso F).inv = Sigma.ι F j
参数：F : J -> Type (max v u)；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem coproductIso_mk_comp_inv {J : Type v} (F : J → Type (max v u)) (j : J) :
    (↾fun x => ⟨j, x⟩) ≫ (coproductIso F).inv = Sigma.ι F j :=
  rfl

end CategoryTheory.Limits.Types

