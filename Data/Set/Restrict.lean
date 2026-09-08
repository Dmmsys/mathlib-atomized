/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Image

/-!
# Restrict the domain of a function to a set

## Main definitions

* `Set.domRestrict f s` : restrict the domain of `f` to the set `s`;
* `Set.codRestrict f s h` : given `h : ∀ x, f x ∈ s`, restrict the codomain of `f` to the set `s`;
-/

@[expose] public section

variable {α β γ δ : Type*} {ι : Sort*} {π : α → Type*}

open Equiv Equiv.Perm Function

namespace Set

/-! ### Domain restriction -/
section domRestrict

/-- Restrict domain of a function `f` to a set `s`. Same as `Subtype.restrict` but this version
takes an argument `↥s` instead of `Subtype s`. -/
/-
**Set.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：domRestrict (s : Set α) (f : forall a : α, π a) : forall a : s, π a
参数：s : Set α；f : forall a : α, π a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict domain of a function `f` to a set `s`. Same as `Subtype.restrict` but t
his version
takes an argument `↥s` instead of `Subtype s`.
-/
def domRestrict (s : Set α) (f : ∀ a : α, π a) : ∀ a : s, π a := fun x => f x
/-
**Set.domRestrict_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：domRestrict_def (s : Set α) : s.domRestrict (π
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict_def (s : Set α) : s.domRestrict (π := π) = fun f x ↦ f x := rfl
/-
**Set.domRestrict_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：domRestrict_eq (f : α -> β) (s : Set α) : s.domRestrict f = f ∘ Subtype.va
l
参数：f : α -> β；s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict_eq (f : α → β) (s : Set α) : s.domRestrict f = f ∘ Subtype.val :=
  rfl
/-
**Set.domRestrict_id** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (s : Set α), s.domRestrict id = Subtype.val
参数：s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma domRestrict_id (s : Set α) : domRestrict s id = Subtype.val := rfl

@[simp, grind =]
/-
**Set.domRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：domRestrict_apply (f : (a : α) -> π a) (s : Set α) (x : s) : s.domRestrict
 f x = f x
参数：f : (a : α) -> π a；s : Set α；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict_apply (f : (a : α) → π a) (s : Set α) (x : s) : s.domRestrict f x = f x :=
  rfl
/-
**Set.domRestrict_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：domRestrict_eq_iff {f : forall a, π a} {s : Set α} {g : forall a : s, π a}
 : domRestrict s f = g ↔ forall (a) (ha : a in s), f a = g ⟨a, ha⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
theorem domRestrict_eq_iff {f : ∀ a, π a} {s : Set α} {g : ∀ a : s, π a} :
    domRestrict s f = g ↔ ∀ (a) (ha : a ∈ s), f a = g ⟨a, ha⟩ :=
  funext_iff.trans Subtype.forall
/-
**Set.eq_domRestrict_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_domRestrict_iff {s : Set α} {f : forall a : s, π a} {g : forall a, π a}
 : f = domRestrict s g ↔ forall (a) (ha : a in s), f ⟨a, ha⟩ = g a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
theorem eq_domRestrict_iff {s : Set α} {f : ∀ a : s, π a} {g : ∀ a, π a} :
    f = domRestrict s g ↔ ∀ (a) (ha : a ∈ s), f ⟨a, ha⟩ = g a :=
  funext_iff.trans Subtype.forall

@[simp]
/-
**Set.range_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_domRestrict (f : α -> β) (s : Set α) : Set.range (s.domRestrict f) =
 f '' s
参数：f : α -> β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem range_domRestrict (f : α → β) (s : Set α) : Set.range (s.domRestrict f) = f '' s :=
  (range_comp _ _).trans <| congr_arg (f '' ·) Subtype.range_coe
/-
**Set.image_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_domRestrict (f : α -> β) (s t : Set α) : s.domRestrict f '' Subtype.
val ⁻¹' t = f '' (t inter s)
参数：f : α -> β；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.domRestrict_eq`：domRestrict_eq (f : α -> β) (s : Set α) : s.domRestr
ict f = f ∘ Subtype.val
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem image_domRestrict (f : α → β) (s t : Set α) :
    s.domRestrict f '' Subtype.val ⁻¹' t = f '' (t ∩ s) := by
  rw [domRestrict_eq, image_comp, image_preimage_eq_inter_range, Subtype.range_coe]

@[simp]
/-
**Set.domRestrict_dite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：domRestrict_dite {s : Set α} [forall x, Decidable (x in s)] (f : forall a 
in s, β) (g : forall a ∉ s, β) : (s.domRestrict fun a => if h : a in s then f a 
h else g a h) = (fun a : s => f a a.2)
参数：x in s；f : forall a in s, β；g : forall a ∉ s, β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem domRestrict_dite {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀ a ∈ s, β)
    (g : ∀ a ∉ s, β) :
    (s.domRestrict fun a => if h : a ∈ s then f a h else g a h) = (fun a : s => f a a.2) :=
  funext fun a => dif_pos a.2

@[simp]
/-
**Set.domRestrict_dite_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：domRestrict_dite_compl {s : Set α} [forall x, Decidable (x in s)] (f : for
all a in s, β) (g : forall a ∉ s, β) : (sᶜ.domRestrict fun a => if h : a in s th
en f a h else g a h) = (fun a : (sᶜ : Set α) => g a a.2)
参数：x in s；f : forall a in s, β；g : forall a ∉ s, β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem domRestrict_dite_compl {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀ a ∈ s, β)
    (g : ∀ a ∉ s, β) :
    (sᶜ.domRestrict fun a => if h : a ∈ s then f a h else g a h) =
      (fun a : (sᶜ : Set α) => g a a.2) :=
  funext fun a => dif_neg a.2

@[simp]
/-
**Set.domRestrict_ite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：domRestrict_ite (f g : α -> β) (s : Set α) [forall x, Decidable (x in s)] 
: (s.domRestrict fun a => if a in s then f a else g a) = s.domRestrict f
参数：f g : α -> β；s : Set α；x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.domRestrict_dite`：domRestrict_dite {s : Set α} [forall x, Decidable 
(x in s)] (f : forall a in s, β) (g : forall a ∉ s, β) : (s.domRestrict fun a =>
 if h : a …
-/
theorem domRestrict_ite (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    (s.domRestrict fun a => if a ∈ s then f a else g a) = s.domRestrict f := domRestrict_dite _ _

@[simp]
/-
**Set.domRestrict_ite_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：domRestrict_ite_compl (f g : α -> β) (s : Set α) [forall x, Decidable (x i
n s)] : (sᶜ.domRestrict fun a => if a in s then f a else g a) = sᶜ.domRestrict g
参数：f g : α -> β；s : Set α；x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.domRestrict_dite_compl`：domRestrict_dite_compl {s : Set α} [forall x
, Decidable (x in s)] (f : forall a in s, β) (g : forall a ∉ s, β) : (sᶜ.domRest
rict fun a => if…
-/
theorem domRestrict_ite_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    (sᶜ.domRestrict fun a => if a ∈ s then f a else g a) = sᶜ.domRestrict g :=
  domRestrict_dite_compl _ _

@[simp]
/-
**Set.domRestrict_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：domRestrict_piecewise (f g : α -> β) (s : Set α) [forall x, Decidable (x i
n s)] : s.domRestrict (piecewise s f g) = s.domRestrict f
参数：f g : α -> β；s : Set α；x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.domRestrict_ite`：domRestrict_ite (f g : α -> β) (s : Set α) [forall 
x, Decidable (x in s)] : (s.domRestrict fun a => if a in s then f a else g a) = 
s.domRest…
-/
theorem domRestrict_piecewise (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    s.domRestrict (piecewise s f g) = s.domRestrict f := domRestrict_ite _ _ _

@[simp]
/-
**Set.domRestrict_piecewise_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：domRestrict_piecewise_compl (f g : α -> β) (s : Set α) [forall x, Decidabl
e (x in s)] : sᶜ.domRestrict (piecewise s f g) = sᶜ.domRestrict g
参数：f g : α -> β；s : Set α；x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.domRestrict_ite_compl`：domRestrict_ite_compl (f g : α -> β) (s : Set
 α) [forall x, Decidable (x in s)] : (sᶜ.domRestrict fun a => if a in s then f a
 else g a) = sᶜ…
-/
theorem domRestrict_piecewise_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    sᶜ.domRestrict (piecewise s f g) = sᶜ.domRestrict g := domRestrict_ite_compl _ _ _
/-
**Set.domRestrict_extend_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：domRestrict_extend_range (f : α -> β) (g : α -> γ) (g' : β -> γ) : (range 
f).domRestrict (extend f g g') = fun x => g x.coe_prop.choose
参数：f : α -> β；g : α -> γ；g' : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.domRestrict_dite`：domRestrict_dite {s : Set α} [forall x, Decidable 
(x in s)] (f : forall a in s, β) (g : forall a ∉ s, β) : (s.domRestrict fun a =>
 if h : a …
-/
theorem domRestrict_extend_range (f : α → β) (g : α → γ) (g' : β → γ) :
    (range f).domRestrict (extend f g g') = fun x => g x.coe_prop.choose := by
  classical
  exact domRestrict_dite _ _

@[simp]
/-
**Set.domRestrict_extend_compl_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：domRestrict_extend_compl_range (f : α -> β) (g : α -> γ) (g' : β -> γ) : (
range f)ᶜ.domRestrict (extend f g g') = g' ∘ Subtype.val
参数：f : α -> β；g : α -> γ；g' : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.domRestrict_dite_compl`：domRestrict_dite_compl {s : Set α} [forall x
, Decidable (x in s)] (f : forall a in s, β) (g : forall a ∉ s, β) : (sᶜ.domRest
rict fun a => if…
-/
theorem domRestrict_extend_compl_range (f : α → β) (g : α → γ) (g' : β → γ) :
    (range f)ᶜ.domRestrict (extend f g g') = g' ∘ Subtype.val := by
  classical
  exact domRestrict_dite_compl _ _

/-- If a function `f` is restricted to a set `t`, and `s ⊆ t`, this is the restriction to `s`. -/
@[simp]
/-
**Set.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：domRestrict (s : Set α) (f : forall a : α, π a) : forall a : s, π a
参数：s : Set α；f : forall a : α, π a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function `f` is restricted to a set `t`, and `s ⊆ t`, this is the restricti
on to `s`.
-/
def domRestrict₂ {s t : Set α} (hst : s ⊆ t) (f : ∀ a : t, π a) : ∀ a : s, π a :=
  fun x => f ⟨x.1, hst x.2⟩
/-
**Set.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：domRestrict (s : Set α) (f : forall a : α, π a) : forall a : s, π a
参数：s : Set α；f : forall a : α, π a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict₂_def {s t : Set α} (hst : s ⊆ t) :
    domRestrict₂ (π := π) hst = fun f x ↦ f ⟨x.1, hst x.2⟩ := rfl
/-
**Set.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：domRestrict (s : Set α) (f : forall a : α, π a) : forall a : s, π a
参数：s : Set α；f : forall a : α, π a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict₂_comp_domRestrict {s t : Set α} (hst : s ⊆ t) :
    (domRestrict₂ (π := π) hst) ∘ t.domRestrict = s.domRestrict := rfl
/-
**Set.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：domRestrict (s : Set α) (f : forall a : α, π a) : forall a : s, π a
参数：s : Set α；f : forall a : α, π a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict₂_comp_domRestrict₂ {s t u : Set α} (hst : s ⊆ t) (htu : t ⊆ u) :
    (domRestrict₂ (π := π) hst) ∘ (domRestrict₂ htu) = domRestrict₂ (hst.trans htu) := rfl
/-
**Set.range_extend_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_extend_subset (f : α -> β) (g : α -> γ) (g' : β -> γ) : range (exten
d f g g') subseteq range g union g' '' (range f)ᶜ
参数：f : α -> β；g : α -> γ；g' : β -> γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.extend_def`：extend_def (f : α -> β) (g : α -> γ) (e' : β -> γ) 
(b : β) [Decidable (exists a, f a = b)] : extend f g e' b = if h : exists a, f a
 = b then…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem range_extend_subset (f : α → β) (g : α → γ) (g' : β → γ) :
    range (extend f g g') ⊆ range g ∪ g' '' (range f)ᶜ := by
  classical
  rintro _ ⟨y, rfl⟩
  rw [extend_def]
  split_ifs with h
  exacts [Or.inl (mem_range_self _), Or.inr (mem_image_of_mem _ h)]
/-
**Set.range_extend** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_extend {f : α -> β} (hf : Injective f) (g : α -> γ) (g' : β -> γ) : 
range (extend f g g') = range g union g' '' (range f)ᶜ
参数：hf : Injective f；g : α -> γ；g' : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.range_extend_subset`：range_extend_subset (f : α -> β) (g : α -> γ) (
g' : β -> γ) : range (extend f g g') subseteq range g union g' '' (range f)ᶜ
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
-/
theorem range_extend {f : α → β} (hf : Injective f) (g : α → γ) (g' : β → γ) :
    range (extend f g g') = range g ∪ g' '' (range f)ᶜ := by
  refine (range_extend_subset _ _ _).antisymm ?_
  rintro z (⟨x, rfl⟩ | ⟨y, hy, rfl⟩)
  exacts [⟨f x, hf.extend_apply _ _ _⟩, ⟨y, extend_apply' _ _ _ hy⟩]

/-- If `g` factors through `f` and `g` is injective, then `extend f g j` is injective on the
range of `f`. -/
/-
**Set._root_.Function.FactorsThrough.extend_injOn** 是 Mathlib 中的一个引理，位于命名空间 `Set
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` factors through `f` and `g` is injective, then `extend f g j` is injectiv
e on the
range of `f`.
-/
lemma _root_.Function.FactorsThrough.extend_injOn {f : α → β} {g : α → γ} {j : β → γ}
    (hf : g.FactorsThrough f) (hg : g.Injective) :
    (range f).InjOn (extend f g j) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
  rw [hf.extend_apply, hf.extend_apply] at heq
  rw [hg heq]

/-- If `f` and `g` are injective, then `extend f g j` is injective on the range of `f`. -/
/-
**Set._root_.Function.Injective.extend_injOn** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `g` are injective, then `extend f g j` is injective on the range of `
f`.
-/
lemma _root_.Function.Injective.extend_injOn {f : α → β} {g : α → γ} {j : β → γ}
    (hf : f.Injective) (hg : g.Injective) :
    (range f).InjOn (extend f g j) :=
  (hf.factorsThrough g).extend_injOn hg

/-- Restrict codomain of a function `f` to a set `s`. Same as `Subtype.coind` but this version
has codomain `↥s` instead of `Subtype s`. -/
/-
**Set.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：codRestrict (f : ι -> α) (s : Set α) (h : forall x, f x in s) : ι -> s
参数：f : ι -> α；s : Set α；h : forall x, f x in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict codomain of a function `f` to a set `s`. Same as `Subtype.coind` but th
is version
has codomain `↥s` instead of `Subtype s`.
-/
def codRestrict (f : ι → α) (s : Set α) (h : ∀ x, f x ∈ s) : ι → s := fun x => ⟨f x, h x⟩

@[simp]
/-
**Set.val_codRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：val_codRestrict_apply (f : ι -> α) (s : Set α) (h : forall x, f x in s) (x
 : ι) : (codRestrict f s h x : α) = f x
参数：f : ι -> α；s : Set α；h : forall x, f x in s；x : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_codRestrict_apply (f : ι → α) (s : Set α) (h : ∀ x, f x ∈ s) (x : ι) :
    (codRestrict f s h x : α) = f x :=
  rfl

@[simp]
/-
**Set.domRestrict_comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：domRestrict_comp_codRestrict {f : ι -> α} {g : α -> β} {b : Set α} (h : fo
rall x, f x in b) : b.domRestrict g ∘ b.codRestrict f h = g ∘ f
参数：h : forall x, f x in b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict_comp_codRestrict {f : ι → α} {g : α → β} {b : Set α}
    (h : ∀ x, f x ∈ b) : b.domRestrict g ∘ b.codRestrict f h = g ∘ f :=
  rfl

@[simp]
/-
**Set.injective_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：injective_codRestrict {f : ι -> α} {s : Set α} (h : forall x, f x in s) : 
Injective (codRestrict f s h) ↔ Injective f
参数：h : forall x, f x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem injective_codRestrict {f : ι → α} {s : Set α} (h : ∀ x, f x ∈ s) :
    Injective (codRestrict f s h) ↔ Injective f := by
  simp only [Injective, Subtype.ext_iff, val_codRestrict_apply]

alias ⟨_, _root_.Function.Injective.codRestrict⟩ := injective_codRestrict
/-
**Set.range_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_5} {f : ι → α} {s : Set α} (h : ∀ (x : ι), f 
x ∈ s),   Set.range (Set.codRestrict f s h) = Subtype.val ⁻¹' Set.range f
参数：h : ∀ (x : ι), f x ∈ s；Set.codRestrict f s h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem range_codRestrict {f : ι → α} {s : Set α} (h : ∀ x, f x ∈ s) :
    range (s.codRestrict f h) = (↑) ⁻¹' range f := by
  ext; simp [Subtype.ext_iff]
/-
**Set.surjective_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：surjective_codRestrict {f : ι -> α} {s : Set α} (h : forall x, f x in s) :
 (s.codRestrict f h).Surjective ↔ range f = s
参数：h : forall x, f x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_codRestrict`：∀ {α : Type u_1} {ι : Sort u_5} {f : ι → α} {s : 
Set α} (h : ∀ (x : ι), f x ∈ s),   Set.range (Set.codRestrict f s h) = Subtype.v
al ⁻¹' Set.…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.Subset.antisymm_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ a ⊆ b ∧ b
 ⊆ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem surjective_codRestrict {f : ι → α} {s : Set α} (h : ∀ x, f x ∈ s) :
    (s.codRestrict f h).Surjective ↔ range f = s := by
  simp [← range_eq_univ, Subset.antisymm_iff (a := range f), range_subset_iff, h]
/-
**Set.codRestrict_range_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：codRestrict_range_surjective (f : ι -> α) : ((range f).codRestrict f mem_r
ange_self).Surjective
参数：f : ι -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem codRestrict_range_surjective (f : ι → α) :
    ((range f).codRestrict f mem_range_self).Surjective := by
  rintro ⟨b, ⟨a, rfl⟩⟩
  exact ⟨a, rfl⟩

variable {s : Set α} {f₁ f₂ : α → β}

@[simp]
/-
**Set.domRestrict_eq_domRestrict_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：domRestrict_eq_domRestrict_iff : domRestrict s f₁ = domRestrict s f₂ ↔ EqO
n f₁ f₂ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.domRestrict_eq_iff`：domRestrict_eq_iff {f : forall a, π a} {s : Set 
α} {g : forall a : s, π a} : domRestrict s f = g ↔ forall (a) (ha : a in s), f a
 = g ⟨a, ha⟩
-/
theorem domRestrict_eq_domRestrict_iff :
    domRestrict s f₁ = domRestrict s f₂ ↔ EqOn f₁ f₂ s := domRestrict_eq_iff

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_def := domRestrict_def
@[deprecated (since := "2026-07-19")] alias restrict_eq := domRestrict_eq
@[deprecated (since := "2026-07-19")] alias restrict_id := domRestrict_id
@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply
@[deprecated (since := "2026-07-19")] alias restrict_eq_iff := domRestrict_eq_iff
@[deprecated (since := "2026-07-19")] alias eq_restrict_iff := eq_domRestrict_iff
@[deprecated (since := "2026-07-19")] alias range_restrict := range_domRestrict
@[deprecated (since := "2026-07-19")] alias image_restrict := image_domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_dite := domRestrict_dite
@[deprecated (since := "2026-07-19")] alias restrict_dite_compl := domRestrict_dite_compl
@[deprecated (since := "2026-07-19")] alias restrict_ite := domRestrict_ite
@[deprecated (since := "2026-07-19")] alias restrict_ite_compl := domRestrict_ite_compl
@[deprecated (since := "2026-07-19")] alias restrict_piecewise := domRestrict_piecewise
@[deprecated (since := "2026-07-19")] alias restrict_piecewise_compl := domRestrict_piecewise_compl
@[deprecated (since := "2026-07-19")] alias restrict_extend_range := domRestrict_extend_range
@[deprecated (since := "2026-07-19")]
alias restrict_extend_compl_range := domRestrict_extend_compl_range
@[deprecated (since := "2026-07-19")] alias restrict₂ := domRestrict₂
@[deprecated (since := "2026-07-19")] alias restrict₂_def := domRestrict₂_def
@[deprecated (since := "2026-07-19")] alias restrict₂_comp_restrict := domRestrict₂_comp_domRestrict
@[deprecated (since := "2026-07-19")]
alias restrict₂_comp_restrict₂ := domRestrict₂_comp_domRestrict₂
@[deprecated (since := "2026-07-19")]
alias restrict_comp_codRestrict := domRestrict_comp_codRestrict
@[deprecated (since := "2026-07-19")]
alias restrict_eq_restrict_iff := domRestrict_eq_domRestrict_iff

end domRestrict

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {p : Set γ} {f f₁ f₂ : α → β} {g g₁ g₂ : β → γ}
  {f' f₁' f₂' : β → α} {g' : γ → β} {a : α} {b : β}

section MapsTo

/-
**Set.MapsTo.restrict_commutes** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α) (t : Set β) (h : S
et.MapsTo f s t),   Subtype.val ∘ Set.MapsTo.restrict f s t h = f ∘ Subtype.val
参数：f : α → β；s : Set α；t : Set β；h : Set.MapsTo f s t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MapsTo.restrict_commutes (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) :
    Subtype.val ∘ h.restrict f s t = f ∘ Subtype.val :=
  rfl

@[simp]
/-
**Set.MapsTo.val_restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} (h : S
et.MapsTo f s t) (x : ↑s),   ↑(Set.MapsTo.restrict f s t h x) = f ↑x
参数：h : Set.MapsTo f s t；x : ↑s；Set.MapsTo.restrict f s t h x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MapsTo.val_restrict_apply (h : MapsTo f s t) (x : s) : (h.restrict f s t x : β) = f x :=
  rfl
/-
**Set.MapsTo.coe_iterate_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {f : α → α} (h : Set.MapsTo f s s) (x : ↑s) (
k : ℕ),   ↑((Set.MapsTo.restrict f s s h)^[k] x) = f^[k] ↑x
参数：h : Set.MapsTo f s s；x : ↑s；k : ℕ；(Set.MapsTo.restrict f s s h)^[k] x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
-/
theorem MapsTo.coe_iterate_restrict {f : α → α} (h : MapsTo f s s) (x : s) (k : ℕ) :
    h.restrict^[k] x = f^[k] x := by
  induction k with
  | zero => simp
  | succ k ih => simp only [iterate_succ', comp_apply, val_restrict_apply, ih]

/-- Restricting the domain and then the codomain is the same as `MapsTo.restrict`. -/
@[simp]
/-
**Set.codRestrict_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：codRestrict_domRestrict (h : forall x : s, f x in t) : codRestrict (s.domR
estrict f) t h = MapsTo.restrict f s t fun x hx => h ⟨x, hx⟩
参数：h : forall x : s, f x in t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricting the domain and then the codomain is the same as `MapsTo.restrict`.
-/
theorem codRestrict_domRestrict (h : ∀ x : s, f x ∈ t) :
    codRestrict (s.domRestrict f) t h = MapsTo.restrict f s t fun x hx => h ⟨x, hx⟩ :=
  rfl

@[deprecated (since := "2026-07-19")] alias codRestrict_restrict := codRestrict_domRestrict

/-- Reverse of `Set.codRestrict_domRestrict`. -/
/-
**Set.MapsTo.restrict_eq_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} (h : S
et.MapsTo f s t),   Set.MapsTo.restrict f s t h = Set.codRestrict (s.domRestrict
 f) t ⋯
参数：h : Set.MapsTo f s t；s.domRestrict f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reverse of `Set.codRestrict_domRestrict`.
-/
theorem MapsTo.restrict_eq_codRestrict (h : MapsTo f s t) :
    h.restrict f s t = codRestrict (s.domRestrict f) t fun x => h x.2 :=
  rfl
/-
**Set.MapsTo.coe_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} (h : S
et.MapsTo f s t),   Subtype.val ∘ Set.MapsTo.restrict f s t h = s.domRestrict f
参数：h : Set.MapsTo f s t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MapsTo.coe_restrict (h : Set.MapsTo f s t) :
    Subtype.val ∘ h.restrict f s t = s.domRestrict f :=
  rfl
/-
**Set.MapsTo.range_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α) (t : Set β) (h : S
et.MapsTo f s t),   Set.range (Set.MapsTo.restrict f s t h) = Subtype.val ⁻¹' f 
'' s
参数：f : α → β；s : Set α；t : Set β；h : Set.MapsTo f s t；Set.MapsTo.restrict f s t 
h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_subtype_map`：range_subtype_map {p : α -> Prop} {q : β -> Prop}
 (f : α -> β) (h : forall x, p x -> q (f x)) : range (Subtype.map f h) = (↑) ⁻¹'
 f '' { x |…
-/
theorem MapsTo.range_restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) :
    range (h.restrict f s t) = Subtype.val ⁻¹' f '' s :=
  Set.range_subtype_map f h
/-
**Set.mapsTo_iff_exists_map_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_iff_exists_map_subtype : MapsTo f s t ↔ exists g : s -> t, forall x
 : s, f x = g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
-/
theorem mapsTo_iff_exists_map_subtype : MapsTo f s t ↔ ∃ g : s → t, ∀ x : s, f x = g x :=
  ⟨fun h => ⟨h.restrict f s t, fun _ => rfl⟩, fun ⟨g, hg⟩ x hx => by
    rw [hg ⟨x, hx⟩]
    apply Subtype.coe_prop⟩
/-
**Set.surjective_mapsTo_image_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：surjective_mapsTo_image_restrict (f : α -> β) (s : Set α) : Surjective ((m
apsTo_image f s).restrict f s (f '' s))
参数：f : α -> β；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem surjective_mapsTo_image_restrict (f : α → β) (s : Set α) :
    Surjective ((mapsTo_image f s).restrict f s (f '' s)) := fun ⟨_, x, hs, hxy⟩ =>
  ⟨⟨x, hs⟩, Subtype.ext hxy⟩

end MapsTo

/-! ### Restriction onto preimage -/
section

variable (t)

variable (f s) in
/-
**Set.image_restrictPreimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_restrictPreimage : t.restrictPreimage f '' Subtype.val ⁻¹' s = Subty
pe.val ⁻¹' f '' s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.MapsTo.restrict_commutes`：∀ {α : Type u_1} {β : Type u_2} (f : α → β
) (s : Set α) (t : Set β) (h : Set.MapsTo f s t),   Subtype.val ∘ Set.MapsTo.res
trict f s t h = f …
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Set.image_preimage_inter`：image_preimage_inter (f : α -> β) (s : Set α) 
(t : Set β) : f '' (f ⁻¹' t inter s) = t inter f '' s
-/
theorem image_restrictPreimage :
    t.restrictPreimage f '' Subtype.val ⁻¹' s = Subtype.val ⁻¹' f '' s := by
  delta Set.restrictPreimage
  rw [← (Subtype.coe_injective).image_injective.eq_iff, ← image_comp, MapsTo.restrict_commutes,
    image_comp, Subtype.image_preimage_coe, Subtype.image_preimage_coe, image_preimage_inter]

variable (f) in
/-
**Set.range_restrictPreimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_restrictPreimage : range (t.restrictPreimage f) = Subtype.val ⁻¹' ra
nge f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_restrictPreimage : range (t.restrictPreimage f) = Subtype.val ⁻¹' range f := by
  simp only [← image_univ, ← image_restrictPreimage, preimage_univ]

@[simp]
/-
**Set.restrictPreimage_mk** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：restrictPreimage_mk (h : a in f ⁻¹' t) : t.restrictPreimage f ⟨a, h⟩ = ⟨f 
a, h⟩
参数：h : a in f ⁻¹' t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictPreimage_mk (h : a ∈ f ⁻¹' t) : t.restrictPreimage f ⟨a, h⟩ = ⟨f a, h⟩ := rfl
/-
**Set.image_val_preimage_restrictPreimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_val_preimage_restrictPreimage {u : Set t} : Subtype.val '' t.restric
tPreimage f ⁻¹' u = f ⁻¹' Subtype.val '' u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image_val_preimage_restrictPreimage {u : Set t} :
    Subtype.val '' t.restrictPreimage f ⁻¹' u = f ⁻¹' Subtype.val '' u := by
  ext
  simp
/-
**Set.preimage_restrictPreimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_restrictPreimage {u : Set t} : t.restrictPreimage f ⁻¹' u = (fun 
a : f ⁻¹' t => f a) ⁻¹' Subtype.val '' u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `Set.image_val_preimage_restrictPreimage`：image_val_preimage_restrictPrei
mage {u : Set t} : Subtype.val '' t.restrictPreimage f ⁻¹' u = f ⁻¹' Subtype.val
 '' u
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem preimage_restrictPreimage {u : Set t} :
    t.restrictPreimage f ⁻¹' u = (fun a : f ⁻¹' t ↦ f a) ⁻¹' Subtype.val '' u := by
  rw [← preimage_preimage (g := f) (f := Subtype.val), ← image_val_preimage_restrictPreimage,
    preimage_image_eq _ Subtype.val_injective]
/-
**Set.restrictPreimage_injective** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：restrictPreimage_injective (hf : Injective f) : Injective (t.restrictPreim
age f)
参数：hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Subtype.mk.inj`：∀ {α : Sort u} {p : α → Prop} {val : α} {property : p va
l} {val_1 : α} {property_1 : p val_1},   ⟨val, property⟩ = ⟨val_1, property_1⟩ →
 val…
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
-/
lemma restrictPreimage_injective (hf : Injective f) : Injective (t.restrictPreimage f) :=
  fun _ _ e => Subtype.coe_injective <| hf <| Subtype.mk.inj e
/-
**Set.restrictPreimage_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：restrictPreimage_surjective (hf : Surjective f) : Surjective (t.restrictPr
eimage f)
参数：hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
lemma restrictPreimage_surjective (hf : Surjective f) : Surjective (t.restrictPreimage f) :=
  fun x => ⟨⟨_, ((hf x).choose_spec.symm ▸ x.2 : _ ∈ t)⟩, Subtype.ext (hf x).choose_spec⟩
/-
**Set.restrictPreimage_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：restrictPreimage_bijective (hf : Bijective f) : Bijective (t.restrictPreim
age f)
参数：hf : Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.restrictPreimage_injective`：restrictPreimage_injective (hf : Injecti
ve f) : Injective (t.restrictPreimage f)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Set.restrictPreimage_surjective`：restrictPreimage_surjective (hf : Surje
ctive f) : Surjective (t.restrictPreimage f)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma restrictPreimage_bijective (hf : Bijective f) : Bijective (t.restrictPreimage f) :=
  ⟨t.restrictPreimage_injective hf.1, t.restrictPreimage_surjective hf.2⟩

alias _root_.Function.Injective.restrictPreimage := Set.restrictPreimage_injective
alias _root_.Function.Surjective.restrictPreimage := Set.restrictPreimage_surjective
alias _root_.Function.Bijective.restrictPreimage := Set.restrictPreimage_bijective

end

/-! ### Injectivity on a set -/
section injOn

/-
**Set.injOn_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：injOn_iff_injective : InjOn f s ↔ Injective (s.domRestrict f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem injOn_iff_injective : InjOn f s ↔ Injective (s.domRestrict f) :=
  ⟨fun H a b h => Subtype.ext <| H a.2 b.2 h, fun H a as b bs h =>
    congr_arg Subtype.val <| @H ⟨a, as⟩ ⟨b, bs⟩ h⟩

alias ⟨InjOn.injective, _⟩ := Set.injOn_iff_injective

set_option backward.isDefEq.respectTransparency false in
/-
**Set.MapsTo.restrict_inj** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} (h : S
et.MapsTo f s t),   Function.Injective (Set.MapsTo.restrict f s t h) ↔ Set.InjOn
 f s
参数：h : Set.MapsTo f s t；Set.MapsTo.restrict f s t h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.MapsTo.restrict_eq_codRestrict`：∀ {α : Type u_1} {β : Type u_2} {s :
 Set α} {t : Set β} {f : α → β} (h : Set.MapsTo f s t),   Set.MapsTo.restrict f 
s t h = Set.codRestrict …
· 使用定理 `Set.injective_codRestrict`：injective_codRestrict {f : ι -> α} {s : Set α
} (h : forall x, f x in s) : Injective (codRestrict f s h) ↔ Injective f
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem MapsTo.restrict_inj (h : MapsTo f s t) : Injective (h.restrict f s t) ↔ InjOn f s := by
  rw [h.restrict_eq_codRestrict, injective_codRestrict, injOn_iff_injective]

end injOn

/-! ### Surjectivity on a set -/
section surjOn

/-
**Set.surjOn_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：surjOn_iff_surjective : SurjOn f s univ ↔ Surjective (s.domRestrict f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem surjOn_iff_surjective : SurjOn f s univ ↔ Surjective (s.domRestrict f) :=
  ⟨fun H b =>
    let ⟨a, as, e⟩ := @H b trivial
    ⟨⟨a, as⟩, e⟩,
    fun H b _ =>
    let ⟨⟨a, as⟩, e⟩ := H b
    ⟨a, as, e⟩⟩

@[simp]
/-
**Set.MapsTo.restrict_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} (h : S
et.MapsTo f s t),   Function.Surjective (Set.MapsTo.restrict f s t h) ↔ Set.Surj
On f s t
参数：h : Set.MapsTo f s t；Set.MapsTo.restrict f s t h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem MapsTo.restrict_surjective_iff (h : MapsTo f s t) :
    Surjective (MapsTo.restrict _ _ _ h) ↔ SurjOn f s t := by
  refine ⟨fun h' b hb ↦ ?_, fun h' ⟨b, hb⟩ ↦ ?_⟩
  · obtain ⟨⟨a, ha⟩, ha'⟩ := h' ⟨b, hb⟩
    replace ha' : f a = b := by simpa [Subtype.ext_iff] using ha'
    rw [← ha']
    exact mem_image_of_mem f ha
  · obtain ⟨a, ha, rfl⟩ := h' hb
    exact ⟨⟨a, ha⟩, rfl⟩

end surjOn

end Set

