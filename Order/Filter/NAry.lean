/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Filter.Bases.Basic
public import Mathlib.Order.Filter.Prod

/-!
# N-ary maps of filter

This file defines the binary and ternary maps of filters. This is mostly useful to define pointwise
operations on filters.

## Main declarations

* `Filter.map₂`: Binary map of filters.

## Notes

This file is very similar to `Mathlib/Data/Set/NAry.lean`, `Mathlib/Data/Finset/NAry.lean` and
`Mathlib/Data/Option/NAry.lean`. Please keep them in sync.
-/

@[expose] public section


open Function Set

open Filter

namespace Filter

variable {α α' β β' γ γ' δ δ' ε ε' : Type*} {m : α → β → γ} {f f₁ f₂ : Filter α}
  {g g₁ g₂ : Filter β} {h : Filter γ} {s : Set α} {t : Set β} {u : Set γ}
  {a : α} {b : β}

/-- The image of a binary function `m : α → β → γ` as a function `Filter α → Filter β → Filter γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f

--- 原说明 ---
The image of a binary function `m : α → β → γ` as a function `Filter α → Filter 
β → Filter γ`.
Mathematically this should be thought of as the image of the corresponding funct
ion `α × β → γ`.
-/
def map₂ (m : α → β → γ) (f : Filter α) (g : Filter β) : Filter γ :=
  ((f ×ˢ g).map (uncurry m)).copy { s | ∃ u ∈ f, ∃ v ∈ g, image2 m u v ⊆ s } fun _ ↦ by
    simp only [mem_map, mem_prod_iff, image2_subset_iff, prod_subset_iff]; rfl

@[simp 900]
/-
**Filter.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_map : t in map m f ↔ m ⁻¹' t in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map₂_iff : u ∈ map₂ m f g ↔ ∃ s ∈ f, ∃ t ∈ g, image2 m s t ⊆ u :=
  Iff.rfl
/-
**Filter.image2_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image2_mem_map₂ (hs : s ∈ f) (ht : t ∈ g) : image2 m s t ∈ map₂ m f g :=
  ⟨_, hs, _, ht, Subset.rfl⟩
/-
**Filter.map_prod_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_prod_eq_map₂ (m : α → β → γ) (f : Filter α) (g : Filter β) :
    Filter.map (fun p : α × β => m p.1 p.2) (f ×ˢ g) = map₂ m f g := by
  rw [map₂, copy_eq, uncurry_def]
/-
**Filter.map_prod_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_prod_eq_map₂' (m : α × β → γ) (f : Filter α) (g : Filter β) :
    Filter.map m (f ×ˢ g) = map₂ (fun a b => m (a, b)) f g :=
  map_prod_eq_map₂ m.curry f g

@[simp]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_mk_eq_prod (f : Filter α) (g : Filter β) : map₂ Prod.mk f g = f ×ˢ g := by
  simp only [← map_prod_eq_map₂, map_id']
/-
**Filter.HasBasis.map** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l : Filter α} {p : ι → Pro
p} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filter.map f l).HasBasis p f
un i => f '' s i
参数：f : α → β；Filter.map f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma HasBasis.map₂ {ι ι' : Type*} {p : ι → Prop} {q : ι' → Prop} {s t}
    (m : α → β → γ) (hf : f.HasBasis p s) (hg : g.HasBasis q t) :
    (map₂ m f g).HasBasis (fun i : ι × ι' ↦ p i.1 ∧ q i.2) fun i ↦ image2 m (s i.1) (t i.2) := by
  simpa only [← map_prod_eq_map₂, ← image_prod] using (hf.prod hg).map _

-- lemma image2_mem_map₂_iff (hm : injective2 m) : image2 m s t ∈ map₂ m f g ↔ s ∈ f ∧ t ∈ g :=
-- ⟨by { rintro ⟨u, v, hu, hv, h⟩, rw image2_subset_image2_iff hm at h,
--   exact ⟨mem_of_superset hu h.1, mem_of_superset hv h.2⟩ }, fun h ↦ image2_mem_map₂ h.1 h.2⟩
@[gcongr]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : map₂ m f₁ g₁ ≤ map₂ m f₂ g₂ :=
  fun _ ⟨s, hs, t, ht, hst⟩ => ⟨s, hf hs, t, hg ht, hst⟩
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_mono_left (h : g₁ ≤ g₂) : map₂ m f g₁ ≤ map₂ m f g₂ :=
  map₂_mono Subset.rfl h
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_mono_right (h : f₁ ≤ f₂) : map₂ m f₁ g ≤ map₂ m f₂ g :=
  map₂_mono h Subset.rfl

@[simp]
/-
**Filter.le_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_map {f : Filter α} {m : α -> β} {g : Filter β} (h : forall s in f, m ''
 s in g) : g <= f.map m
参数：h : forall s in f, m '' s in g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
-/
theorem le_map₂_iff {h : Filter γ} :
    h ≤ map₂ m f g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → image2 m s t ∈ h :=
  ⟨fun H _ hs _ ht => H <| image2_mem_map₂ hs ht, fun H _ ⟨_, hs, _, ht, hu⟩ =>
    mem_of_superset (H hs ht) hu⟩

@[simp]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_eq_bot_iff : map₂ m f g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := by simp [← map_prod_eq_map₂]

@[simp]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_bot_left : map₂ m ⊥ g = ⊥ := map₂_eq_bot_iff.2 <| .inl rfl

@[simp]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_bot_right : map₂ m f ⊥ = ⊥ := map₂_eq_bot_iff.2 <| .inr rfl

@[simp]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_neBot_iff : (map₂ m f g).NeBot ↔ f.NeBot ∧ g.NeBot := by simp [neBot_iff, not_or]
/-
**Filter.NeBot.map** 是 Mathlib 中的一个定理，位于命名空间 `Filter.NeBot`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α}, f.NeBot → ∀ (m : α → β), (
Filter.map m f).NeBot
参数：m : α → β；Filter.map m f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.map_neBot_iff`：map_neBot_iff (f : α -> β) {F : Filter α} : NeBot 
(map f F) ↔ NeBot F
-/
protected theorem NeBot.map₂ (hf : f.NeBot) (hg : g.NeBot) : (map₂ m f g).NeBot :=
  map₂_neBot_iff.2 ⟨hf, hg⟩
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
instance map₂.neBot [NeBot f] [NeBot g] : NeBot (map₂ m f g) := .map₂ ‹_› ‹_›
/-
**Filter.NeBot.of_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter.NeBot`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {m : α → β}, (Filter.map m 
f).NeBot → f.NeBot
参数：Filter.map m f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.map_neBot_iff`：map_neBot_iff (f : α -> β) {F : Filter α} : NeBot 
(map f F) ↔ NeBot F
-/
theorem NeBot.of_map₂_left (h : (map₂ m f g).NeBot) : f.NeBot :=
  (map₂_neBot_iff.1 h).1
/-
**Filter.NeBot.of_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter.NeBot`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {m : α → β}, (Filter.map m 
f).NeBot → f.NeBot
参数：Filter.map m f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.map_neBot_iff`：map_neBot_iff (f : α -> β) {F : Filter α} : NeBot 
(map f F) ↔ NeBot F
-/
theorem NeBot.of_map₂_right (h : (map₂ m f g).NeBot) : g.NeBot :=
  (map₂_neBot_iff.1 h).2
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_sup_left : map₂ m (f₁ ⊔ f₂) g = map₂ m f₁ g ⊔ map₂ m f₂ g := by
  simp_rw [← map_prod_eq_map₂, sup_prod, map_sup]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_sup_right : map₂ m f (g₁ ⊔ g₂) = map₂ m f g₁ ⊔ map₂ m f g₂ := by
  simp_rw [← map_prod_eq_map₂, prod_sup, map_sup]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_inf_subset_left : map₂ m (f₁ ⊓ f₂) g ≤ map₂ m f₁ g ⊓ map₂ m f₂ g :=
  Monotone.map_inf_le (fun _ _ ↦ map₂_mono_right) f₁ f₂
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_inf_subset_right : map₂ m f (g₁ ⊓ g₂) ≤ map₂ m f g₁ ⊓ map₂ m f g₂ :=
  Monotone.map_inf_le (fun _ _ ↦ map₂_mono_left) g₁ g₂

@[simp]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_pure_left : map₂ m (pure a) g = g.map (m a) := by
  rw [← map_prod_eq_map₂, pure_prod, map_map]; rfl

@[simp]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_pure_right : map₂ m f (pure b) = f.map (m · b) := by
  rw [← map_prod_eq_map₂, prod_pure, map_map]; rfl
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_pure : map₂ m (pure a) (pure b) = pure (m a b) := by rw [map₂_pure_right, map_pure]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_swap (m : α → β → γ) (f : Filter α) (g : Filter β) :
    map₂ m f g = map₂ (fun a b => m b a) g f := by
  rw [← map_prod_eq_map₂, prod_comm, map_map, ← map_prod_eq_map₂, Function.comp_def]
  simp

@[simp]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_left [NeBot g] : map₂ (fun x _ => x) f g = f := by
  rw [← map_prod_eq_map₂, map_fst_prod]

@[simp]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_right [NeBot f] : map₂ (fun _ y => y) f g = g := by rw [map₂_swap, map₂_left]
/-
**Filter.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_map : Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Filter.map_compose`：map_compose : Filter.map m' ∘ Filter.map m = Filter.
map (m' ∘ m)
-/
theorem map_map₂ (m : α → β → γ) (n : γ → δ) :
    (map₂ m f g).map n = map₂ (fun a b => n (m a b)) f g := by
  rw [← map_prod_eq_map₂, ← map_prod_eq_map₂, map_map]; rfl
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_map_left (m : γ → β → δ) (n : α → γ) :
    map₂ m (f.map n) g = map₂ (fun a b => m (n a) b) f g := by
  rw [← map_prod_eq_map₂, ← map_prod_eq_map₂, ← @map_id _ g, prod_map_map_eq, map_map, map_id]; rfl
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_map_right (m : α → γ → δ) (n : β → γ) :
    map₂ m f (g.map n) = map₂ (fun a b => m a (n b)) f g := by
  rw [map₂_swap, map₂_map_left, map₂_swap]

@[simp]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_curry (m : α × β → γ) (f : Filter α) (g : Filter β) :
    map₂ m.curry f g = (f ×ˢ g).map m :=
  (map_prod_eq_map₂' _ _ _).symm

@[simp]
/-
**Filter.map_uncurry_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_uncurry_prod (m : α -> β -> γ) (f : Filter α) (g : Filter β) : (f ×ˢ g
).map (uncurry m) = map₂ m f g
参数：m : α -> β -> γ；f : Filter α；g : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map₂_curry`：map₂_curry (m : α × β -> γ) (f : Filter α) (g : Filte
r β) : map₂ m.curry f g = (f ×ˢ g).map m
-/
theorem map_uncurry_prod (m : α → β → γ) (f : Filter α) (g : Filter β) :
    (f ×ˢ g).map (uncurry m) = map₂ m f g :=
  (map₂_curry (uncurry m) f g).symm

/-!
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity, ... of operations
to the associativity, commutativity, distributivity, ... of `Filter.map₂` of those operations.

The proof pattern is `map₂_lemma operation_lemma`. For example, `map₂_comm mul_comm` proves that
`map₂ (*) f g = map₂ (*) g f` in a `CommSemigroup`.
-/

/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f

--- 原说明 ---
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity,
 ... of operations
to the associativity, commutativity, distributivity, ... of `Filter.map₂` of tho
se operations.

The proof pattern is `map₂_lemma operation_lemma`. For example, `map₂_comm mul_c
omm` proves that
`map₂ (*) f g = map₂ (*) g f` in a `CommSemigroup`.
-/
theorem map₂_assoc {m : δ → γ → ε} {n : α → β → δ} {m' : α → ε' → ε} {n' : β → γ → ε'}
    {h : Filter γ} (h_assoc : ∀ a b c, m (n a b) c = m' a (n' b c)) :
    map₂ m (map₂ n f g) h = map₂ m' f (map₂ n' g h) := by
  rw [← map_prod_eq_map₂ n, ← map_prod_eq_map₂ n', map₂_map_left, map₂_map_right,
    ← map_prod_eq_map₂, ← map_prod_eq_map₂, ← prod_assoc, map_map]
  simp only [h_assoc, Function.comp_def, Equiv.prodAssoc_apply]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_comm {n : β → α → γ} (h_comm : ∀ a b, m a b = n b a) : map₂ m f g = map₂ n g f :=
  (map₂_swap _ _ _).trans <| by simp_rw [h_comm]
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_left_comm {m : α → δ → ε} {n : β → γ → δ} {m' : α → γ → δ'} {n' : β → δ' → ε}
    (h_left_comm : ∀ a b c, m a (n b c) = n' b (m' a c)) :
    map₂ m f (map₂ n g h) = map₂ n' g (map₂ m' f h) := by
  rw [map₂_swap m', map₂_swap m]
  exact map₂_assoc fun _ _ _ => h_left_comm _ _ _
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem map₂_right_comm {m : δ → γ → ε} {n : α → β → δ} {m' : α → γ → δ'} {n' : δ' → β → ε}
    (h_right_comm : ∀ a b c, m (n a b) c = n' (m' a c) b) :
    map₂ m (map₂ n f g) h = map₂ n' (map₂ m' f h) g := by
  rw [map₂_swap n, map₂_swap n']
  exact map₂_assoc fun _ _ _ => h_right_comm _ _ _
/-
**Filter.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_map : Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Filter.map_compose`：map_compose : Filter.map m' ∘ Filter.map m = Filter.
map (m' ∘ m)
-/
theorem map_map₂_distrib {n : γ → δ} {m' : α' → β' → δ} {n₁ : α → α'} {n₂ : β → β'}
    (h_distrib : ∀ a b, n (m a b) = m' (n₁ a) (n₂ b)) :
    (map₂ m f g).map n = map₂ m' (f.map n₁) (g.map n₂) := by
  simp_rw [map_map₂, map₂_map_left, map₂_map_right, h_distrib]

/-- Symmetric statement to `Filter.map₂_map_left_comm`. -/
/-
**Filter.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_map : Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Filter.map_compose`：map_compose : Filter.map m' ∘ Filter.map m = Filter.
map (m' ∘ m)

--- 原说明 ---
Symmetric statement to `Filter.map₂_map_left_comm`.
-/
theorem map_map₂_distrib_left {n : γ → δ} {m' : α' → β → δ} {n' : α → α'}
    (h_distrib : ∀ a b, n (m a b) = m' (n' a) b) : (map₂ m f g).map n = map₂ m' (f.map n') g :=
  map_map₂_distrib h_distrib

/-- Symmetric statement to `Filter.map_map₂_right_comm`. -/
/-
**Filter.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_map : Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Filter.map_compose`：map_compose : Filter.map m' ∘ Filter.map m = Filter.
map (m' ∘ m)

--- 原说明 ---
Symmetric statement to `Filter.map_map₂_right_comm`.
-/
theorem map_map₂_distrib_right {n : γ → δ} {m' : α → β' → δ} {n' : β → β'}
    (h_distrib : ∀ a b, n (m a b) = m' a (n' b)) : (map₂ m f g).map n = map₂ m' f (g.map n') :=
  map_map₂_distrib h_distrib

/-- Symmetric statement to `Filter.map_map₂_distrib_left`. -/
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f

--- 原说明 ---
Symmetric statement to `Filter.map_map₂_distrib_left`.
-/
theorem map₂_map_left_comm {m : α' → β → γ} {n : α → α'} {m' : α → β → δ} {n' : δ → γ}
    (h_left_comm : ∀ a b, m (n a) b = n' (m' a b)) : map₂ m (f.map n) g = (map₂ m' f g).map n' :=
  (map_map₂_distrib_left fun a b => (h_left_comm a b).symm).symm

/-- Symmetric statement to `Filter.map_map₂_distrib_right`. -/
/-
**Filter.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_map : Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Filter.map_compose`：map_compose : Filter.map m' ∘ Filter.map m = Filter.
map (m' ∘ m)

--- 原说明 ---
Symmetric statement to `Filter.map_map₂_distrib_right`.
-/
theorem map_map₂_right_comm {m : α → β' → γ} {n : β → β'} {m' : α → β → δ} {n' : δ → γ}
    (h_right_comm : ∀ a b, m a (n b) = n' (m' a b)) : map₂ m f (g.map n) = (map₂ m' f g).map n' :=
  (map_map₂_distrib_right fun a b => (h_right_comm a b).symm).symm

/-- The other direction does not hold because of the `f-f` cross terms on the RHS. -/
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f

--- 原说明 ---
The other direction does not hold because of the `f-f` cross terms on the RHS.
-/
theorem map₂_distrib_le_left {m : α → δ → ε} {n : β → γ → δ} {m₁ : α → β → β'} {m₂ : α → γ → γ'}
    {n' : β' → γ' → ε} (h_distrib : ∀ a b c, m a (n b c) = n' (m₁ a b) (m₂ a c)) :
    map₂ m f (map₂ n g h) ≤ map₂ n' (map₂ m₁ f g) (map₂ m₂ f h) := by
  rintro s ⟨t₁, ⟨u₁, hu₁, v, hv, ht₁⟩, t₂, ⟨u₂, hu₂, w, hw, ht₂⟩, hs⟩
  refine ⟨u₁ ∩ u₂, inter_mem hu₁ hu₂, _, image2_mem_map₂ hv hw, ?_⟩
  refine (image2_distrib_subset_left h_distrib).trans ((image2_subset ?_ ?_).trans hs)
  · exact (image2_subset_right inter_subset_left).trans ht₁
  · exact (image2_subset_right inter_subset_right).trans ht₂

/-- The other direction does not hold because of the `h`-`h` cross terms on the RHS. -/
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f

--- 原说明 ---
The other direction does not hold because of the `h`-`h` cross terms on the RHS.
-/
theorem map₂_distrib_le_right {m : δ → γ → ε} {n : α → β → δ} {m₁ : α → γ → α'} {m₂ : β → γ → β'}
    {n' : α' → β' → ε} (h_distrib : ∀ a b c, m (n a b) c = n' (m₁ a c) (m₂ b c)) :
    map₂ m (map₂ n f g) h ≤ map₂ n' (map₂ m₁ f h) (map₂ m₂ g h) := by
  rintro s ⟨t₁, ⟨u, hu, w₁, hw₁, ht₁⟩, t₂, ⟨v, hv, w₂, hw₂, ht₂⟩, hs⟩
  refine ⟨_, image2_mem_map₂ hu hv, w₁ ∩ w₂, inter_mem hw₁ hw₂, ?_⟩
  refine (image2_distrib_subset_right h_distrib).trans ((image2_subset ?_ ?_).trans hs)
  · exact (image2_subset_left inter_subset_left).trans ht₁
  · exact (image2_subset_left inter_subset_right).trans ht₂
/-
**Filter.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_map : Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Filter.map_compose`：map_compose : Filter.map m' ∘ Filter.map m = Filter.
map (m' ∘ m)
-/
theorem map_map₂_antidistrib {n : γ → δ} {m' : β' → α' → δ} {n₁ : β → β'} {n₂ : α → α'}
    (h_antidistrib : ∀ a b, n (m a b) = m' (n₁ b) (n₂ a)) :
    (map₂ m f g).map n = map₂ m' (g.map n₁) (f.map n₂) := by
  rw [map₂_swap m]
  exact map_map₂_distrib fun _ _ => h_antidistrib _ _

/-- Symmetric statement to `Filter.map₂_map_left_anticomm`. -/
/-
**Filter.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_map : Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Filter.map_compose`：map_compose : Filter.map m' ∘ Filter.map m = Filter.
map (m' ∘ m)

--- 原说明 ---
Symmetric statement to `Filter.map₂_map_left_anticomm`.
-/
theorem map_map₂_antidistrib_left {n : γ → δ} {m' : β' → α → δ} {n' : β → β'}
    (h_antidistrib : ∀ a b, n (m a b) = m' (n' b) a) : (map₂ m f g).map n = map₂ m' (g.map n') f :=
  map_map₂_antidistrib h_antidistrib

/-- Symmetric statement to `Filter.map_map₂_right_anticomm`. -/
/-
**Filter.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_map : Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Filter.map_compose`：map_compose : Filter.map m' ∘ Filter.map m = Filter.
map (m' ∘ m)

--- 原说明 ---
Symmetric statement to `Filter.map_map₂_right_anticomm`.
-/
theorem map_map₂_antidistrib_right {n : γ → δ} {m' : β → α' → δ} {n' : α → α'}
    (h_antidistrib : ∀ a b, n (m a b) = m' b (n' a)) : (map₂ m f g).map n = map₂ m' g (f.map n') :=
  map_map₂_antidistrib h_antidistrib

/-- Symmetric statement to `Filter.map_map₂_antidistrib_left`. -/
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f

--- 原说明 ---
Symmetric statement to `Filter.map_map₂_antidistrib_left`.
-/
theorem map₂_map_left_anticomm {m : α' → β → γ} {n : α → α'} {m' : β → α → δ} {n' : δ → γ}
    (h_left_anticomm : ∀ a b, m (n a) b = n' (m' b a)) :
    map₂ m (f.map n) g = (map₂ m' g f).map n' :=
  (map_map₂_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm

/-- Symmetric statement to `Filter.map_map₂_antidistrib_right`. -/
/-
**Filter.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_map : Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Filter.map_compose`：map_compose : Filter.map m' ∘ Filter.map m = Filter.
map (m' ∘ m)

--- 原说明 ---
Symmetric statement to `Filter.map_map₂_antidistrib_right`.
-/
theorem map_map₂_right_anticomm {m : α → β' → γ} {n : β → β'} {m' : β → α → δ} {n' : δ → γ}
    (h_right_anticomm : ∀ a b, m a (n b) = n' (m' b a)) :
    map₂ m f (g.map n) = (map₂ m' g f).map n' :=
  (map_map₂_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm

/-- If `a` is a left identity for `f : α → β → β`, then `pure a` is a left identity for
`Filter.map₂ f`. -/
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f

--- 原说明 ---
If `a` is a left identity for `f : α → β → β`, then `pure a` is a left identity 
for
`Filter.map₂ f`.
-/
theorem map₂_left_identity {f : α → β → β} {a : α} (h : ∀ b, f a b = b) (l : Filter β) :
    map₂ f (pure a) l = l := by rw [map₂_pure_left, show f a = id from funext h, map_id]

/-- If `b` is a right identity for `f : α → β → α`, then `pure b` is a right identity for
`Filter.map₂ f`. -/
/-
**Filter.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：map (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f

--- 原说明 ---
If `b` is a right identity for `f : α → β → α`, then `pure b` is a right identit
y for
`Filter.map₂ f`.
-/
theorem map₂_right_identity {f : α → β → α} {b : β} (h : ∀ a, f a b = a) (l : Filter α) :
    map₂ f l (pure b) = l := by rw [map₂_pure_right, funext h, map_id']

end Filter

