/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
module

public import Mathlib.Control.Basic
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Order.Filter.Basic

/-!
# Theorems about map and comap on filters.
-/

@[expose] public section

assert_not_exists IsOrderedRing Fintype

open Function Set Order
open scoped symmDiff

universe u v w x y

namespace Filter

variable {α β γ δ : Type*} {ι : Sort*} {F : Filter α} {G : Filter β}

/-! ### Push-forwards, pull-backs, and the monad structure -/

section Map

@[simp]
/-
**Filter.map_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_principal {s : Set α} {f : α -> β} : map f (𝓟 s) = 𝓟 (Set.image f s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_principal {s : Set α} {f : α → β} : map f (𝓟 s) = 𝓟 (Set.image f s) :=
  Filter.ext fun _ => image_subset_iff.symm

variable {f : Filter α} {m : α → β} {m' : β → γ} {s : Set α} {t : Set β}

@[simp]
/-
**Filter.eventually_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_map {P : β -> Prop} : (forallᶠ b in map m f, P b) ↔ forallᶠ a i
n f, P (m a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_map {P : β → Prop} : (∀ᶠ b in map m f, P b) ↔ ∀ᶠ a in f, P (m a) :=
  Iff.rfl

@[simp]
/-
**Filter.frequently_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_map {P : β -> Prop} : (existsᶠ b in map m f, P b) ↔ existsᶠ a i
n f, P (m a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem frequently_map {P : β → Prop} : (∃ᶠ b in map m f, P b) ↔ ∃ᶠ a in f, P (m a) :=
  Iff.rfl

@[simp]
/-
**Filter.eventuallyEq_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyEq_map {f₁ f₂ : β -> γ} : f₁ =ᶠ[map m f] f₂ ↔ f₁ ∘ m =ᶠ[f] f₂ ∘ 
m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventuallyEq_map {f₁ f₂ : β → γ} : f₁ =ᶠ[map m f] f₂ ↔ f₁ ∘ m =ᶠ[f] f₂ ∘ m := .rfl

@[simp]
/-
**Filter.eventuallyLE_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyLE_map [LE γ] {f₁ f₂ : β -> γ} : f₁ <=ᶠ[map m f] f₂ ↔ f₁ ∘ m <=ᶠ
[f] f₂ ∘ m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventuallyLE_map [LE γ] {f₁ f₂ : β → γ} : f₁ ≤ᶠ[map m f] f₂ ↔ f₁ ∘ m ≤ᶠ[f] f₂ ∘ m := .rfl

@[simp]
/-
**Filter.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_map : t in map m f ↔ m ⁻¹' t in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map : t ∈ map m f ↔ m ⁻¹' t ∈ f :=
  Iff.rfl
/-
**Filter.mem_map'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_map' : t in map m f ↔ { x | m x in t } in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map' : t ∈ map m f ↔ { x | m x ∈ t } ∈ f :=
  Iff.rfl
/-
**Filter.image_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：image_mem_map (hs : s in f) : m '' s in map m f
参数：hs : s in f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.sets_of_superset`：∀ {α : Type u_1} (self : Filter α) {x y : Set α
}, x ∈ self.sets → x ⊆ y → y ∈ self.sets
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
-/
theorem image_mem_map (hs : s ∈ f) : m '' s ∈ map m f :=
  f.sets_of_superset hs <| subset_preimage_image m s

@[simp 1100]
/-
**Filter.image_mem_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：image_mem_map_iff (hf : Injective m) : m '' s in map m f ↔ s in f
参数：hf : Injective m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
-/
theorem image_mem_map_iff (hf : Injective m) : m '' s ∈ map m f ↔ s ∈ f :=
  ⟨fun h => by rwa [← preimage_image_eq s hf], image_mem_map⟩
/-
**Filter.range_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：range_mem_map : range m in map m f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem range_mem_map : range m ∈ map m f := by
  rw [← image_univ]
  exact image_mem_map univ_mem
/-
**Filter.mem_map_iff_exists_image** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_map_iff_exists_image : t in map m f ↔ exists s in f, m '' s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
-/
theorem mem_map_iff_exists_image : t ∈ map m f ↔ ∃ s ∈ f, m '' s ⊆ t :=
  ⟨fun ht => ⟨m ⁻¹' t, ht, image_preimage_subset _ _⟩, fun ⟨_, hs, ht⟩ =>
    mem_of_superset (image_mem_map hs) ht⟩

@[simp]
/-
**Filter.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_id : Filter.map id f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.filter_eq`：∀ {α : Type u_1} {f g : Filter α}, f.sets = g.sets → f
 = g
-/
theorem map_id : Filter.map id f = f :=
  filter_eq <| rfl

@[simp]
/-
**Filter.map_id'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_id' : Filter.map (fun x => x) f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_id`：map_id : Filter.map id f = f
-/
theorem map_id' : Filter.map (fun x => x) f = f :=
  map_id

@[simp]
/-
**Filter.map_compose** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_compose : Filter.map m' ∘ Filter.map m = Filter.map (m' ∘ m)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.filter_eq`：∀ {α : Type u_1} {f g : Filter α}, f.sets = g.sets → f
 = g
-/
theorem map_compose : Filter.map m' ∘ Filter.map m = Filter.map (m' ∘ m) :=
  funext fun _ => filter_eq <| rfl

@[simp]
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
theorem map_map : Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f :=
  congr_fun Filter.map_compose f

/-- If functions `m₁` and `m₂` are eventually equal at a filter `f`, then
they map this filter to the same filter. -/
/-
**Filter.map_congr** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_congr {m₁ m₂ : α -> β} {f : Filter α} (h : m₁ =ᶠ[f] m₂) : map m₁ f = m
ap m₂ f
参数：h : m₁ =ᶠ[f] m₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext'`：∀ {α : Type u} {f₁ f₂ : Filter α}, (∀ (p : α → Prop), (∀ᶠ (
x : α) in f₁, p x) ↔ ∀ᶠ (x : α) in f₂, p x) → f₁ = f₂
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If functions `m₁` and `m₂` are eventually equal at a filter `f`, then
they map this filter to the same filter.
-/
theorem map_congr {m₁ m₂ : α → β} {f : Filter α} (h : m₁ =ᶠ[f] m₂) : map m₁ f = map m₂ f :=
  Filter.ext' fun _ => eventually_congr (h.mono fun _ hx => hx ▸ Iff.rfl)

end Map

section Comap

variable {f : α → β} {l : Filter β} {p : α → Prop} {s : Set α}

/-
**Filter.mem_comap'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_comap' : s in comap f l ↔ { y | forall ⦃x⦄, f x = y -> x in s } in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem mem_comap' : s ∈ comap f l ↔ { y | ∀ ⦃x⦄, f x = y → x ∈ s } ∈ l :=
  ⟨fun ⟨t, ht, hts⟩ => mem_of_superset ht fun y hy x hx => hts <| mem_preimage.2 <| by rwa [hx],
    fun h => ⟨_, h, fun _ hx => hx rfl⟩⟩

-- TODO: it would be nice to use `kernImage` much more to take advantage of common name and API,
-- and then this would become `mem_comap'`
/-
**Filter.mem_comap''** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_comap'' : s in comap f l ↔ kernImage f s in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_comap'`：mem_comap' : s in comap f l ↔ { y | forall ⦃x⦄, f x =
 y -> x in s } in l
-/
theorem mem_comap'' : s ∈ comap f l ↔ kernImage f s ∈ l :=
  mem_comap'

/-- RHS form is used, e.g., in the definition of `UniformSpace`. -/
/-
**Filter.mem_comap_prodMk** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：mem_comap_prodMk {x : α} {s : Set β} {F : Filter (α × β)} : s in comap (Pr
od.mk x) F ↔ {p : α × β | p.fst = x -> p.snd in s} in F
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
RHS form is used, e.g., in the definition of `UniformSpace`.
-/
lemma mem_comap_prodMk {x : α} {s : Set β} {F : Filter (α × β)} :
    s ∈ comap (Prod.mk x) F ↔ {p : α × β | p.fst = x → p.snd ∈ s} ∈ F := by
  simp_rw [mem_comap', Prod.ext_iff, and_imp, @forall_comm β (_ = _), forall_eq, eq_comm]

@[simp]
/-
**Filter.eventually_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_comap : (forallᶠ a in comap f l, p a) ↔ forallᶠ b in l, forall 
a, f a = b -> p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_comap'`：mem_comap' : s in comap f l ↔ { y | forall ⦃x⦄, f x =
 y -> x in s } in l
-/
theorem eventually_comap : (∀ᶠ a in comap f l, p a) ↔ ∀ᶠ b in l, ∀ a, f a = b → p a :=
  mem_comap'

@[simp]
/-
**Filter.frequently_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_comap : (existsᶠ a in comap f l, p a) ↔ existsᶠ b in l, exists 
a, f a = b ∧ p a
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_comap : (∃ᶠ a in comap f l, p a) ↔ ∃ᶠ b in l, ∃ a, f a = b ∧ p a := by
  simp only [Filter.Frequently, eventually_comap, not_exists, _root_.not_and]
/-
**Filter.mem_comap_iff_compl** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_comap_iff_compl : s in comap f l ↔ (f '' sᶜ)ᶜ in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.kernImage_eq_compl`：kernImage_eq_compl {s : Set α} : kernImage f s =
 (f '' sᶜ)ᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_comap_iff_compl : s ∈ comap f l ↔ (f '' sᶜ)ᶜ ∈ l := by
  simp only [mem_comap'', kernImage_eq_compl]
/-
**Filter.compl_mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：compl_mem_comap : sᶜ in comap f l ↔ (f '' s)ᶜ in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_comap_iff_compl`：mem_comap_iff_compl : s in comap f l ↔ (f ''
 sᶜ)ᶜ in l
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem compl_mem_comap : sᶜ ∈ comap f l ↔ (f '' s)ᶜ ∈ l := by rw [mem_comap_iff_compl, compl_compl]

end Comap


/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulFunctor (Filter : Type u → Type u) where
  id_map _ := map_id
  comp_map _ _ _ := map_map.symm
  map_const := rfl
/-
**Filter.pure_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pure_sets (a : α) : (pure a : Filter α).sets = { s | a in s }
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pure_sets (a : α) : (pure a : Filter α).sets = { s | a ∈ s } :=
  rfl

@[simp]
/-
**Filter.eventually_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_pure {a : α} {p : α -> Prop} : (forallᶠ x in pure a, p x) ↔ p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_pure {a : α} {p : α → Prop} : (∀ᶠ x in pure a, p x) ↔ p a :=
  Iff.rfl

@[simp]
/-
**Filter.frequently_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_pure {a : α} {p : α -> Prop} : (existsᶠ x in pure a, p x) ↔ p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_pure {a : α} {p : α → Prop} : (∃ᶠ x in pure a, p x) ↔ p a := by
  simp [Filter.Frequently]

@[simp]
/-
**Filter.principal_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：principal_singleton (a : α) : 𝓟 {a} = pure a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem principal_singleton (a : α) : 𝓟 {a} = pure a :=
  Filter.ext fun s => by simp only [mem_pure, mem_principal, singleton_subset_iff]

@[simp]
/-
**Filter.biSup_pure_eq_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：biSup_pure_eq_principal (s : Set α) : ⨆ a in s, pure a = 𝓟 s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem biSup_pure_eq_principal (s : Set α) : ⨆ a ∈ s, pure a = 𝓟 s :=
  Filter.ext fun s => by simp [Set.subset_def]

@[simp]
/-
**Filter.iSup_pure_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iSup_pure_eq_top : ⨆ a, pure a = (⊤ : Filter α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `Filter.biSup_pure_eq_principal`：biSup_pure_eq_principal (s : Set α) : ⨆ 
a in s, pure a = 𝓟 s
· 使用定理 `iSup_univ`：iSup_univ {f : β -> α} : ⨆ x in (univ : Set β), f x = ⨆ x, f 
x
-/
theorem iSup_pure_eq_top : ⨆ a, pure a = (⊤ : Filter α) := by
  rw [← principal_univ, ← biSup_pure_eq_principal, iSup_univ]

@[simp]
/-
**Filter.map_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_pure (f : α -> β) (a : α) : map f (pure a) = pure (f a)
参数：f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_pure (f : α → β) (a : α) : map f (pure a) = pure (f a) :=
  rfl
/-
**Filter.pure_le_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pure_le_principal {s : Set α} (a : α) : pure a <= 𝓟 s ↔ a in s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pure_le_principal {s : Set α} (a : α) : pure a ≤ 𝓟 s ↔ a ∈ s := by
  simp
/-
**Filter.join_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} (f : Filter α), (pure f).join = f
参数：f : Filter α；pure f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem join_pure (f : Filter α) : join (pure f) = f := rfl

@[simp]
/-
**Filter.pure_bind** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pure_bind (a : α) (m : α -> Filter β) : bind (pure a) m = m a
参数：a : α；m : α -> Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pure_bind (a : α) (m : α → Filter β) : bind (pure a) m = m a := by
  simp only [bind, map_pure, join_pure]
/-
**Filter.map_bind** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_bind {α β} (m : β -> γ) (f : Filter α) (g : α -> Filter β) : map m (bi
nd f g) = bind f (map m ∘ g)
参数：m : β -> γ；f : Filter α；g : α -> Filter β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_bind {α β} (m : β → γ) (f : Filter α) (g : α → Filter β) :
    map m (bind f g) = bind f (map m ∘ g) :=
  rfl
/-
**Filter.bind_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bind_map {α β} (m : α -> β) (f : Filter α) (g : β -> Filter γ) : (bind (ma
p m f) g) = bind f (g ∘ m)
参数：m : α -> β；f : Filter α；g : β -> Filter γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_map {α β} (m : α → β) (f : Filter α) (g : β → Filter γ) :
    (bind (map m f) g) = bind f (g ∘ m) :=
  rfl

/-!
### `Filter` as a `Monad`

In this section we define `Filter.monad`, a `Monad` structure on `Filter`s. This definition is not
an instance because its `Seq` projection is not equal to the `Filter.seq` function we use in the
`Applicative` instance on `Filter`.
-/

section

/-- The monad structure on filters. -/
@[instance_reducible]
/-
**Filter.monad** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：Monad Filter
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monad structure on filters.
-/
protected def monad : Monad Filter where map := @Filter.map

attribute [local instance] Filter.monad
/-
**Filter.lawfulMonad** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：LawfulMonad Filter
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem lawfulMonad : LawfulMonad Filter where
  map_const := rfl
  id_map _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl

end

/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Alternative Filter where
  seq := fun x y => x.seq (y ())
  failure := ⊥
  orElse x y := x ⊔ y ()

@[simp]
/-
**Filter.map_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_def {α β} (m : α -> β) (f : Filter α) : m < > f = map m f
参数：m : α -> β；f : Filter α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_def {α β} (m : α → β) (f : Filter α) : m <$> f = map m f :=
  rfl

@[simp]
/-
**Filter.bind_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bind_def {α β} (f : Filter α) (m : α -> Filter β) : f >>= m = bind f m
参数：f : Filter α；m : α -> Filter β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_def {α β} (f : Filter α) (m : α → Filter β) : f >>= m = bind f m :=
  rfl

/-! #### `map` and `comap` equations -/

section Map

variable {f f₁ f₂ : Filter α} {g g₁ g₂ : Filter β} {m : α → β} {m' : β → γ} {s : Set α} {t : Set β}

/-
**Filter.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} {m : α → β} {s : Set α}, s 
∈ Filter.comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mem_comap : s ∈ comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s := Iff.rfl
/-
**Filter.preimage_mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：preimage_mem_comap (ht : t in g) : m ⁻¹' t in comap m g
参数：ht : t in g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem preimage_mem_comap (ht : t ∈ g) : m ⁻¹' t ∈ comap m g :=
  ⟨t, ht, Subset.rfl⟩
/-
**Filter.Eventually.comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} {p : β → Prop},   (∀ᶠ (b : 
β) in g, p b) → ∀ (f : α → β), ∀ᶠ (a : α) in Filter.comap f g, p (f a)
参数：∀ᶠ (b : β) in g, p b；f : α → β；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
-/
theorem Eventually.comap {p : β → Prop} (hf : ∀ᶠ b in g, p b) (f : α → β) :
    ∀ᶠ a in comap f g, p (f a) :=
  preimage_mem_comap hf

@[simp]
/-
**Filter.EventuallyEq.comp_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {F : Filter β} {f g : β → γ
} (h : α → β),   f =ᶠ[F] g → f ∘ h =ᶠ[Filter.comap h F] g ∘ h
参数：h : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} 
{p : β → Prop},   (∀ᶠ (b : β) in g, p b) → ∀ (f : α → β), ∀ᶠ (a : α) in Filter.c
omap f g, p (…
-/
lemma EventuallyEq.comp_comap {F : Filter β} {f g : β → γ} (h : α → β)
    (hfg : f =ᶠ[F] g) : f.comp h =ᶠ[comap h F] g.comp h :=
  hfg.comap _
/-
**Filter.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_id : comap id f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
theorem comap_id : comap id f = f :=
  le_antisymm (fun _ => preimage_mem_comap) fun _ ⟨_, ht, hst⟩ => mem_of_superset ht hst
/-
**Filter.comap_id'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_id' : comap (fun x => x) f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_id`：comap_id : comap id f = f
-/
theorem comap_id' : comap (fun x => x) f = f := comap_id
/-
**Filter.comap_const_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_const_of_notMem {x : β} (ht : t in g) (hx : x ∉ t) : comap (fun _ : 
α => x) g = ⊥
参数：ht : t in g；hx : x ∉ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_comap'`：mem_comap' : s in comap f l ↔ { y | forall ⦃x⦄, f x =
 y -> x in s } in l
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem comap_const_of_notMem {x : β} (ht : t ∈ g) (hx : x ∉ t) : comap (fun _ : α => x) g = ⊥ :=
  empty_mem_iff_bot.1 <| mem_comap'.2 <| mem_of_superset ht fun _ hx' _ h => hx <| h.symm ▸ hx'
/-
**Filter.comap_const_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_const_of_mem {x : β} (h : forall t in g, x in t) : comap (fun _ : α 
=> x) g = ⊤
参数：h : forall t in g, x in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_comap'`：mem_comap' : s in comap f l ↔ { y | forall ⦃x⦄, f x =
 y -> x in s } in l
-/
theorem comap_const_of_mem {x : β} (h : ∀ t ∈ g, x ∈ t) : comap (fun _ : α => x) g = ⊤ :=
  top_unique fun _ hs => univ_mem' fun _ => h _ (mem_comap'.1 hs) rfl
/-
**Filter.map_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_const [NeBot f] {c : β} : (f.map fun _ => c) = pure c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_const_of_mem`：preimage_const_of_mem {b : β} {s : Set β} (h 
: b in s) : (fun _ : α => b) ⁻¹' s = univ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.preimage_const_of_notMem`：preimage_const_of_notMem {b : β} {s : Set 
β} (h : b ∉ s) : (fun _ : α => b) ⁻¹' s = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem map_const [NeBot f] {c : β} : (f.map fun _ => c) = pure c := by
  ext s
  by_cases h : c ∈ s <;> simp [h]
/-
**Filter.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_comap {m : γ -> β} {n : β -> α} : comap m (comap n f) = comap (n ∘ m
) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.coext`：∀ {α : Type u} {f g : Filter α}, (∀ (s : Set α), sᶜ ∈ f ↔ 
sᶜ ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_comap {m : γ → β} {n : β → α} : comap m (comap n f) = comap (n ∘ m) f :=
  Filter.coext fun s => by simp only [compl_mem_comap, image_image, (· ∘ ·)]

section comm

/-!
The variables in the following lemmas are used as in this diagram:
```
    φ
  α → β
θ ↓   ↓ ψ
  γ → δ
    ρ
```
-/


variable {φ : α → β} {θ : α → γ} {ψ : β → δ} {ρ : γ → δ}

/-
**Filter.map_comm** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_comm (H : ψ ∘ φ = ρ ∘ θ) (F : Filter α) : map ψ (map φ F) = map ρ (map
 θ F)
参数：H : ψ ∘ φ = ρ ∘ θ；F : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_comm (H : ψ ∘ φ = ρ ∘ θ) (F : Filter α) :
    map ψ (map φ F) = map ρ (map θ F) := by
  rw [Filter.map_map, H, ← Filter.map_map]
/-
**Filter.comap_comm** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_comm (H : ψ ∘ φ = ρ ∘ θ) (G : Filter δ) : comap φ (comap ψ G) = coma
p θ (comap ρ G)
参数：H : ψ ∘ φ = ρ ∘ θ；G : Filter δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem comap_comm (H : ψ ∘ φ = ρ ∘ θ) (G : Filter δ) :
    comap φ (comap ψ G) = comap θ (comap ρ G) := by
  rw [Filter.comap_comap, H, ← Filter.comap_comap]

end comm

/-
**Filter._root_.Function.Semiconj.filter_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Semiconj.filter_map {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (map f) (map ga) (map gb) :=
  map_comm h.comp_eq
/-
**Filter._root_.Function.Commute.filter_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Commute.filter_map {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (map f) (map g) :=
  h.semiconj.filter_map
/-
**Filter._root_.Function.Semiconj.filter_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Semiconj.filter_comap {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (comap f) (comap gb) (comap ga) :=
  comap_comm h.comp_eq.symm
/-
**Filter._root_.Function.Commute.filter_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Commute.filter_comap {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (comap f) (comap g) :=
  h.semiconj.filter_comap

section

open Filter

/-
**Filter._root_.Function.LeftInverse.filter_map** 是 Mathlib 中的一个定理，位于命名空间 `Filte
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.LeftInverse.filter_map {f : α → β} {g : β → α} (hfg : LeftInverse g f) :
    LeftInverse (map g) (map f) := fun F ↦ by
  rw [map_map, hfg.comp_eq_id, map_id]
/-
**Filter._root_.Function.LeftInverse.filter_comap** 是 Mathlib 中的一个定理，位于命名空间 `Fil
ter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.LeftInverse.filter_comap {f : α → β} {g : β → α} (hfg : LeftInverse g f) :
    RightInverse (comap g) (comap f) := fun F ↦ by
  rw [comap_comap, hfg.comp_eq_id, comap_id]

nonrec theorem _root_.Function.RightInverse.filter_map {f : α → β} {g : β → α}
    (hfg : RightInverse g f) : RightInverse (map g) (map f) :=
  hfg.filter_map

nonrec theorem _root_.Function.RightInverse.filter_comap {f : α → β} {g : β → α}
    (hfg : RightInverse g f) : LeftInverse (comap g) (comap f) :=
  hfg.filter_comap
/-
**Filter._root_.Set.LeftInvOn.filter_map_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.LeftInvOn.filter_map_Iic {f : α → β} {g : β → α} (hfg : LeftInvOn g f s) :
    LeftInvOn (map g) (map f) (Iic <| 𝓟 s) := fun F (hF : F ≤ 𝓟 s) ↦ by
  have : (g ∘ f) =ᶠ[𝓟 s] id := by simpa only [eventuallyEq_principal] using! hfg
  rw [map_map, map_congr (this.filter_mono hF), map_id]

nonrec theorem _root_.Set.RightInvOn.filter_map_Iic {f : α → β} {g : β → α}
    (hfg : RightInvOn g f t) : RightInvOn (map g) (map f) (Iic <| 𝓟 t) :=
  hfg.filter_map_Iic

end

section KernMap

/-- The analog of `Set.kernImage` for filters.
A set `s` belongs to `Filter.kernMap m f` if either of the following equivalent conditions hold.

1. There exists a set `t ∈ f` such that `s = Set.kernImage m t`. This is used as a definition.
2. There exists a set `t` such that `tᶜ ∈ f` and `sᶜ = m '' t`, see `Filter.mem_kernMap_iff_compl`
   and `Filter.compl_mem_kernMap`.

This definition is useful because it gives a right adjoint to `Filter.comap`, and because it has a
nice interpretation when working with `co-` filters (`Filter.cocompact`, `Filter.cofinite`, ...).
For example, `kernMap m (cocompact α)` is the filter generated by the complements of the sets
`m '' K` where `K` is a compact subset of `α`. -/
/-
**Filter.kernMap** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：kernMap (m : α -> β) (f : Filter α) : Filter β where sets
参数：m : α -> β；f : Filter α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The analog of `Set.kernImage` for filters.
A set `s` belongs to `Filter.kernMap m f` if either of the following equivalent 
conditions hold.

1. There exists a set `t ∈ f` such that `s = Set.kernImage m t`. This is used as
 a definition.
2. There exists a set `t` such that `tᶜ ∈ f` and `sᶜ = m '' t`, see `Filter.mem_
kernMap_iff_compl`
   and `Filter.compl_mem_kernMap`.

This definition is useful because it gives a right adjoint to `Filter.comap`, an
d because it has a
nice interpretation when working with `co-` filters (`Filter.cocompact`, `Filter
.cofinite`, ...).
For example, `kernMap m (cocompact α)` is the filter generated by the complement
s of the sets
`m '' K` where `K` is a compact subset of `α`.
-/
def kernMap (m : α → β) (f : Filter α) : Filter β where
  sets := (kernImage m) '' f.sets
  univ_sets := ⟨univ, f.univ_sets, by simp [kernImage_eq_compl]⟩
  sets_of_superset := by
    rintro _ t ⟨s, hs, rfl⟩ hst
    refine ⟨s ∪ m ⁻¹' t, mem_of_superset hs subset_union_left, ?_⟩
    rw [kernImage_union_preimage, union_eq_right.mpr hst]
  inter_sets := by
    rintro _ _ ⟨s₁, h₁, rfl⟩ ⟨s₂, h₂, rfl⟩
    exact ⟨s₁ ∩ s₂, f.inter_sets h₁ h₂, Set.preimage_kernImage.u_inf⟩

variable {m : α → β} {f : Filter α}
/-
**Filter.mem_kernMap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_kernMap {s : Set β} : s in kernMap m f ↔ exists t in f, kernImage m t 
= s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_kernMap {s : Set β} : s ∈ kernMap m f ↔ ∃ t ∈ f, kernImage m t = s :=
  Iff.rfl
/-
**Filter.mem_kernMap_iff_compl** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_kernMap_iff_compl {s : Set β} : s in kernMap m f ↔ exists t, tᶜ in f ∧
 m '' t = sᶜ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_kernMap`：mem_kernMap {s : Set β} : s in kernMap m f ↔ exists 
t in f, kernImage m t = s
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用引理 `Set.kernImage_compl`：kernImage_compl {s : Set α} : kernImage f (sᶜ) = (f
 '' s)ᶜ
· 使用定理 `compl_eq_comm`：compl_eq_comm : xᶜ = y ↔ yᶜ = x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_kernMap_iff_compl {s : Set β} : s ∈ kernMap m f ↔ ∃ t, tᶜ ∈ f ∧ m '' t = sᶜ := by
  rw [mem_kernMap, compl_surjective.exists]
  refine exists_congr (fun x ↦ and_congr_right fun _ ↦ ?_)
  rw [kernImage_compl, compl_eq_comm, eq_comm]
/-
**Filter.compl_mem_kernMap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：compl_mem_kernMap {s : Set β} : sᶜ in kernMap m f ↔ exists t, tᶜ in f ∧ m 
'' t = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem compl_mem_kernMap {s : Set β} : sᶜ ∈ kernMap m f ↔ ∃ t, tᶜ ∈ f ∧ m '' t = s := by
  simp_rw [mem_kernMap_iff_compl, compl_compl]
/-
**Filter.comap_le_iff_le_kernMap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_le_iff_le_kernMap : comap m g <= f ↔ g <= kernMap m f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_le_iff_le_kernMap : comap m g ≤ f ↔ g ≤ kernMap m f := by
  simp [Filter.le_def, mem_comap'', mem_kernMap, -mem_comap]
/-
**Filter.gc_comap_kernMap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：gc_comap_kernMap (m : α -> β) : GaloisConnection (comap m) (kernMap m)
参数：m : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_le_iff_le_kernMap`：comap_le_iff_le_kernMap : comap m g <= f
 ↔ g <= kernMap m f
-/
theorem gc_comap_kernMap (m : α → β) : GaloisConnection (comap m) (kernMap m) :=
  fun _ _ ↦ comap_le_iff_le_kernMap
/-
**Filter.kernMap_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：kernMap_principal {s : Set α} : kernMap m (𝓟 s) = 𝓟 (kernImage m s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.comap_le_iff_le_kernMap`：comap_le_iff_le_kernMap : comap m g <= f
 ↔ g <= kernMap m f
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.mem_comap''`：mem_comap'' : s in comap f l ↔ kernImage f s in l
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem kernMap_principal {s : Set α} : kernMap m (𝓟 s) = 𝓟 (kernImage m s) := by
  refine eq_of_forall_le_iff (fun g ↦ ?_)
  rw [← comap_le_iff_le_kernMap, le_principal_iff, le_principal_iff, mem_comap'']

end KernMap

@[simp]
/-
**Filter.comap_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 (m ⁻¹' t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 (m ⁻¹' t) :=
  Filter.ext fun _ => ⟨fun ⟨_u, hu, b⟩ => (preimage_mono hu).trans b,
    fun h => ⟨t, Subset.rfl, h⟩⟩
/-
**Filter.principal_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：principal_subtype {α : Type*} (s : Set α) (t : Set s) : 𝓟 t = comap (↑) (𝓟
 (((↑) : s -> α) '' t))
参数：s : Set α；t : Set s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem principal_subtype {α : Type*} (s : Set α) (t : Set s) :
    𝓟 t = comap (↑) (𝓟 (((↑) : s → α) '' t)) := by
  rw [comap_principal, preimage_image_eq _ Subtype.coe_injective]

@[simp]
/-
**Filter.comap_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_pure {b : β} : comap m (pure b) = 𝓟 (m ⁻¹' {b})
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
-/
theorem comap_pure {b : β} : comap m (pure b) = 𝓟 (m ⁻¹' {b}) := by
  rw [← principal_singleton, comap_principal]
/-
**Filter.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_le_iff_le_comap : map m f <= g ↔ f <= comap m g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem map_le_iff_le_comap : map m f ≤ g ↔ f ≤ comap m g :=
  ⟨fun h _ ⟨_, ht, hts⟩ => mem_of_superset (h ht) hts, fun h _ ht => h ⟨_, ht, Subset.rfl⟩⟩
/-
**Filter.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：gc_map_comap (m : α -> β) : GaloisConnection (map m) (comap m)
参数：m : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
-/
theorem gc_map_comap (m : α → β) : GaloisConnection (map m) (comap m) :=
  fun _ _ => map_le_iff_le_comap

@[gcongr, mono]
/-
**Filter.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_mono : Monotone (map m)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `Filter.gc_map_comap`：gc_map_comap (m : α -> β) : GaloisConnection (map m
) (comap m)
-/
theorem map_mono : Monotone (map m) :=
  (gc_map_comap m).monotone_l

@[gcongr, mono]
/-
**Filter.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_mono : Monotone (comap m)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `Filter.gc_map_comap`：gc_map_comap (m : α -> β) : GaloisConnection (map m
) (comap m)
-/
theorem comap_mono : Monotone (comap m) :=
  (gc_map_comap m).monotone_u
/-
**Filter.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map m ⊥ = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `Filter.gc_map_comap`：gc_map_comap (m : α -> β) : GaloisConnection (map m
) (comap m)
-/
@[simp] theorem map_bot : map m ⊥ = ⊥ := (gc_map_comap m).l_bot
/-
**Filter.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : Filter α} {m : α → β},   Filter.m
ap m (f₁ ⊔ f₂) = Filter.map m f₁ ⊔ Filter.map m f₂
参数：f₁ ⊔ f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `Filter.gc_map_comap`：gc_map_comap (m : α -> β) : GaloisConnection (map m
) (comap m)
-/
@[simp] theorem map_sup : map m (f₁ ⊔ f₂) = map m f₁ ⊔ map m f₂ := (gc_map_comap m).l_sup

@[simp]
/-
**Filter.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_iSup {f : ι -> Filter α} : map m (⨆ i, f i) = ⨆ i, map m (f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `Filter.gc_map_comap`：gc_map_comap (m : α -> β) : GaloisConnection (map m
) (comap m)
-/
theorem map_iSup {f : ι → Filter α} : map m (⨆ i, f i) = ⨆ i, map m (f i) :=
  (gc_map_comap m).l_iSup

@[simp]
/-
**Filter.map_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_top (f : α -> β) : map f ⊤ = 𝓟 (range f)
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
theorem map_top (f : α → β) : map f ⊤ = 𝓟 (range f) := by
  rw [← principal_univ, map_principal, image_univ]
/-
**Filter.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.comap m ⊤ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `Filter.gc_map_comap`：gc_map_comap (m : α -> β) : GaloisConnection (map m
) (comap m)
-/
@[simp] theorem comap_top : comap m ⊤ = ⊤ := (gc_map_comap m).u_top
/-
**Filter.comap_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m : α → β},   Filter.c
omap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
参数：g₁ ⊓ g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `Filter.gc_map_comap`：gc_map_comap (m : α -> β) : GaloisConnection (map m
) (comap m)
-/
@[simp] theorem comap_inf : comap m (g₁ ⊓ g₂) = comap m g₁ ⊓ comap m g₂ := (gc_map_comap m).u_inf

@[simp]
/-
**Filter.comap_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) = ⨅ i, comap m (f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `Filter.gc_map_comap`：gc_map_comap (m : α -> β) : GaloisConnection (map m
) (comap m)
-/
theorem comap_iInf {f : ι → Filter β} : comap m (⨅ i, f i) = ⨅ i, comap m (f i) :=
  (gc_map_comap m).u_iInf
/-
**Filter.le_comap_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_comap_top (f : α -> β) (l : Filter α) : l <= comap f ⊤
参数：f : α -> β；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_top`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.co
map m ⊤ = ⊤
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem le_comap_top (f : α → β) (l : Filter α) : l ≤ comap f ⊤ := by
  rw [comap_top]
  exact le_top
/-
**Filter.map_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_comap_le : map m (comap m g) <= g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `Filter.gc_map_comap`：gc_map_comap (m : α -> β) : GaloisConnection (map m
) (comap m)
-/
theorem map_comap_le : map m (comap m g) ≤ g :=
  (gc_map_comap m).l_u_le _
/-
**Filter.le_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_comap_map : f <= comap m (map m f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `Filter.gc_map_comap`：gc_map_comap (m : α -> β) : GaloisConnection (map m
) (comap m)
-/
theorem le_comap_map : f ≤ comap m (map m f) :=
  (gc_map_comap m).le_u_l _

@[simp]
/-
**Filter.comap_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_bot : comap m ⊥ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Filter.mem_bot`：mem_bot {s : Set α} : s in (⊥ : Filter α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem comap_bot : comap m ⊥ = ⊥ :=
  bot_unique fun s _ => ⟨∅, mem_bot, by simp only [empty_subset, preimage_empty]⟩
/-
**Filter.neBot_of_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：neBot_of_comap (h : (comap m g).NeBot) : g.NeBot
参数：h : (comap m g).NeBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Filter.comap_bot`：comap_bot : comap m ⊥ = ⊥
-/
theorem neBot_of_comap (h : (comap m g).NeBot) : g.NeBot := by
  rw [neBot_iff] at *
  contrapose h
  rw [h]
  exact comap_bot
/-
**Filter.comap_inf_principal_range** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_inf_principal_range : comap m (g ⊓ 𝓟 (range m)) = comap m g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_inf_principal_range : comap m (g ⊓ 𝓟 (range m)) = comap m g := by
  simp
/-
**Filter.disjoint_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_comap (h : Disjoint g₁ g₂) : Disjoint (comap m g₁) (comap m g₂)
参数：h : Disjoint g₁ g₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `Filter.comap_bot`：comap_bot : comap m ⊥ = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem disjoint_comap (h : Disjoint g₁ g₂) : Disjoint (comap m g₁) (comap m g₂) := by
  simp only [disjoint_iff, ← comap_inf, h.eq_bot, comap_bot]
/-
**Filter.comap_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_iSup {ι} {f : ι -> Filter β} {m : α -> β} : comap m (iSup f) = ⨆ i, 
comap m (f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `Filter.gc_comap_kernMap`：gc_comap_kernMap (m : α -> β) : GaloisConnectio
n (comap m) (kernMap m)
-/
theorem comap_iSup {ι} {f : ι → Filter β} {m : α → β} : comap m (iSup f) = ⨆ i, comap m (f i) :=
  (gc_comap_kernMap m).l_iSup
/-
**Filter.comap_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_sSup {s : Set (Filter β)} {m : α -> β} : comap m (sSup s) = ⨆ f in s
, comap m f
参数：Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `Filter.comap_iSup`：comap_iSup {ι} {f : ι -> Filter β} {m : α -> β} : com
ap m (iSup f) = ⨆ i, comap m (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_sSup {s : Set (Filter β)} {m : α → β} : comap m (sSup s) = ⨆ f ∈ s, comap m f := by
  simp only [sSup_eq_iSup, comap_iSup]
/-
**Filter.comap_sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_sup : comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_eq_iSup`：sup_eq_iSup (x y : α) : x ⊔ y = ⨆ b : Bool, cond b x y
· 使用定理 `Filter.comap_iSup`：comap_iSup {ι} {f : ι -> Filter β} {m : α -> β} : com
ap m (iSup f) = ⨆ i, comap m (f i)
· 使用定理 `iSup_bool_eq`：iSup_bool_eq {f : Bool -> α} : ⨆ b : Bool, f b = f true ⊔ 
f false
· 使用定理 `Bool.cond_true`：∀ {α : Sort u} {a b : α}, (bif true then a else b) = a
· 使用定理 `Bool.cond_false`：∀ {α : Sort u} {a b : α}, (bif false then a else b) = b
-/
theorem comap_sup : comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g₂ := by
  rw [sup_eq_iSup, comap_iSup, iSup_bool_eq, Bool.cond_true, Bool.cond_false]
/-
**Filter.map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_comap (f : Filter β) (m : α -> β) : (f.comap m).map m = f ⊓ 𝓟 (range m
)
参数：f : Filter β；m : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Filter.map_comap_le`：map_comap_le : map m (comap m g) <= g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.range_mem_map`：range_mem_map : range m in map m f
· 使用引理 `Filter.mem_inf_principal`：mem_inf_principal {f : Filter α} {s t : Set α}
 : s in f ⊓ 𝓟 t ↔ { x | x in t -> x in s } in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
theorem map_comap (f : Filter β) (m : α → β) : (f.comap m).map m = f ⊓ 𝓟 (range m) := by
  refine le_antisymm (le_inf map_comap_le <| le_principal_iff.2 range_mem_map) ?_
  rintro t' ⟨t, ht, sub⟩
  refine mem_inf_principal.2 (mem_of_superset ht ?_)
  rintro _ hxt ⟨x, rfl⟩
  exact sub hxt
/-
**Filter.map_comap_setCoe_val** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_comap_setCoe_val (f : Filter β) (s : Set β) : (f.comap ((↑) : s -> β))
.map (↑) = f ⊓ 𝓟 s
参数：f : Filter β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_comap`：map_comap (f : Filter β) (m : α -> β) : (f.comap m).ma
p m = f ⊓ 𝓟 (range m)
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
theorem map_comap_setCoe_val (f : Filter β) (s : Set β) :
    (f.comap ((↑) : s → β)).map (↑) = f ⊓ 𝓟 s := by
  rw [map_comap, Subtype.range_val]
/-
**Filter.map_comap_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_comap_of_mem {f : Filter β} {m : α -> β} (hf : range m in f) : (f.coma
p m).map m = f
参数：hf : range m in f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_comap`：map_comap (f : Filter β) (m : α -> β) : (f.comap m).ma
p m = f ⊓ 𝓟 (range m)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
-/
theorem map_comap_of_mem {f : Filter β} {m : α → β} (hf : range m ∈ f) : (f.comap m).map m = f := by
  rw [map_comap, inf_eq_left.2 (le_principal_iff.2 hf)]
/-
**Filter.canLift** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：canLift (c) (p) [CanLift α β c p] : CanLift (Filter α) (Filter β) (map c) 
fun f => forallᶠ x : α in f, p x where prf f hf
参数：c；p。
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_comap_of_mem`：map_comap_of_mem {f : Filter β} {m : α -> β} (h
f : range m in f) : (f.comap m).map m = f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
-/
instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Filter α) (Filter β) (map c) fun f => ∀ᶠ x : α in f, p x where
  prf f hf := ⟨comap c f, map_comap_of_mem <| hf.mono CanLift.prf⟩
/-
**Filter.comap_le_comap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_le_comap_iff {f g : Filter β} {m : α -> β} (hf : range m in f) : com
ap m f <= comap m g ↔ f <= g
参数：hf : range m in f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `Filter.map_comap_le`：map_comap_le : map m (comap m g) <= g
· 使用定理 `Filter.map_comap_of_mem`：map_comap_of_mem {f : Filter β} {m : α -> β} (h
f : range m in f) : (f.comap m).map m = f
· 使用定理 `Filter.comap_mono`：comap_mono : Monotone (comap m)
-/
theorem comap_le_comap_iff {f g : Filter β} {m : α → β} (hf : range m ∈ f) :
    comap m f ≤ comap m g ↔ f ≤ g :=
  ⟨fun h => map_comap_of_mem hf ▸ (map_mono h).trans map_comap_le, fun h => comap_mono h⟩
/-
**Filter.map_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_comap_of_surjective {f : α -> β} (hf : Surjective f) (l : Filter β) : 
map f (comap f l) = l
参数：hf : Surjective f；l : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_comap_of_mem`：map_comap_of_mem {f : Filter β} {m : α -> β} (h
f : range m in f) : (f.comap m).map m = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
-/
theorem map_comap_of_surjective {f : α → β} (hf : Surjective f) (l : Filter β) :
    map f (comap f l) = l :=
  map_comap_of_mem <| by simp only [hf.range_eq, univ_mem]
/-
**Filter.comap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_injective {f : α -> β} (hf : Surjective f) : Injective (comap f)
参数：hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Filter.map_comap_of_surjective`：map_comap_of_surjective {f : α -> β} (hf
 : Surjective f) (l : Filter β) : map f (comap f l) = l
-/
theorem comap_injective {f : α → β} (hf : Surjective f) : Injective (comap f) :=
  LeftInverse.injective <| map_comap_of_surjective hf
/-
**Filter._root_.Function.Surjective.filter_map_top** 是 Mathlib 中的一个定理，位于命名空间 `Fi
lter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Surjective.filter_map_top {f : α → β} (hf : Surjective f) : map f ⊤ = ⊤ :=
  (congr_arg _ comap_top).symm.trans <| map_comap_of_surjective hf ⊤
/-
**Filter.subtype_coe_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：subtype_coe_map_comap (s : Set α) (f : Filter α) : map ((↑) : s -> α) (com
ap ((↑) : s -> α) f) = f ⊓ 𝓟 s
参数：s : Set α；f : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_comap`：map_comap (f : Filter β) (m : α -> β) : (f.comap m).ma
p m = f ⊓ 𝓟 (range m)
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem subtype_coe_map_comap (s : Set α) (f : Filter α) :
    map ((↑) : s → α) (comap ((↑) : s → α) f) = f ⊓ 𝓟 s := by rw [map_comap, Subtype.range_coe]
/-
**Filter.image_mem_of_mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：image_mem_of_mem_comap {f : Filter α} {c : β -> α} (h : range c in f) {W :
 Set β} (W_in : W in comap c f) : c '' W in f
参数：h : range c in f；W_in : W in comap c f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_comap_of_mem`：map_comap_of_mem {f : Filter β} {m : α -> β} (h
f : range m in f) : (f.comap m).map m = f
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
-/
theorem image_mem_of_mem_comap {f : Filter α} {c : β → α} (h : range c ∈ f) {W : Set β}
    (W_in : W ∈ comap c f) : c '' W ∈ f := by
  rw [← map_comap_of_mem h]
  exact image_mem_map W_in
/-
**Filter.image_coe_mem_of_mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：image_coe_mem_of_mem_comap {f : Filter α} {U : Set α} (h : U in f) {W : Se
t U} (W_in : W in comap ((↑) : U -> α) f) : (↑) '' W in f
参数：h : U in f；W_in : W in comap ((↑) : U -> α) f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.image_mem_of_mem_comap`：image_mem_of_mem_comap {f : Filter α} {c 
: β -> α} (h : range c in f) {W : Set β} (W_in : W in comap c f) : c '' W in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem image_coe_mem_of_mem_comap {f : Filter α} {U : Set α} (h : U ∈ f) {W : Set U}
    (W_in : W ∈ comap ((↑) : U → α) f) : (↑) '' W ∈ f :=
  image_mem_of_mem_comap (by simp [h]) W_in
/-
**Filter.comap_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_map {f : Filter α} {m : α -> β} (h : Injective m) : comap m (map m f
) = f
参数：h : Injective m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Filter.le_comap_map`：le_comap_map : f <= comap m (map m f)
-/
theorem comap_map {f : Filter α} {m : α → β} (h : Injective m) : comap m (map m f) = f :=
  le_antisymm
    (fun s hs =>
      mem_of_superset (preimage_mem_comap <| image_mem_map hs) <| by
        simp only [preimage_image_eq s h, Subset.rfl])
    le_comap_map
/-
**Filter.mem_comap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_comap_iff {f : Filter β} {m : α -> β} (inj : Injective m) (large : Set
.range m in f) {S : Set α} : S in comap m f ↔ m '' S in f
参数：inj : Injective m；large : Set.range m in f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.image_mem_map_iff`：image_mem_map_iff (hf : Injective m) : m '' s 
in map m f ↔ s in f
· 使用定理 `Filter.map_comap_of_mem`：map_comap_of_mem {f : Filter β} {m : α -> β} (h
f : range m in f) : (f.comap m).map m = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap_iff {f : Filter β} {m : α → β} (inj : Injective m) (large : Set.range m ∈ f)
    {S : Set α} : S ∈ comap m f ↔ m '' S ∈ f := by
  rw [← image_mem_map_iff inj, map_comap_of_mem large]
/-
**Filter.map_le_map_iff_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_le_map_iff_of_injOn {l₁ l₂ : Filter α} {f : α -> β} {s : Set α} (h₁ : 
s in l₁) (h₂ : s in l₂) (hinj : InjOn f s) : map f l₁ <= map f l₂ ↔ l₁ <= l₂
参数：h₁ : s in l₁；h₂ : s in l₂；hinj : InjOn f s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem map_le_map_iff_of_injOn {l₁ l₂ : Filter α} {f : α → β} {s : Set α} (h₁ : s ∈ l₁)
    (h₂ : s ∈ l₂) (hinj : InjOn f s) : map f l₁ ≤ map f l₂ ↔ l₁ ≤ l₂ :=
  ⟨fun h _t ht =>
    mp_mem h₁ <|
      mem_of_superset (h <| image_mem_map (inter_mem h₂ ht)) fun _y ⟨_x, ⟨hxs, hxt⟩, hxy⟩ hys =>
        hinj hxs hys hxy ▸ hxt,
    fun h => map_mono h⟩
/-
**Filter.map_le_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_le_map_iff {f g : Filter α} {m : α -> β} (hm : Injective m) : map m f 
<= map m g ↔ f <= g
参数：hm : Injective m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
· 使用定理 `Filter.comap_map`：comap_map {f : Filter α} {m : α -> β} (h : Injective m
) : comap m (map m f) = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_le_map_iff {f g : Filter α} {m : α → β} (hm : Injective m) :
    map m f ≤ map m g ↔ f ≤ g := by rw [map_le_iff_le_comap, comap_map hm]
/-
**Filter.map_eq_map_iff_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_eq_map_iff_of_injOn {f g : Filter α} {m : α -> β} {s : Set α} (hsf : s
 in f) (hsg : s in g) (hm : InjOn m s) : map m f = map m g ↔ f = g
参数：hsf : s in f；hsg : s in g；hm : InjOn m s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_le_map_iff_of_injOn`：map_le_map_iff_of_injOn {l₁ l₂ : Filter 
α} {f : α -> β} {s : Set α} (h₁ : s in l₁) (h₂ : s in l₂) (hinj : InjOn f s) : m
ap f l₁ <= map f l₂ …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_eq_map_iff_of_injOn {f g : Filter α} {m : α → β} {s : Set α} (hsf : s ∈ f) (hsg : s ∈ g)
    (hm : InjOn m s) : map m f = map m g ↔ f = g := by
  simp only [le_antisymm_iff, map_le_map_iff_of_injOn hsf hsg hm,
    map_le_map_iff_of_injOn hsg hsf hm]
/-
**Filter.map_inj** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_inj {f g : Filter α} {m : α -> β} (hm : Injective m) : map m f = map m
 g ↔ f = g
参数：hm : Injective m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_eq_map_iff_of_injOn`：map_eq_map_iff_of_injOn {f g : Filter α}
 {m : α -> β} {s : Set α} (hsf : s in f) (hsg : s in g) (hm : InjOn m s) : map m
 f = map m g ↔ f = g
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem map_inj {f g : Filter α} {m : α → β} (hm : Injective m) : map m f = map m g ↔ f = g :=
  map_eq_map_iff_of_injOn univ_mem univ_mem hm.injOn
/-
**Filter.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_injective {m : α -> β} (hm : Injective m) : Injective (map m)
参数：hm : Injective m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.map_inj`：map_inj {f g : Filter α} {m : α -> β} (hm : Injective m)
 : map m f = map m g ↔ f = g
-/
theorem map_injective {m : α → β} (hm : Injective m) : Injective (map m) := fun _ _ =>
  (map_inj hm).1
/-
**Filter.comap_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_neBot_iff {f : Filter β} {m : α -> β} : NeBot (comap m f) ↔ forall t
 in f, exists a, m a in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
-/
theorem comap_neBot_iff {f : Filter β} {m : α → β} : NeBot (comap m f) ↔ ∀ t ∈ f, ∃ a, m a ∈ t := by
  simp only [← forall_mem_nonempty_iff_neBot, mem_comap, forall_exists_index, and_imp]
  exact ⟨fun h t t_in => h (m ⁻¹' t) t t_in Subset.rfl, fun h s t ht hst => (h t ht).imp hst⟩
/-
**Filter.comap_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_neBot {f : Filter β} {m : α -> β} (hm : forall t in f, exists a, m a
 in t) : NeBot (comap m f)
参数：hm : forall t in f, exists a, m a in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.comap_neBot_iff`：comap_neBot_iff {f : Filter β} {m : α -> β} : Ne
Bot (comap m f) ↔ forall t in f, exists a, m a in t
-/
theorem comap_neBot {f : Filter β} {m : α → β} (hm : ∀ t ∈ f, ∃ a, m a ∈ t) : NeBot (comap m f) :=
  comap_neBot_iff.mpr hm
/-
**Filter.comap_neBot_iff_frequently** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_neBot_iff_frequently {f : Filter β} {m : α -> β} : NeBot (comap m f)
 ↔ existsᶠ y in f, y in range m
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_neBot_iff_frequently {f : Filter β} {m : α → β} :
    NeBot (comap m f) ↔ ∃ᶠ y in f, y ∈ range m := by
  simp only [comap_neBot_iff, frequently_iff, mem_range, @and_comm (_ ∈ _), exists_exists_eq_and]
/-
**Filter.comap_neBot_iff_compl_range** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_neBot_iff_compl_range {f : Filter β} {m : α -> β} : NeBot (comap m f
) ↔ (range m)ᶜ ∉ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_neBot_iff_frequently`：comap_neBot_iff_frequently {f : Filte
r β} {m : α -> β} : NeBot (comap m f) ↔ existsᶠ y in f, y in range m
-/
theorem comap_neBot_iff_compl_range {f : Filter β} {m : α → β} :
    NeBot (comap m f) ↔ (range m)ᶜ ∉ f :=
  comap_neBot_iff_frequently
/-
**Filter.comap_eq_bot_iff_compl_range** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_eq_bot_iff_compl_range {f : Filter β} {m : α -> β} : comap m f = ⊥ ↔
 (range m)ᶜ in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `Filter.comap_neBot_iff_compl_range`：comap_neBot_iff_compl_range {f : Fil
ter β} {m : α -> β} : NeBot (comap m f) ↔ (range m)ᶜ ∉ f
-/
theorem comap_eq_bot_iff_compl_range {f : Filter β} {m : α → β} : comap m f = ⊥ ↔ (range m)ᶜ ∈ f :=
  not_iff_not.mp <| neBot_iff.symm.trans comap_neBot_iff_compl_range
/-
**Filter.comap_surjective_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_surjective_eq_bot {f : Filter β} {m : α -> β} (hm : Surjective m) : 
comap m f = ⊥ ↔ f = ⊥
参数：hm : Surjective m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_eq_bot_iff_compl_range`：comap_eq_bot_iff_compl_range {f : F
ilter β} {m : α -> β} : comap m f = ⊥ ↔ (range m)ᶜ in f
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comap_surjective_eq_bot {f : Filter β} {m : α → β} (hm : Surjective m) :
    comap m f = ⊥ ↔ f = ⊥ := by
  rw [comap_eq_bot_iff_compl_range, hm.range_eq, compl_univ, empty_mem_iff_bot]
/-
**Filter.disjoint_comap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_comap_iff (h : Surjective m) : Disjoint (comap m g₁) (comap m g₂)
 ↔ Disjoint g₁ g₂
参数：h : Surjective m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_surjective_eq_bot`：comap_surjective_eq_bot {f : Filter β} {
m : α -> β} (hm : Surjective m) : comap m f = ⊥ ↔ f = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_comap_iff (h : Surjective m) :
    Disjoint (comap m g₁) (comap m g₂) ↔ Disjoint g₁ g₂ := by
  rw [disjoint_iff, disjoint_iff, ← comap_inf, comap_surjective_eq_bot h]
/-
**Filter.NeBot.comap_of_range_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter.NeBot`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter β} {m : α → β}, f.NeBot → Set.
range m ∈ f → (Filter.comap m f).NeBot
参数：Filter.comap m f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.comap_neBot_iff_frequently`：comap_neBot_iff_frequently {f : Filte
r β} {m : α -> β} : NeBot (comap m f) ↔ existsᶠ y in f, y in range m
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
-/
theorem NeBot.comap_of_range_mem {f : Filter β} {m : α → β} (_ : NeBot f) (hm : range m ∈ f) :
    NeBot (comap m f) :=
  comap_neBot_iff_frequently.2 <| Eventually.frequently hm

section Sum
open Sum

@[simp]
/-
**Filter.comap_inl_map_inr** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_inl_map_inr : comap inl (map (@inr α β) g) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_comap_iff_compl`：mem_comap_iff_compl : s in comap f l ↔ (f ''
 sᶜ)ᶜ in l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_inr_image_inl`：preimage_inr_image_inl (s : Set α) : Sum.inr
 ⁻¹' @Sum.inl α β '' s = ∅
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_inl_map_inr : comap inl (map (@inr α β) g) = ⊥ := by
  ext
  rw [mem_comap_iff_compl]
  simp

@[simp]
/-
**Filter.comap_inr_map_inl** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_inr_map_inl : comap inr (map (@inl α β) f) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_comap_iff_compl`：mem_comap_iff_compl : s in comap f l ↔ (f ''
 sᶜ)ᶜ in l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_inl_image_inr`：preimage_inl_image_inr (s : Set β) : Sum.inl
 ⁻¹' @Sum.inr α β '' s = ∅
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_inr_map_inl : comap inr (map (@inl α β) f) = ⊥ := by
  ext
  rw [mem_comap_iff_compl]
  simp

@[simp]
/-
**Filter.map_inl_inf_map_inr** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_inl_inf_map_inr : map inl f ⊓ map inr g = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_top`：map_top (f : α -> β) : map f ⊤ = 𝓟 (range f)
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `Set.range_inl_inter_range_inr`：range_inl_inter_range_inr : range (Sum.in
l : α -> α oplus β) inter range Sum.inr = ∅
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
-/
theorem map_inl_inf_map_inr : map inl f ⊓ map inr g = ⊥ := by
  apply le_bot_iff.mp
  trans map inl ⊤ ⊓ map inr ⊤
  · apply inf_le_inf <;> simp
  · simp

@[simp]
/-
**Filter.map_inr_inf_map_inl** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_inr_inf_map_inl : map inr f ⊓ map inl g = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Filter.map_inl_inf_map_inr`：map_inl_inf_map_inr : map inl f ⊓ map inr g 
= ⊥
-/
theorem map_inr_inf_map_inl : map inr f ⊓ map inl g = ⊥ := by
  rw [inf_comm, map_inl_inf_map_inr]
/-
**Filter.comap_sumElim_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_sumElim_eq (l : Filter γ) (m₁ : α -> γ) (m₂ : β -> γ) : comap (Sum.e
lim m₁ m₂) l = map inl (comap m₁ l) ⊔ map inr (comap m₂ l)
参数：l : Filter γ；m₁ : α -> γ；m₂ : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_sumElim`：image_sumElim (s : Set (α oplus β)) (f : α -> γ) (g :
 β -> γ) : Sum.elim f g '' s = f '' Sum.inl ⁻¹' s union g '' Sum.inr ⁻¹' s
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_sumElim_eq (l : Filter γ) (m₁ : α → γ) (m₂ : β → γ) :
    comap (Sum.elim m₁ m₂) l = map inl (comap m₁ l) ⊔ map inr (comap m₂ l) := by
  ext s
  simp_rw [mem_sup, mem_map, mem_comap_iff_compl]
  simp [image_sumElim]
/-
**Filter.map_comap_inl_sup_map_comap_inr** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_comap_inl_sup_map_comap_inr (l : Filter (α oplus β)) : map inl (comap 
inl l) ⊔ map inr (comap inr l) = l
参数：l : Filter (α oplus β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.comap_sumElim_eq`：comap_sumElim_eq (l : Filter γ) (m₁ : α -> γ) (
m₂ : β -> γ) : comap (Sum.elim m₁ m₂) l = map inl (comap m₁ l) ⊔ map inr (comap 
m₂ l)
· 使用定理 `Sum.elim_inl_inr`：∀ {α : Type u_1} {β : Type u_2}, Sum.elim Sum.inl Sum.
inr = id
· 使用定理 `Filter.comap_id`：comap_id : comap id f = f
-/
theorem map_comap_inl_sup_map_comap_inr (l : Filter (α ⊕ β)) :
    map inl (comap inl l) ⊔ map inr (comap inr l) = l := by
  rw [← comap_sumElim_eq, Sum.elim_inl_inr, comap_id]
/-
**Filter.map_sumElim_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_sumElim_eq (l : Filter (α oplus β)) (m₁ : α -> γ) (m₂ : β -> γ) : map 
(Sum.elim m₁ m₂) l = map m₁ (comap inl l) ⊔ map m₂ (comap inr l)
参数：l : Filter (α oplus β)；m₁ : α -> γ；m₂ : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_comap_inl_sup_map_comap_inr`：map_comap_inl_sup_map_comap_inr 
(l : Filter (α oplus β)) : map inl (comap inl l) ⊔ map inr (comap inr l) = l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.map_sup`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : Filter α} {m : 
α → β},   Filter.map m (f₁ ⊔ f₂) = Filter.map m f₁ ⊔ Filter.map m f₂
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Filter.comap_sup`：comap_sup : comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g
₂
· 使用定理 `GaloisConnection.u_l_u_eq_u`：u_l_u_eq_u (b : β) : u (l (u b)) = u b
· 使用定理 `Filter.gc_map_comap`：gc_map_comap (m : α -> β) : GaloisConnection (map m
) (comap m)
· 使用定理 `Filter.comap_inl_map_inr`：comap_inl_map_inr : comap inl (map (@inr α β) 
g) = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Filter.comap_inr_map_inl`：comap_inr_map_inl : comap inr (map (@inl α β) 
f) = ⊥
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_sumElim_eq (l : Filter (α ⊕ β)) (m₁ : α → γ) (m₂ : β → γ) :
    map (Sum.elim m₁ m₂) l = map m₁ (comap inl l) ⊔ map m₂ (comap inr l) := by
  rw [← map_comap_inl_sup_map_comap_inr l]
  simp [map_sup, map_map, comap_sup, (gc_map_comap _).u_l_u_eq_u]

end Sum

@[simp]
/-
**Filter.comap_fst_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_fst_neBot_iff {f : Filter α} : (f.comap (Prod.fst : α × β -> α)).NeB
ot ↔ f.NeBot ∧ Nonempty β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.filter_eq_bot_of_isEmpty`：filter_eq_bot_of_isEmpty [IsEmpty α] (f
 : Filter α) : f = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.range_fst`：∀ {α : Type u_1} {β : Type u_2} [Nonempty β], Set.range 
Prod.fst = Set.univ
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem comap_fst_neBot_iff {f : Filter α} :
    (f.comap (Prod.fst : α × β → α)).NeBot ↔ f.NeBot ∧ Nonempty β := by
  cases isEmpty_or_nonempty β
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]; simp [*]
  · simp [comap_neBot_iff_frequently, *]

@[instance]
/-
**Filter.comap_fst_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_fst_neBot [Nonempty β] {f : Filter α} [NeBot f] : (f.comap (Prod.fst
 : α × β -> α)).NeBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.comap_fst_neBot_iff`：comap_fst_neBot_iff {f : Filter α} : (f.coma
p (Prod.fst : α × β -> α)).NeBot ↔ f.NeBot ∧ Nonempty β
-/
theorem comap_fst_neBot [Nonempty β] {f : Filter α} [NeBot f] :
    (f.comap (Prod.fst : α × β → α)).NeBot :=
  comap_fst_neBot_iff.2 ⟨‹_›, ‹_›⟩

@[simp]
/-
**Filter.comap_snd_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_snd_neBot_iff {f : Filter β} : (f.comap (Prod.snd : α × β -> β)).NeB
ot ↔ Nonempty α ∧ f.NeBot
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.filter_eq_bot_of_isEmpty`：filter_eq_bot_of_isEmpty [IsEmpty α] (f
 : Filter α) : f = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.range_snd`：∀ {α : Type u_1} {β : Type u_2} [Nonempty α], Set.range 
Prod.snd = Set.univ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem comap_snd_neBot_iff {f : Filter β} :
    (f.comap (Prod.snd : α × β → β)).NeBot ↔ Nonempty α ∧ f.NeBot := by
  rcases isEmpty_or_nonempty α with hα | hα
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]; simp
  · simp [comap_neBot_iff_frequently, hα]

@[instance]
/-
**Filter.comap_snd_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_snd_neBot [Nonempty α] {f : Filter β} [NeBot f] : (f.comap (Prod.snd
 : α × β -> β)).NeBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.comap_snd_neBot_iff`：comap_snd_neBot_iff {f : Filter β} : (f.coma
p (Prod.snd : α × β -> β)).NeBot ↔ Nonempty α ∧ f.NeBot
-/
theorem comap_snd_neBot [Nonempty α] {f : Filter β} [NeBot f] :
    (f.comap (Prod.snd : α × β → β)).NeBot :=
  comap_snd_neBot_iff.2 ⟨‹_›, ‹_›⟩
/-
**Filter.comap_eval_neBot_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_eval_neBot_iff' {ι : Type*} {α : ι -> Type*} {i : ι} {f : Filter (α 
i)} : (comap (eval i) f).NeBot ↔ (forall j, Nonempty (α j)) ∧ NeBot f
参数：α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.filter_eq_bot_of_isEmpty`：filter_eq_bot_of_isEmpty [IsEmpty α] (f
 : Filter α) : f = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.nonempty_pi`：Classical.nonempty_pi {ι} {α : ι -> Sort*} : None
mpty (forall i, α i) ↔ forall i, Nonempty (α i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.range_eval`：range_eval {α : ι -> Sort _} [forall i, Nonempty (α i)] 
(i : ι) : range (eval i : (forall i, α i) -> α i) = univ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem comap_eval_neBot_iff' {ι : Type*} {α : ι → Type*} {i : ι} {f : Filter (α i)} :
    (comap (eval i) f).NeBot ↔ (∀ j, Nonempty (α j)) ∧ NeBot f := by
  rcases isEmpty_or_nonempty (∀ j, α j) with H | H
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]
    simp [← Classical.nonempty_pi]
  · have : ∀ j, Nonempty (α j) := Classical.nonempty_pi.1 H
    simp [comap_neBot_iff_frequently, *]

@[simp]
/-
**Filter.comap_eval_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_eval_neBot_iff {ι : Type*} {α : ι -> Type*} [forall j, Nonempty (α j
)] {i : ι} {f : Filter (α i)} : (comap (eval i) f).NeBot ↔ NeBot f
参数：α j；α i。
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_eval_neBot_iff {ι : Type*} {α : ι → Type*} [∀ j, Nonempty (α j)] {i : ι}
    {f : Filter (α i)} : (comap (eval i) f).NeBot ↔ NeBot f := by simp [comap_eval_neBot_iff', *]

@[instance]
/-
**Filter.comap_eval_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_eval_neBot {ι : Type*} {α : ι -> Type*} [forall j, Nonempty (α j)] (
i : ι) (f : Filter (α i)) [NeBot f] : (comap (eval i) f).NeBot
参数：α j；i : ι；f : Filter (α i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.comap_eval_neBot_iff`：comap_eval_neBot_iff {ι : Type*} {α : ι -> 
Type*} [forall j, Nonempty (α j)] {i : ι} {f : Filter (α i)} : (comap (eval i) f
).NeBot ↔ NeBot f
-/
theorem comap_eval_neBot {ι : Type*} {α : ι → Type*} [∀ j, Nonempty (α j)] (i : ι)
    (f : Filter (α i)) [NeBot f] : (comap (eval i) f).NeBot :=
  comap_eval_neBot_iff.2 ‹_›
/-
**Filter.comap_coe_neBot_of_le_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_coe_neBot_of_le_principal {s : Set γ} {l : Filter γ} [h : NeBot l] (
h' : l <= 𝓟 s) : NeBot (comap ((↑) : s -> γ) l)
参数：h' : l <= 𝓟 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.comap_of_range_mem`：∀ {α : Type u_1} {β : Type u_2} {f : Fi
lter β} {m : α → β}, f.NeBot → Set.range m ∈ f → (Filter.comap m f).NeBot
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem comap_coe_neBot_of_le_principal {s : Set γ} {l : Filter γ} [h : NeBot l] (h' : l ≤ 𝓟 s) :
    NeBot (comap ((↑) : s → γ) l) :=
  h.comap_of_range_mem <| (@Subtype.range_coe γ s).symm ▸ h' (mem_principal_self s)
/-
**Filter.NeBot.comap_of_surj** 是 Mathlib 中的一个定理，位于命名空间 `Filter.NeBot`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter β} {m : α → β}, f.NeBot → Func
tion.Surjective m → (Filter.comap m f).NeBot
参数：Filter.comap m f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.comap_of_range_mem`：∀ {α : Type u_1} {β : Type u_2} {f : Fi
lter β} {m : α → β}, f.NeBot → Set.range m ∈ f → (Filter.comap m f).NeBot
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem NeBot.comap_of_surj {f : Filter β} {m : α → β} (hf : NeBot f) (hm : Surjective m) :
    NeBot (comap m f) :=
  hf.comap_of_range_mem <| univ_mem' hm
/-
**Filter.NeBot.comap_of_image_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter.NeBot`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter β} {m : α → β},   f.NeBot → ∀ 
{s : Set α}, m '' s ∈ f → (Filter.comap m f).NeBot
参数：Filter.comap m f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.comap_of_range_mem`：∀ {α : Type u_1} {β : Type u_2} {f : Fi
lter β} {m : α → β}, f.NeBot → Set.range m ∈ f → (Filter.comap m f).NeBot
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem NeBot.comap_of_image_mem {f : Filter β} {m : α → β} (hf : NeBot f) {s : Set α}
    (hs : m '' s ∈ f) : NeBot (comap m f) :=
  hf.comap_of_range_mem <| mem_of_superset hs (image_subset_range _ _)

@[simp]
/-
**Filter.map_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.map_bot`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map 
m ⊥ = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥ :=
  ⟨by
    rw [← empty_mem_iff_bot, ← empty_mem_iff_bot]
    exact id, fun h => by simp only [h, map_bot]⟩

@[simp]
/-
**Filter.bot_eq_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bot_eq_map_iff : ⊥ = map m f ↔ f = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Filter.map_eq_bot_iff`：map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bot_eq_map_iff : ⊥ = map m f ↔ f = ⊥ := by rw [eq_comm, map_eq_bot_iff]
/-
**Filter.map_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_neBot_iff (f : α -> β) {F : Filter α} : NeBot (map f F) ↔ NeBot F
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_neBot_iff (f : α → β) {F : Filter α} : NeBot (map f F) ↔ NeBot F := by
  simp only [neBot_iff, Ne, map_eq_bot_iff]
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
theorem NeBot.map (hf : NeBot f) (m : α → β) : NeBot (map m f) :=
  (map_neBot_iff m).2 hf
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
theorem NeBot.of_map : NeBot (f.map m) → NeBot f :=
  (map_neBot_iff m).1
/-
**Filter.map_neBot** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：map_neBot [hf : NeBot f] : NeBot (f.map m)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.map`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α}, f.NeBo
t → ∀ (m : α → β), (Filter.map m f).NeBot
-/
instance map_neBot [hf : NeBot f] : NeBot (f.map m) :=
  hf.map m
/-
**Filter.sInter_comap_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sInter_comap_sets (f : α -> β) (F : Filter β) : ⋂₀ (comap f F).sets = ⋂ U 
in F, f ⁻¹' U
参数：f : α -> β；F : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sInter_comap_sets (f : α → β) (F : Filter β) : ⋂₀ (comap f F).sets = ⋂ U ∈ F, f ⁻¹' U := by
  ext x
  suffices (∀ (A : Set α) (B : Set β), B ∈ F → f ⁻¹' B ⊆ A → x ∈ A) ↔
      ∀ B : Set β, B ∈ F → f x ∈ B by
    simp only [mem_sInter, mem_iInter, Filter.mem_sets, mem_comap, this, and_imp,
      mem_preimage, exists_imp]
  constructor
  · intro h U U_in
    simpa only [Subset.rfl, forall_prop_of_true, mem_preimage] using h (f ⁻¹' U) U U_in
  · intro h V U U_in f_U_V
    exact f_U_V (h U U_in)

end Map

-- this is a generic rule for monotone functions:
/-
**Filter.map_iInf_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_iInf_le {f : ι -> Filter α} {m : α -> β} : map m (iInf f) <= ⨅ i, map 
m (f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem map_iInf_le {f : ι → Filter α} {m : α → β} : map m (iInf f) ≤ ⨅ i, map m (f i) :=
  le_iInf fun _ => map_mono <| iInf_le _ _
/-
**Filter.map_iInf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_iInf_eq {f : ι -> Filter α} {m : α -> β} (hf : Directed (· >= ·) f) [N
onempty ι] : map m (iInf f) = ⨅ i, map m (f i)
参数：hf : Directed (· >= ·) f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Filter.map_iInf_le`：map_iInf_le {f : ι -> Filter α} {m : α -> β} : map m
 (iInf f) <= ⨅ i, map m (f i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_iInf_of_directed`：mem_iInf_of_directed {f : ι -> Filter α} (h
 : Directed (· >= ·) f) [Nonempty ι] (s) : s in iInf f ↔ exists i, s in f i
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
-/
theorem map_iInf_eq {f : ι → Filter α} {m : α → β} (hf : Directed (· ≥ ·) f) [Nonempty ι] :
    map m (iInf f) = ⨅ i, map m (f i) :=
  map_iInf_le.antisymm fun s (hs : m ⁻¹' s ∈ iInf f) =>
    let ⟨i, hi⟩ := (mem_iInf_of_directed hf _).1 hs
    have : ⨅ i, map m (f i) ≤ 𝓟 s :=
      iInf_le_of_le i <| by simpa only [le_principal_iff, mem_map]
    Filter.le_principal_iff.1 this
/-
**Filter.map_biInf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_biInf_eq {ι : Type w} {f : ι -> Filter α} {m : α -> β} {p : ι -> Prop}
 (h : DirectedOn (f ⁻¹'o (· >= ·)) { x | p x }) (ne : exists i, p i) : map m (⨅ 
(i) (_ : p i), f i) = ⨅ (i) (_ : p i), map m (f i)
参数：h : DirectedOn (f ⁻¹'o (· >= ·)) { x | p x }；ne : exists i, p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `Filter.map_iInf_eq`：map_iInf_eq {f : ι -> Filter α} {m : α -> β} (hf : D
irected (· >= ·) f) [Nonempty ι] : map m (iInf f) = ⨅ i, map m (f i)
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
-/
theorem map_biInf_eq {ι : Type w} {f : ι → Filter α} {m : α → β} {p : ι → Prop}
    (h : DirectedOn (f ⁻¹'o (· ≥ ·)) { x | p x }) (ne : ∃ i, p i) :
    map m (⨅ (i) (_ : p i), f i) = ⨅ (i) (_ : p i), map m (f i) := by
  have := nonempty_subtype.2 ne
  simp only [iInf_subtype']
  exact map_iInf_eq h.directed_val
/-
**Filter.map_inf_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_inf_le {f g : Filter α} {m : α -> β} : map m (f ⊓ g) <= map m f ⊓ map 
m g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem map_inf_le {f g : Filter α} {m : α → β} : map m (f ⊓ g) ≤ map m f ⊓ map m g :=
  (@map_mono _ _ m).map_inf_le f g
/-
**Filter.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_inf {f g : Filter α} {m : α -> β} (h : Injective m) : map m (f ⊓ g) = 
map m f ⊓ map m g
参数：h : Injective m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Filter.map_inf_le`：map_inf_le {f g : Filter α} {m : α -> β} : map m (f ⊓
 g) <= map m f ⊓ map m g
· 使用定理 `Filter.mem_inf_of_inter`：mem_inf_of_inter {f g : Filter α} {s t u : Set 
α} (hs : s in f) (ht : t in g) (h : s inter t subseteq u) : u in f ⊓ g
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem map_inf {f g : Filter α} {m : α → β} (h : Injective m) :
    map m (f ⊓ g) = map m f ⊓ map m g := by
  refine map_inf_le.antisymm ?_
  rintro t ⟨s₁, hs₁, s₂, hs₂, ht : m ⁻¹' t = s₁ ∩ s₂⟩
  refine mem_inf_of_inter (image_mem_map hs₁) (image_mem_map hs₂) ?_
  rw [← image_inter h, image_subset_iff, ht]
/-
**Filter.map_inf'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_inf' {f g : Filter α} {m : α -> β} {t : Set α} (htf : t in f) (htg : t
 in g) (h : InjOn m t) : map m (f ⊓ g) = map m f ⊓ map m g
参数：htf : t in f；htg : t in g；h : InjOn m t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.InjOn.injective`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α 
→ β}, Set.InjOn f s → Function.Injective (s.domRestrict f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_inf`：map_inf {f g : Filter α} {m : α -> β} (h : Injective m) 
: map m (f ⊓ g) = map m f ⊓ map m g
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_inf' {f g : Filter α} {m : α → β} {t : Set α} (htf : t ∈ f) (htg : t ∈ g)
    (h : InjOn m t) : map m (f ⊓ g) = map m f ⊓ map m g := by
  lift f to Filter t using htf; lift g to Filter t using htg
  replace h : Injective (m ∘ ((↑) : t → α)) := h.injective
  simp only [map_map, ← map_inf Subtype.coe_injective, map_inf h]
/-
**Filter.disjoint_of_map** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：disjoint_of_map {α β : Type*} {F G : Filter α} {f : α -> β} (h : Disjoint 
(map f F) (map f G)) : Disjoint F G
参数：h : Disjoint (map f F) (map f G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.map_eq_bot_iff`：map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Filter.map_inf_le`：map_inf_le {f g : Filter α} {m : α -> β} : map m (f ⊓
 g) <= map m f ⊓ map m g
-/
lemma disjoint_of_map {α β : Type*} {F G : Filter α} {f : α → β}
    (h : Disjoint (map f F) (map f G)) : Disjoint F G :=
  disjoint_iff.mpr <| map_eq_bot_iff.mp <| le_bot_iff.mp <| trans map_inf_le (disjoint_iff.mp h)
/-
**Filter.disjoint_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_map {m : α -> β} (hm : Injective m) {f₁ f₂ : Filter α} : Disjoint
 (map m f₁) (map m f₂) ↔ Disjoint f₁ f₂
参数：hm : Injective m。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_inf`：map_inf {f g : Filter α} {m : α -> β} (h : Injective m) 
: map m (f ⊓ g) = map m f ⊓ map m g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_map {m : α → β} (hm : Injective m) {f₁ f₂ : Filter α} :
    Disjoint (map m f₁) (map m f₂) ↔ Disjoint f₁ f₂ := by
  simp only [disjoint_iff, ← map_inf hm, map_eq_bot_iff]
/-
**Filter.map_equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_equiv_symm (e : α ≃ β) (f : Filter β) : map e.symm f = comap e f
参数：e : α ≃ β；f : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_injective`：map_injective {m : α -> β} (hm : Injective m) : In
jective (map m)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Filter.map_id`：map_id : Filter.map id f = f
· 使用定理 `Filter.map_comap_of_surjective`：map_comap_of_surjective {f : α -> β} (hf
 : Surjective f) (l : Filter β) : map f (comap f l) = l
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem map_equiv_symm (e : α ≃ β) (f : Filter β) : map e.symm f = comap e f :=
  map_injective e.injective <| by
    rw [map_map, e.self_comp_symm, map_id, map_comap_of_surjective e.surjective]
/-
**Filter.map_eq_comap_of_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_eq_comap_of_inverse {f : Filter α} {m : α -> β} {n : β -> α} (h₁ : m ∘
 n = id) (h₂ : n ∘ m = id) : map m f = comap n f
参数：h₁ : m ∘ n = id；h₂ : n ∘ m = id。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_equiv_symm`：map_equiv_symm (e : α ≃ β) (f : Filter β) : map e
.symm f = comap e f
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem map_eq_comap_of_inverse {f : Filter α} {m : α → β} {n : β → α} (h₁ : m ∘ n = id)
    (h₂ : n ∘ m = id) : map m f = comap n f :=
  map_equiv_symm ⟨n, m, congr_fun h₁, congr_fun h₂⟩ f
/-
**Filter.comap_equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_equiv_symm (e : α ≃ β) (f : Filter α) : comap e.symm f = map e f
参数：e : α ≃ β；f : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Filter.map_eq_comap_of_inverse`：map_eq_comap_of_inverse {f : Filter α} {
m : α -> β} {n : β -> α} (h₁ : m ∘ n = id) (h₂ : n ∘ m = id) : map m f = comap n
 f
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
-/
theorem comap_equiv_symm (e : α ≃ β) (f : Filter α) : comap e.symm f = map e f :=
  (map_eq_comap_of_inverse e.self_comp_symm e.symm_comp_self).symm
/-
**Filter.map_swap_eq_comap_swap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_swap_eq_comap_swap {f : Filter (α × β)} : map Prod.swap f = comap Prod
.swap f
参数：α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_eq_comap_of_inverse`：map_eq_comap_of_inverse {f : Filter α} {
m : α -> β} {n : β -> α} (h₁ : m ∘ n = id) (h₂ : n ∘ m = id) : map m f = comap n
 f
· 使用定理 `Prod.swap_swap_eq`：∀ {α : Type u_1} {β : Type u_2}, Prod.swap ∘ Prod.swa
p = id
-/
theorem map_swap_eq_comap_swap {f : Filter (α × β)} : map Prod.swap f = comap Prod.swap f :=
  map_eq_comap_of_inverse Prod.swap_swap_eq Prod.swap_swap_eq

/-- A useful lemma when dealing with uniformities. -/
/-
**Filter.map_swap4_eq_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_swap4_eq_comap {f : Filter ((α × β) × γ × δ)} : map (fun p : (α × β) ×
 γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) f = comap (fun p : (α × γ) × β × δ =
> ((p.1.1, p.2.1), (p.1.2, p.2.2))) f
参数：(α × β) × γ × δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_eq_comap_of_inverse`：map_eq_comap_of_inverse {f : Filter α} {
m : α -> β} {n : β -> α} (h₁ : m ∘ n = id) (h₂ : n ∘ m = id) : map m f = comap n
 f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
A useful lemma when dealing with uniformities.
-/
theorem map_swap4_eq_comap {f : Filter ((α × β) × γ × δ)} :
    map (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) f =
      comap (fun p : (α × γ) × β × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) f :=
  map_eq_comap_of_inverse (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl) (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl)
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
theorem le_map {f : Filter α} {m : α → β} {g : Filter β} (h : ∀ s ∈ f, m '' s ∈ g) : g ≤ f.map m :=
  fun _ hs => mem_of_superset (h _ hs) <| image_preimage_subset _ _
/-
**Filter.le_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_map_iff {f : Filter α} {m : α -> β} {g : Filter β} : g <= f.map m ↔ for
all s in f, m '' s in g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `Filter.le_map`：le_map {f : Filter α} {m : α -> β} {g : Filter β} (h : fo
rall s in f, m '' s in g) : g <= f.map m
-/
theorem le_map_iff {f : Filter α} {m : α → β} {g : Filter β} : g ≤ f.map m ↔ ∀ s ∈ f, m '' s ∈ g :=
  ⟨fun h _ hs => h (image_mem_map hs), le_map⟩
/-
**Filter.push_pull** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (F : Filter α) (G : Filter β),
   Filter.map f (F ⊓ Filter.comap f G) = Filter.map f F ⊓ G
参数：f : α → β；F : Filter α；G : Filter β；F ⊓ Filter.comap f G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.map_inf_le`：map_inf_le {f g : Filter α} {m : α -> β} : map m (f ⊓
 g) <= map m f ⊓ map m g
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `Filter.map_comap_le`：map_comap_le : map m (comap m g) <= g
· 使用定理 `Filter.mem_inf_of_inter`：mem_inf_of_inter {f g : Filter α} {s t u : Set 
α} (hs : s in f) (ht : t in g) (h : s inter t subseteq u) : u in f ⊓ g
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inter_preimage`：image_inter_preimage (f : α -> β) (s : Set α) 
(t : Set β) : f '' (s inter f ⁻¹' t) = f '' s inter t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
-/
protected theorem push_pull (f : α → β) (F : Filter α) (G : Filter β) :
    map f (F ⊓ comap f G) = map f F ⊓ G := by
  apply le_antisymm
  · calc
      map f (F ⊓ comap f G) ≤ map f F ⊓ (map f <| comap f G) := map_inf_le
      _ ≤ map f F ⊓ G := inf_le_inf_left (map f F) map_comap_le
  · rintro U ⟨V, V_in, W, ⟨Z, Z_in, hZ⟩, h⟩
    apply mem_inf_of_inter (image_mem_map V_in) Z_in
    calc
      f '' V ∩ Z = f '' (V ∩ f ⁻¹' Z) := by rw [image_inter_preimage]
      _ ⊆ f '' (V ∩ W) := by gcongr
      _ = f '' f ⁻¹' U := by rw [h]
      _ ⊆ U := image_preimage_subset f U
/-
**Filter.push_pull'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (F : Filter α) (G : Filter β),
   Filter.map f (Filter.comap f G ⊓ F) = G ⊓ Filter.map f F
参数：f : α → β；F : Filter α；G : Filter β；Filter.comap f G ⊓ F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Filter.push_pull`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (F : Filte
r α) (G : Filter β),   Filter.map f (F ⊓ Filter.comap f G) = Filter.map f F ⊓ G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem push_pull' (f : α → β) (F : Filter α) (G : Filter β) :
    map f (comap f G ⊓ F) = G ⊓ map f F := by simp only [Filter.push_pull, inf_comm]
/-
**Filter.disjoint_comap_iff_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_comap_iff_map {f : α -> β} {F : Filter α} {G : Filter β} : Disjoi
nt F (comap f G) ↔ Disjoint (map f F) G
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_comap_iff_map {f : α → β} {F : Filter α} {G : Filter β} :
    Disjoint F (comap f G) ↔ Disjoint (map f F) G := by
  simp only [disjoint_iff, ← Filter.push_pull, map_eq_bot_iff]
/-
**Filter.disjoint_comap_iff_map'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：disjoint_comap_iff_map' {f : α -> β} {F : Filter α} {G : Filter β} : Disjo
int (comap f G) F ↔ Disjoint G (map f F)
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_comap_iff_map' {f : α → β} {F : Filter α} {G : Filter β} :
    Disjoint (comap f G) F ↔ Disjoint G (map f F) := by
  simp only [disjoint_iff, ← Filter.push_pull', map_eq_bot_iff]
/-
**Filter.neBot_inf_comap_iff_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：neBot_inf_comap_iff_map {f : α -> β} {F : Filter α} {G : Filter β} : NeBot
 (F ⊓ comap f G) ↔ NeBot (map f F ⊓ G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_neBot_iff`：map_neBot_iff (f : α -> β) {F : Filter α} : NeBot 
(map f F) ↔ NeBot F
· 使用定理 `Filter.push_pull`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (F : Filte
r α) (G : Filter β),   Filter.map f (F ⊓ Filter.comap f G) = Filter.map f F ⊓ G
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem neBot_inf_comap_iff_map {f : α → β} {F : Filter α} {G : Filter β} :
    NeBot (F ⊓ comap f G) ↔ NeBot (map f F ⊓ G) := by
  rw [← map_neBot_iff, Filter.push_pull]
/-
**Filter.neBot_inf_comap_iff_map'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：neBot_inf_comap_iff_map' {f : α -> β} {F : Filter α} {G : Filter β} : NeBo
t (comap f G ⊓ F) ↔ NeBot (G ⊓ map f F)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_neBot_iff`：map_neBot_iff (f : α -> β) {F : Filter α} : NeBot 
(map f F) ↔ NeBot F
· 使用定理 `Filter.push_pull'`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (F : Filt
er α) (G : Filter β),   Filter.map f (Filter.comap f G ⊓ F) = G ⊓ Filter.map f F
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem neBot_inf_comap_iff_map' {f : α → β} {F : Filter α} {G : Filter β} :
    NeBot (comap f G ⊓ F) ↔ NeBot (G ⊓ map f F) := by
  rw [← map_neBot_iff, Filter.push_pull']
/-
**Filter.comap_inf_principal_neBot_of_image_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filte
r`。
形式化陈述：comap_inf_principal_neBot_of_image_mem {f : Filter β} {m : α -> β} (hf : N
eBot f) {s : Set α} (hs : m '' s in f) : NeBot (comap m f ⊓ 𝓟 s)
参数：hf : NeBot f；hs : m '' s in f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.neBot_inf_comap_iff_map'`：neBot_inf_comap_iff_map' {f : α -> β} {
F : Filter α} {G : Filter β} : NeBot (comap f G ⊓ F) ↔ NeBot (G ⊓ map f F)
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Filter.frequently_mem_iff_neBot`：frequently_mem_iff_neBot {l : Filter α}
 {s : Set α} : (existsᶠ x in l, x in s) ↔ NeBot (l ⊓ 𝓟 s)
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
-/
theorem comap_inf_principal_neBot_of_image_mem {f : Filter β} {m : α → β} (hf : NeBot f) {s : Set α}
    (hs : m '' s ∈ f) : NeBot (comap m f ⊓ 𝓟 s) := by
  rw [neBot_inf_comap_iff_map', map_principal, ← frequently_mem_iff_neBot]
  exact Eventually.frequently hs
/-
**Filter.principal_eq_map_coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：principal_eq_map_coe_top (s : Set α) : 𝓟 s = map ((↑) : s -> α) ⊤
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_top`：map_top (f : α -> β) : map f ⊤ = 𝓟 (range f)
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem principal_eq_map_coe_top (s : Set α) : 𝓟 s = map ((↑) : s → α) ⊤ := by simp
/-
**Filter.inf_principal_eq_bot_iff_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inf_principal_eq_bot_iff_comap {F : Filter α} {s : Set α} : F ⊓ 𝓟 s = ⊥ ↔ 
comap ((↑) : s -> α) F = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.principal_eq_map_coe_top`：principal_eq_map_coe_top (s : Set α) : 
𝓟 s = map ((↑) : s -> α) ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.push_pull'`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (F : Filt
er α) (G : Filter β),   Filter.map f (Filter.comap f G ⊓ F) = G ⊓ Filter.map f F
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
· 使用定理 `Filter.map_eq_bot_iff`：map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inf_principal_eq_bot_iff_comap {F : Filter α} {s : Set α} :
    F ⊓ 𝓟 s = ⊥ ↔ comap ((↑) : s → α) F = ⊥ := by
  rw [principal_eq_map_coe_top s, ← Filter.push_pull', inf_top_eq, map_eq_bot_iff]
/-
**Filter.map_generate_le_generate_preimage_preimage** 是 Mathlib 中的一个引理，位于命名空间 `F
ilter`。
形式化陈述：map_generate_le_generate_preimage_preimage (U : Set (Set β)) (f : β -> α) 
: map f (generate U) <= generate ((f ⁻¹' ·) ⁻¹' U)
参数：U : Set (Set β)；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.le_generate_iff`：le_generate_iff {s : Set (Set α)} {f : Filter α}
 : f <= generate s ↔ s subseteq f.sets
· 使用引理 `Filter.mem_generate_of_mem`：mem_generate_of_mem {s : Set <| Set α} {U : 
Set α} (h : U in s) : U in generate s
-/
lemma map_generate_le_generate_preimage_preimage (U : Set (Set β)) (f : β → α) :
    map f (generate U) ≤ generate ((f ⁻¹' ·) ⁻¹' U) := by
  rw [le_generate_iff]
  exact fun u hu ↦ mem_generate_of_mem hu
/-
**Filter.generate_image_preimage_le_comap** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：generate_image_preimage_le_comap (U : Set (Set α)) (f : β -> α) : generate
 ((f ⁻¹' ·) '' U) <= comap f (generate U)
参数：U : Set (Set α)；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
· 使用定理 `Filter.le_generate_iff`：le_generate_iff {s : Set (Set α)} {f : Filter α}
 : f <= generate s ↔ s subseteq f.sets
· 使用引理 `Filter.mem_generate_of_mem`：mem_generate_of_mem {s : Set <| Set α} {U : 
Set α} (h : U in s) : U in generate s
-/
lemma generate_image_preimage_le_comap (U : Set (Set α)) (f : β → α) :
    generate ((f ⁻¹' ·) '' U) ≤ comap f (generate U) := by
  rw [← map_le_iff_le_comap, le_generate_iff]
  exact fun u hu ↦ mem_generate_of_mem ⟨u, hu, rfl⟩

section Applicative

/-
**Filter.singleton_mem_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：singleton_mem_pure {a : α} : {a} in (pure a : Filter α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem singleton_mem_pure {a : α} : {a} ∈ (pure a : Filter α) :=
  mem_singleton a
/-
**Filter.pure_injective** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pure_injective : Injective (pure : α -> Filter α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.ext_iff`：∀ {α : Type u_1} {f g : Filter α}, f = g ↔ ∀ (s : Set α)
, s ∈ f ↔ s ∈ g
-/
theorem pure_injective : Injective (pure : α → Filter α) := fun a _ hab =>
  (Filter.ext_iff.1 hab { x | a = x }).1 rfl
/-
**Filter.pure_neBot** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：pure_neBot {α : Type u} {a : α} : NeBot (pure a)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
instance pure_neBot {α : Type u} {a : α} : NeBot (pure a) :=
  ⟨mt empty_mem_iff_bot.2 <| notMem_empty a⟩

@[simp]
/-
**Filter.le_pure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_pure_iff {f : Filter α} {a : α} : f <= pure a ↔ {a} in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_pure_iff {f : Filter α} {a : α} : f ≤ pure a ↔ {a} ∈ f := by
  rw [← principal_singleton, le_principal_iff]
/-
**Filter.mem_seq_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_seq_def {f : Filter (α -> β)} {g : Filter α} {s : Set β} : s in f.seq 
g ↔ exists u in f, exists t in g, forall x in u, forall y in t, (x : α -> β) y i
n s
参数：α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_seq_def {f : Filter (α → β)} {g : Filter α} {s : Set β} :
    s ∈ f.seq g ↔ ∃ u ∈ f, ∃ t ∈ g, ∀ x ∈ u, ∀ y ∈ t, (x : α → β) y ∈ s :=
  Iff.rfl
/-
**Filter.mem_seq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_seq_iff {f : Filter (α -> β)} {g : Filter α} {s : Set β} : s in f.seq 
g ↔ exists u in f, exists t in g, Set.seq u t subseteq s
参数：α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem mem_seq_iff {f : Filter (α → β)} {g : Filter α} {s : Set β} :
    s ∈ f.seq g ↔ ∃ u ∈ f, ∃ t ∈ g, Set.seq u t ⊆ s := by
  simp only [mem_seq_def, seq_subset]
/-
**Filter.mem_map_seq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_map_seq_iff {f : Filter α} {g : Filter β} {m : α -> β -> γ} {s : Set γ
} : s in (f.map m).seq g ↔ exists t u, t in g ∧ u in f ∧ forall x in u, forall y
 in t, m x y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
-/
theorem mem_map_seq_iff {f : Filter α} {g : Filter β} {m : α → β → γ} {s : Set γ} :
    s ∈ (f.map m).seq g ↔ ∃ t u, t ∈ g ∧ u ∈ f ∧ ∀ x ∈ u, ∀ y ∈ t, m x y ∈ s :=
  Iff.intro (fun ⟨t, ht, s, hs, hts⟩ => ⟨s, m ⁻¹' t, hs, ht, fun _ => hts _⟩)
    fun ⟨t, s, ht, hs, hts⟩ =>
    ⟨m '' s, image_mem_map hs, t, ht, fun _ ⟨_, has, Eq⟩ => Eq ▸ hts _ has⟩
/-
**Filter.seq_mem_seq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：seq_mem_seq {f : Filter (α -> β)} {g : Filter α} {s : Set (α -> β)} {t : S
et α} (hs : s in f) (ht : t in g) : s.seq t in f.seq g
参数：α -> β；α -> β；hs : s in f；ht : t in g。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem seq_mem_seq {f : Filter (α → β)} {g : Filter α} {s : Set (α → β)} {t : Set α} (hs : s ∈ f)
    (ht : t ∈ g) : s.seq t ∈ f.seq g :=
  ⟨s, hs, t, ht, fun f hf a ha => ⟨f, hf, a, ha, rfl⟩⟩
/-
**Filter.le_seq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_seq {f : Filter (α -> β)} {g : Filter α} {h : Filter β} (hh : forall t 
in f, forall u in g, Set.seq t u in h) : h <= seq f g
参数：α -> β；hh : forall t in f, forall u in g, Set.seq t u in h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
theorem le_seq {f : Filter (α → β)} {g : Filter α} {h : Filter β}
    (hh : ∀ t ∈ f, ∀ u ∈ g, Set.seq t u ∈ h) : h ≤ seq f g := fun _ ⟨_, ht, _, hu, hs⟩ =>
  mem_of_superset (hh _ ht _ hu) fun _ ⟨_, hm, _, ha, eq⟩ => eq ▸ hs _ hm _ ha

@[gcongr, mono]
/-
**Filter.seq_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：seq_mono {f₁ f₂ : Filter (α -> β)} {g₁ g₂ : Filter α} (hf : f₁ <= f₂) (hg 
: g₁ <= g₂) : f₁.seq g₁ <= f₂.seq g₂
参数：α -> β；hf : f₁ <= f₂；hg : g₁ <= g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.le_seq`：le_seq {f : Filter (α -> β)} {g : Filter α} {h : Filter β
} (hh : forall t in f, forall u in g, Set.seq t u in h) : h <= seq f g
· 使用定理 `Filter.seq_mem_seq`：seq_mem_seq {f : Filter (α -> β)} {g : Filter α} {s 
: Set (α -> β)} {t : Set α} (hs : s in f) (ht : t in g) : s.seq t in f.seq g
-/
theorem seq_mono {f₁ f₂ : Filter (α → β)} {g₁ g₂ : Filter α} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
    f₁.seq g₁ ≤ f₂.seq g₂ :=
  le_seq fun _ hs _ ht => seq_mem_seq (hf hs) (hg ht)

@[simp]
/-
**Filter.pure_seq_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pure_seq_eq_map (g : α -> β) (f : Filter α) : seq (pure g) f = f.map g
参数：g : α -> β；f : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.le_map`：le_map {f : Filter α} {m : α -> β} {g : Filter β} (h : fo
rall s in f, m '' s in g) : g <= f.map m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.singleton_seq`：singleton_seq {f : α -> β} {t : Set α} : Set.seq ({f}
 : Set (α -> β)) t = f '' t
· 使用定理 `Filter.seq_mem_seq`：seq_mem_seq {f : Filter (α -> β)} {g : Filter α} {s 
: Set (α -> β)} {t : Set α} (hs : s in f) (ht : t in g) : s.seq t in f.seq g
· 使用定理 `Filter.singleton_mem_pure`：singleton_mem_pure {a : α} : {a} in (pure a :
 Filter α)
· 使用定理 `Filter.le_seq`：le_seq {f : Filter (α -> β)} {g : Filter α} {h : Filter β
} (hh : forall t in f, forall u in g, Set.seq t u in h) : h <= seq f g
· 使用定理 `Filter.sets_of_superset`：∀ {α : Type u_1} (self : Filter α) {x y : Set α
}, x ∈ self.sets → x ⊆ y → y ∈ self.sets
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
-/
theorem pure_seq_eq_map (g : α → β) (f : Filter α) : seq (pure g) f = f.map g := by
  refine le_antisymm (le_map fun s hs => ?_) (le_seq fun s hs t ht => ?_)
  · rw [← singleton_seq]
    apply seq_mem_seq _ hs
    exact singleton_mem_pure
  · refine sets_of_superset (map g f) (image_mem_map ht) ?_
    rintro b ⟨a, ha, rfl⟩
    exact ⟨g, hs, a, ha, rfl⟩

@[simp]
/-
**Filter.seq_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：seq_pure (f : Filter (α -> β)) (a : α) : seq f (pure a) = map (fun g : α -
> β => g a) f
参数：f : Filter (α -> β)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.le_map`：le_map {f : Filter α} {m : α -> β} {g : Filter β} (h : fo
rall s in f, m '' s in g) : g <= f.map m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.seq_singleton`：seq_singleton {s : Set (α -> β)} {a : α} : Set.seq s 
{a} = (fun f : α -> β => f a) '' s
· 使用定理 `Filter.seq_mem_seq`：seq_mem_seq {f : Filter (α -> β)} {g : Filter α} {s 
: Set (α -> β)} {t : Set α} (hs : s in f) (ht : t in g) : s.seq t in f.seq g
· 使用定理 `Filter.singleton_mem_pure`：singleton_mem_pure {a : α} : {a} in (pure a :
 Filter α)
· 使用定理 `Filter.le_seq`：le_seq {f : Filter (α -> β)} {g : Filter α} {h : Filter β
} (hh : forall t in f, forall u in g, Set.seq t u in h) : h <= seq f g
· 使用定理 `Filter.sets_of_superset`：∀ {α : Type u_1} (self : Filter α) {x y : Set α
}, x ∈ self.sets → x ⊆ y → y ∈ self.sets
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
-/
theorem seq_pure (f : Filter (α → β)) (a : α) : seq f (pure a) = map (fun g : α → β => g a) f := by
  refine le_antisymm (le_map fun s hs => ?_) (le_seq fun s hs t ht => ?_)
  · rw [← seq_singleton]
    exact seq_mem_seq hs singleton_mem_pure
  · refine sets_of_superset (map (fun g : α → β => g a) f) (image_mem_map hs) ?_
    rintro b ⟨g, hg, rfl⟩
    exact ⟨g, hg, a, ht, rfl⟩

@[simp]
/-
**Filter.seq_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：seq_assoc (x : Filter α) (g : Filter (α -> β)) (h : Filter (β -> γ)) : seq
 h (seq g x) = seq (seq (map (· ∘ ·) h) g) x
参数：x : Filter α；g : Filter (α -> β)；h : Filter (β -> γ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.le_seq`：le_seq {f : Filter (α -> β)} {g : Filter α} {h : Filter β
} (hh : forall t in f, forall u in g, Set.seq t u in h) : h <= seq f g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_seq_iff`：mem_seq_iff {f : Filter (α -> β)} {g : Filter α} {s 
: Set β} : s in f.seq g ↔ exists u in f, exists t in g, Set.seq u t subseteq s
· 使用定理 `Filter.mem_map_iff_exists_image`：mem_map_iff_exists_image : t in map m f
 ↔ exists s in f, m '' s subseteq t
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
· 使用定理 `Set.seq_mono`：seq_mono {s₀ s₁ : Set (α -> β)} {t₀ t₁ : Set α} (hs : s₀ s
ubseteq s₁) (ht : t₀ subseteq t₁) : seq s₀ t₀ subseteq seq s₁ t₁
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.seq_seq`：seq_seq {s : Set (β -> γ)} {t : Set (α -> β)} {u : Set α} :
 seq s (seq t u) = seq (seq ((· ∘ ·) '' s) t) u
· 使用定理 `Filter.seq_mem_seq`：seq_mem_seq {f : Filter (α -> β)} {g : Filter α} {s 
: Set (α -> β)} {t : Set α} (hs : s in f) (ht : t in g) : s.seq t in f.seq g
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
-/
theorem seq_assoc (x : Filter α) (g : Filter (α → β)) (h : Filter (β → γ)) :
    seq h (seq g x) = seq (seq (map (· ∘ ·) h) g) x := by
  refine le_antisymm (le_seq fun s hs t ht => ?_) (le_seq fun s hs t ht => ?_)
  · rcases mem_seq_iff.1 hs with ⟨u, hu, v, hv, hs⟩
    rcases mem_map_iff_exists_image.1 hu with ⟨w, hw, hu⟩
    grw [← hs, ← hu]
    rw [← Set.seq_seq]
    exact seq_mem_seq hw (seq_mem_seq hv ht)
  · rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩
    grw [← ht]
    rw [Set.seq_seq]
    exact seq_mem_seq (seq_mem_seq (image_mem_map hs) hu) hv
/-
**Filter.prod_map_seq_comm** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_map_seq_comm (f : Filter α) (g : Filter β) : (map Prod.mk f).seq g = 
seq (map (fun b a => (a, b)) g) f
参数：f : Filter α；g : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.le_seq`：le_seq {f : Filter (α -> β)} {g : Filter α} {h : Filter β
} (hh : forall t in f, forall u in g, Set.seq t u in h) : h <= seq f g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_map_iff_exists_image`：mem_map_iff_exists_image : t in map m f
 ↔ exists s in f, m '' s subseteq t
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
· 使用定理 `Set.seq_mono`：seq_mono {s₀ s₁ : Set (α -> β)} {t₀ t₁ : Set α} (hs : s₀ s
ubseteq s₁) (ht : t₀ subseteq t₁) : seq s₀ t₀ subseteq seq s₁ t₁
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.prod_image_seq_comm`：prod_image_seq_comm (s : Set α) (t : Set β) : (
Prod.mk '' s).seq t = seq ((fun b a => (a, b)) '' t) s
· 使用定理 `Filter.seq_mem_seq`：seq_mem_seq {f : Filter (α -> β)} {g : Filter α} {s 
: Set (α -> β)} {t : Set α} (hs : s in f) (ht : t in g) : s.seq t in f.seq g
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
-/
theorem prod_map_seq_comm (f : Filter α) (g : Filter β) :
    (map Prod.mk f).seq g = seq (map (fun b a => (a, b)) g) f := by
  refine le_antisymm (le_seq fun s hs t ht => ?_) (le_seq fun s hs t ht => ?_)
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    grw [← hs]
    rw [← Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    grw [← hs]
    rw [Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu
/-
**Filter.seq_eq_filter_seq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：seq_eq_filter_seq {α β : Type u} (f : Filter (α -> β)) (g : Filter α) : f 
<*> g = seq f g
参数：f : Filter (α -> β)；g : Filter α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem seq_eq_filter_seq {α β : Type u} (f : Filter (α → β)) (g : Filter α) :
    f <*> g = seq f g :=
  rfl
/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulApplicative (Filter : Type u → Type u) where
  map_pure := map_pure
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  seq_pure := seq_pure
  pure_seq := pure_seq_eq_map
  seq_assoc := seq_assoc
/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommApplicative (Filter : Type u → Type u) :=
  ⟨fun f g => prod_map_seq_comm f g⟩

end Applicative

/-! #### `bind` equations -/


section Bind

@[simp]
/-
**Filter.eventually_bind** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_bind {f : Filter α} {m : α -> Filter β} {p : β -> Prop} : (fora
llᶠ y in bind f m, p y) ↔ forallᶠ x in f, forallᶠ y in m x, p y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_bind {f : Filter α} {m : α → Filter β} {p : β → Prop} :
    (∀ᶠ y in bind f m, p y) ↔ ∀ᶠ x in f, ∀ᶠ y in m x, p y :=
  Iff.rfl

@[simp]
/-
**Filter.frequently_bind** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_bind {f : Filter α} {m : α -> Filter β} {p : β -> Prop} : (exis
tsᶠ y in bind f m, p y) ↔ existsᶠ x in f, existsᶠ y in m x, p y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_bind {f : Filter α} {m : α → Filter β} {p : β → Prop} :
    (∃ᶠ y in bind f m, p y) ↔ ∃ᶠ x in f, ∃ᶠ y in m x, p y := by
  rw [← not_iff_not]
  simp only [not_frequently, eventually_bind]

@[simp]
/-
**Filter.eventuallyEq_bind** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyEq_bind {f : Filter α} {m : α -> Filter β} {g₁ g₂ : β -> γ} : g₁
 =ᶠ[bind f m] g₂ ↔ forallᶠ x in f, g₁ =ᶠ[m x] g₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventuallyEq_bind {f : Filter α} {m : α → Filter β} {g₁ g₂ : β → γ} :
    g₁ =ᶠ[bind f m] g₂ ↔ ∀ᶠ x in f, g₁ =ᶠ[m x] g₂ :=
  Iff.rfl

@[simp]
/-
**Filter.eventuallyLE_bind** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyLE_bind [LE γ] {f : Filter α} {m : α -> Filter β} {g₁ g₂ : β -> 
γ} : g₁ <=ᶠ[bind f m] g₂ ↔ forallᶠ x in f, g₁ <=ᶠ[m x] g₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventuallyLE_bind [LE γ] {f : Filter α} {m : α → Filter β} {g₁ g₂ : β → γ} :
    g₁ ≤ᶠ[bind f m] g₂ ↔ ∀ᶠ x in f, g₁ ≤ᶠ[m x] g₂ :=
  Iff.rfl
/-
**Filter.mem_bind'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_bind' {s : Set β} {f : Filter α} {m : α -> Filter β} : s in bind f m ↔
 { a | s in m a } in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_bind' {s : Set β} {f : Filter α} {m : α → Filter β} :
    s ∈ bind f m ↔ { a | s ∈ m a } ∈ f :=
  Iff.rfl

@[simp]
/-
**Filter.mem_bind** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_bind {s : Set β} {f : Filter α} {m : α -> Filter β} : s in bind f m ↔ 
exists t in f, forall x in t, s in m x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.exists_mem_subset_iff`：exists_mem_subset_iff : (exists t in f, t 
subseteq s) ↔ s in f
-/
theorem mem_bind {s : Set β} {f : Filter α} {m : α → Filter β} :
    s ∈ bind f m ↔ ∃ t ∈ f, ∀ x ∈ t, s ∈ m x :=
  calc
    s ∈ bind f m ↔ { a | s ∈ m a } ∈ f := Iff.rfl
    _ ↔ ∃ t ∈ f, t ⊆ { a | s ∈ m a } := exists_mem_subset_iff.symm
    _ ↔ ∃ t ∈ f, ∀ x ∈ t, s ∈ m x := Iff.rfl
/-
**Filter.bind_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bind_le {f : Filter α} {g : α -> Filter β} {l : Filter β} (h : forallᶠ x i
n f, g x <= l) : f.bind g <= l
参数：h : forallᶠ x in f, g x <= l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.join_le`：join_le {f : Filter (Filter α)} {l : Filter α} (h : fora
llᶠ m in f, m <= l) : join f <= l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
-/
theorem bind_le {f : Filter α} {g : α → Filter β} {l : Filter β} (h : ∀ᶠ x in f, g x ≤ l) :
    f.bind g ≤ l :=
  join_le <| eventually_map.2 h

@[gcongr, mono]
/-
**Filter.bind_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bind_mono {f₁ f₂ : Filter α} {g₁ g₂ : α -> Filter β} (hf : f₁ <= f₂) (hg :
 g₁ <=ᶠ[f₁] g₂) : bind f₁ g₁ <= bind f₂ g₂
参数：hf : f₁ <= f₂；hg : g₁ <=ᶠ[f₁] g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.join_mono`：join_mono {f₁ f₂ : Filter (Filter α)} (h : f₁ <= f₂) :
 join f₁ <= join f₂
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem bind_mono {f₁ f₂ : Filter α} {g₁ g₂ : α → Filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ᶠ[f₁] g₂) :
    bind f₁ g₁ ≤ bind f₂ g₂ := by
  refine le_trans (fun s hs => ?_) (join_mono <| map_mono hf)
  simp only [mem_join, mem_bind', mem_map] at hs ⊢
  filter_upwards [hg, hs] with _ hx hs using hx hs
/-
**Filter.bind_inf_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bind_inf_principal {f : Filter α} {g : α -> Filter β} {s : Set β} : (f.bin
d fun x => g x ⊓ 𝓟 s) = f.bind g ⊓ 𝓟 s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem bind_inf_principal {f : Filter α} {g : α → Filter β} {s : Set β} :
    (f.bind fun x => g x ⊓ 𝓟 s) = f.bind g ⊓ 𝓟 s :=
  Filter.ext fun s => by simp only [mem_bind, mem_inf_principal]
/-
**Filter.sup_bind** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sup_bind {f g : Filter α} {h : α -> Filter β} : bind (f ⊔ g) h = bind f h 
⊔ bind g h
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_bind {f g : Filter α} {h : α → Filter β} : bind (f ⊔ g) h = bind f h ⊔ bind g h := rfl
/-
**Filter.principal_bind** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：principal_bind {s : Set α} {f : α -> Filter β} : bind (𝓟 s) f = ⨆ x in s, 
f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem principal_bind {s : Set α} {f : α → Filter β} : bind (𝓟 s) f = ⨆ x ∈ s, f x :=
  show join (map f (𝓟 s)) = ⨆ x ∈ s, f x by
    simp only [sSup_image, join_principal_eq_sSup, map_principal]

end Bind

end Filter

open Filter

variable {α β : Type*} {F : Filter α} {G : Filter β}

-- TODO(Anatole): unify with the global case
/-
**Filter.map_surjOn_Iic_iff_le_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_surjOn_Iic_iff_le_map {m : α -> β} : SurjOn (map m) (Iic F) (Ii
c G) ↔ G <= map m F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.push_pull`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (F : Filte
r α) (G : Filter β),   Filter.map f (F ⊓ Filter.comap f G) = Filter.map f F ⊓ G
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.RightInvOn.surjOn`：surjOn (hf : RightInvOn f' f t) (hf' : MapsTo f' 
t s) : SurjOn f s t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic
 b ↔ x ≤ b
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem Filter.map_surjOn_Iic_iff_le_map {m : α → β} :
    SurjOn (map m) (Iic F) (Iic G) ↔ G ≤ map m F := by
  refine ⟨fun hm ↦ ?_, fun hm ↦ ?_⟩
  · rcases hm self_mem_Iic with ⟨H, (hHF : H ≤ F), rfl⟩
    exact map_mono hHF
  · have : RightInvOn (F ⊓ comap m ·) (map m) (Iic G) :=
      fun H (hHG : H ≤ G) ↦ by simpa [Filter.push_pull] using hHG.trans hm
    exact this.surjOn fun H _ ↦ mem_Iic.mpr inf_le_left
/-
**Filter.map_surjOn_Iic_iff_surjOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_surjOn_Iic_iff_surjOn {s : Set α} {t : Set β} {m : α -> β} : Su
rjOn (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 t) ↔ SurjOn m s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_surjOn_Iic_iff_le_map`：Filter.map_surjOn_Iic_iff_le_map {m : 
α -> β} : SurjOn (map m) (Iic F) (Iic G) ↔ G <= map m F
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
· 使用定理 `Set.SurjOn.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t 
: Set β), Set.SurjOn f s t = (t ⊆ f '' s)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.map_surjOn_Iic_iff_surjOn {s : Set α} {t : Set β} {m : α → β} :
    SurjOn (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 t) ↔ SurjOn m s t := by
  rw [map_surjOn_Iic_iff_le_map, map_principal, principal_mono, SurjOn]

alias ⟨_, Set.SurjOn.filter_map_Iic⟩ := Filter.map_surjOn_Iic_iff_surjOn
/-
**Filter.filter_injOn_Iic_iff_injOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.filter_injOn_Iic_iff_injOn {s : Set α} {m : α -> β} : InjOn (map m)
 (Iic <| 𝓟 s) ↔ InjOn m s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Filter.pure_injective`：pure_injective : Injective (pure : α -> Filter α)
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `Set.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic
 b ↔ x ≤ b
· 使用定理 `Filter.pure_le_principal`：pure_le_principal {s : Set α} (a : α) : pure a
 <= 𝓟 s ↔ a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_pure`：map_pure (f : α -> β) (a : α) : map f (pure a) = pure (
f a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.map_eq_map_iff_of_injOn`：map_eq_map_iff_of_injOn {f g : Filter α}
 {m : α -> β} {s : Set α} (hsf : s in f) (hsg : s in g) (hm : InjOn m s) : map m
 f = map m g ↔ f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
-/
theorem Filter.filter_injOn_Iic_iff_injOn {s : Set α} {m : α → β} :
    InjOn (map m) (Iic <| 𝓟 s) ↔ InjOn m s := by
  refine ⟨fun hm x hx y hy hxy ↦ ?_, fun hm F hF G hG ↦ ?_⟩
  · rwa [← pure_injective.eq_iff, ← map_pure, ← map_pure, hm.eq_iff, pure_injective.eq_iff]
      at hxy <;> rwa [mem_Iic, pure_le_principal]
  · simp [map_eq_map_iff_of_injOn (le_principal_iff.mp hF) (le_principal_iff.mp hG) hm]

alias ⟨_, Set.InjOn.filter_map_Iic⟩ := Filter.filter_injOn_Iic_iff_injOn
