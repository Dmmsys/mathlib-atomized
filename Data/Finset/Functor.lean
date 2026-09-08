/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kim Morrison
-/
module

public import Batteries.Control.AlternativeMonad
public import Mathlib.Data.Finset.Lattice.Union
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Multiset.Functor

/-!
# Functoriality of `Finset`

This file defines the functor structure of `Finset`.

## TODO

Currently, all instances are classical because the functor classes want to run over all types. If
instead we could state that a functor is lawful/applicative/traversable... between two given types,
then we could provide the instances for types with decidable equality.
-/

@[expose] public section


universe u

open Function

namespace Finset

/-! ### Functor -/

section Functor

variable {α β : Type u} [∀ P, Decidable P]

/-- Because `Finset.image` requires a `DecidableEq` instance for the target type, we can only
construct `Functor Finset` when working classically. -/
/-
**Finset.functor** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：[(P : Prop) → Decidable P] → Functor Finset
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Because `Finset.image` requires a `DecidableEq` instance for the target type, we
 can only
construct `Functor Finset` when working classically.
-/
protected instance functor : Functor Finset where map f s := s.image f
/-
**Finset.lawfulFunctor** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：lawfulFunctor : LawfulFunctor Finset where id_map _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.image_id`：image_id [DecidableEq α] : s.image id = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
-/
instance lawfulFunctor : LawfulFunctor Finset where
  id_map _ := image_id
  comp_map _ _ _ := image_image.symm
  map_const {α} {β} := by simp only [Functor.mapConst, Functor.map]

@[simp]
/-
**Finset.fmap_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fmap_def {s : Finset α} (f : α -> β) : f < > s = s.image f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fmap_def {s : Finset α} (f : α → β) : f <$> s = s.image f := rfl

end Functor

/-! ### Pure -/


/-
**Finset.pure** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：Pure Finset
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Pure
-/
protected instance pure : Pure Finset :=
  ⟨fun x => {x}⟩

@[simp]
/-
**Finset.pure_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pure_def {α} : (pure : α -> Finset α) = singleton
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pure_def {α} : (pure : α → Finset α) = singleton := rfl

/-! ### Applicative functor -/


section Applicative

variable {α β : Type u} [∀ P, Decidable P]

/-
**Finset.applicative** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：[(P : Prop) → Decidable P] → Applicative Finset
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance applicative : Applicative Finset :=
  { Finset.functor, Finset.pure with
    seq := fun t s => t.sup fun f => (s ()).image f
    seqLeft := fun s t => if t () = ∅ then ∅ else s
    seqRight := fun s t => if s = ∅ then ∅ else t () }

@[simp]
/-
**Finset.seq_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：seq_def (s : Finset α) (t : Finset (α -> β)) : t <*> s = t.sup fun f => s.
image f
参数：s : Finset α；t : Finset (α -> β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem seq_def (s : Finset α) (t : Finset (α → β)) : t <*> s = t.sup fun f => s.image f :=
  rfl

@[simp]
/-
**Finset.seqLeft_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：seqLeft_def (s : Finset α) (t : Finset β) : s <* t = if t = ∅ then ∅ else 
s
参数：s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem seqLeft_def (s : Finset α) (t : Finset β) : s <* t = if t = ∅ then ∅ else s :=
  rfl

@[simp]
/-
**Finset.seqRight_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：seqRight_def (s : Finset α) (t : Finset β) : s *> t = if s = ∅ then ∅ else
 t
参数：s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem seqRight_def (s : Finset α) (t : Finset β) : s *> t = if s = ∅ then ∅ else t :=
  rfl

/-- `Finset.image₂` in terms of monadic operations. Note that this can't be taken as the definition
because of the lack of universe polymorphism. -/
/-
**Finset.image** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：image (f : α -> β) (s : Finset α) : Finset β
参数：f : α -> β；s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finset.image₂` in terms of monadic operations. Note that this can't be taken as
 the definition
because of the lack of universe polymorphism.
-/
theorem image₂_def {α β γ : Type u} (f : α → β → γ) (s : Finset α) (t : Finset β) :
    image₂ f s t = f <$> s <*> t := by
  ext
  simp [mem_sup]
/-
**Finset.lawfulApplicative** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：lawfulApplicative : LawfulApplicative Finset
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.seq_def`：seq_def (s : Finset α) (t : Finset (α -> β)) : t <*> s =
 t.sup fun f => s.image f
· 使用定理 `Finset.fmap_def`：fmap_def {s : Finset α} (f : α -> β) : f < > s = s.imag
e f
· 使用定理 `Finset.seqLeft_def`：seqLeft_def (s : Finset α) (t : Finset β) : s <* t =
 if t = ∅ then ∅ else s
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_bot`：sup_bot (s : Finset β) : (s.sup fun _ => ⊥) = (⊥ : α)
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
· 使用定理 `Finset.mem_sup`：∀ {α : Type u_2} {ι : Type u_5} [inst : DecidableEq α] {
s : Finset ι} {f : ι → Finset α} {a : α},   a ∈ s.sup f ↔ ∃ i ∈ s, a ∈ f i
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image_const_self`：mem_image_const_self : b in s.image (const 
α b) ↔ s.Nonempty
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.seqRight_def`：seqRight_def (s : Finset α) (t : Finset β) : s *> t
 = if s = ∅ then ∅ else t
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.image_empty`：image_empty (f : α -> β) : (∅ : Finset α).image f = 
∅
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `Finset.bot_eq_empty`：bot_eq_empty : (⊥ : Finset α) = ∅
· 使用定理 `Finset.image_id`：image_id [DecidableEq α] : s.image id = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `Finset.image_singleton`：image_singleton (f : α -> β) (a : α) : image f {
a} = {f a}
· 使用定理 `Finset.sup_singleton_apply`：sup_singleton_apply (s : Finset β) (f : β ->
 α) : (s.sup fun b => {f b}) = s.image f
（共 32 条，此处仅展示前 30 条）
-/
instance lawfulApplicative : LawfulApplicative Finset :=
  { Finset.lawfulFunctor with
    seqLeft_eq := fun s t => by
      rw [seq_def, fmap_def, seqLeft_def]
      obtain rfl | ht := t.eq_empty_or_nonempty
      · simp_rw [image_empty, if_true]
        exact (sup_bot _).symm
      · ext a
        rw [if_neg ht.ne_empty, mem_sup]
        refine ⟨fun ha => ⟨const _ a, mem_image_of_mem _ ha, mem_image_const_self.2 ht⟩, ?_⟩
        rintro ⟨f, hf, ha⟩
        rw [mem_image] at hf ha
        obtain ⟨b, hb, rfl⟩ := hf
        obtain ⟨_, _, rfl⟩ := ha
        exact hb
    seqRight_eq := fun s t => by
      rw [seq_def, fmap_def, seqRight_def]
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [if_pos rfl, image_empty, sup_empty, bot_eq_empty]
      · ext a
        rw [if_neg hs.ne_empty, mem_sup]
        refine ⟨fun ha => ⟨id, mem_image_const_self.2 hs, by rwa [image_id]⟩, ?_⟩
        rintro ⟨f, hf, ha⟩
        rw [mem_image] at hf ha
        obtain ⟨b, hb, rfl⟩ := ha
        obtain ⟨_, _, rfl⟩ := hf
        exact hb
    pure_seq := fun f s => by simp only [pure_def, seq_def, sup_singleton, fmap_def]
    map_pure := fun _ _ => image_singleton _ _
    seq_pure := fun _ _ => sup_singleton_apply _ _
    seq_assoc := fun s t u => by
      ext a
      simp_rw [seq_def, fmap_def]
      simp only [mem_sup, mem_image]
      constructor
      · rintro ⟨g, hg, b, ⟨f, hf, a, ha, rfl⟩, rfl⟩
        exact ⟨g ∘ f, ⟨comp g, ⟨g, hg, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩
      · rintro ⟨c, ⟨_, ⟨g, hg, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩
        exact ⟨g, hg, f a, ⟨f, hf, a, ha, rfl⟩, rfl⟩ }
/-
**Finset.commApplicative** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：commApplicative : CommApplicative Finset
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Finset.sup_eq_biUnion`：sup_eq_biUnion {α β} [DecidableEq β] (s : Finset 
α) (t : α -> Finset β) : s.sup t = s.biUnion t
· 使用定理 `Finset.product_eq_biUnion`：product_eq_biUnion [DecidableEq (α × β)] (s :
 Finset α) (t : Finset β) : s ×ˢ t = s.biUnion fun a => t.image fun b => (a, b)
· 使用定理 `Finset.product_eq_biUnion_right`：product_eq_biUnion_right [DecidableEq (
α × β)] (s : Finset α) (t : Finset β) : s ×ˢ t = t.biUnion fun b => s.image fun 
a => (a, b)
-/
instance commApplicative : CommApplicative Finset :=
  { Finset.lawfulApplicative with
    commutative_prod := fun s t => by
      simp_rw [seq_def, fmap_def, sup_image, sup_eq_biUnion]
      change (s.biUnion fun a => t.image fun b => (a, b))
        = t.biUnion fun b => s.image fun a => (a, b)
      trans s ×ˢ t <;> [rw [product_eq_biUnion]; rw [product_eq_biUnion_right]] }

end Applicative

/-! ### Monad -/


section Monad

variable [∀ P, Decidable P]

/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monad Finset :=
  { Finset.applicative with bind := sup }

@[simp]
/-
**Finset.bind_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：bind_def {α β} : (· >>= ·) = sup (α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_def {α β} : (· >>= ·) = sup (α := Finset α) (β := β) :=
  rfl
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMonad Finset :=
  { Finset.lawfulApplicative with
    bind_pure_comp := fun _ _ => sup_singleton_apply _ _
    bind_map := fun _ _ => rfl
    pure_bind := fun _ _ => sup_singleton
    bind_assoc := fun s f g => by simp only [bind, sup_eq_biUnion, biUnion_biUnion] }

end Monad

/-! ### Alternative functor -/


section Alternative

variable [∀ P, Decidable P]

/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AlternativeMonad Finset where
  orElse s t := s ∪ t ()
  failure := ∅
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulAlternative Finset where
  map_failure _ := Finset.image_empty _
  failure_seq _ := Finset.sup_empty
  orElse_failure _ := Finset.union_empty _
  failure_orElse _ := Finset.empty_union _
  orElse_assoc _ _ _ := Finset.union_assoc _ _ _ |>.symm
  map_orElse _ _ _ := Finset.image_union _ _

end Alternative

/-! ### Traversable functor -/


section Traversable

variable {α β γ : Type u} {F G : Type u → Type u} [Applicative F] [Applicative G]
  [CommApplicative F] [CommApplicative G]

/-- Traverse function for `Finset`. -/
/-
**Finset.traverse** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：traverse [DecidableEq β] (f : α -> F β) (s : Finset α) : F (Finset β)
参数：f : α -> F β；s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Traverse function for `Finset`.
-/
def traverse [DecidableEq β] (f : α → F β) (s : Finset α) : F (Finset β) :=
  Multiset.toFinset <$> Multiset.traverse f s.1

@[simp]
/-
**Finset.id_traverse** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：id_traverse [DecidableEq α] (s : Finset α) : traverse (pure : α -> Id α) s
 = pure s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCommApplicativeId`：CommApplicative Id
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.traverse.eq_1`：∀ {α β : Type u} {F : Type u → Type u} [inst : App
licative F] [inst_1 : CommApplicative F] [inst_2 : DecidableEq β]   (f : α → F β
) (s : Fin…
· 使用定理 `Multiset.id_traverse`：id_traverse {α : Type*} (x : Multiset α) : travers
e (pure : α -> Id α) x = pure x
· 使用定理 `Finset.val_toFinset`：val_toFinset [DecidableEq α] (s : Finset α) : s.val
.toFinset = s
-/
theorem id_traverse [DecidableEq α] (s : Finset α) : traverse (pure : α → Id α) s = pure s := by
  rw [traverse, Multiset.id_traverse]
  exact s.val_toFinset

open scoped Classical in
@[simp]
/-
**Finset.map_comp_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_comp_coe (h : α -> β) : Functor.map h ∘ Multiset.toFinset = Multiset.t
oFinset ∘ Functor.map h
参数：h : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.image_toFinset`：image_toFinset [DecidableEq α] {s : Multiset α} :
 s.toFinset.image f = (s.map f).toFinset
-/
theorem map_comp_coe (h : α → β) :
    Functor.map h ∘ Multiset.toFinset = Multiset.toFinset ∘ Functor.map h :=
  funext fun _ => image_toFinset

open scoped Classical in
@[simp]
/-
**Finset.map_comp_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_comp_coe_apply (h : α -> β) (s : Multiset α) : s.toFinset.image h = (h
 <$> s).toFinset
参数：h : α -> β；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.map_comp_coe`：map_comp_coe (h : α -> β) : Functor.map h ∘ Multise
t.toFinset = Multiset.toFinset ∘ Functor.map h
-/
theorem map_comp_coe_apply (h : α → β) (s : Multiset α) :
    s.toFinset.image h = (h <$> s).toFinset :=
  congrFun (map_comp_coe h) s

open scoped Classical in
/-
**Finset.map_traverse** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_traverse (g : α -> G β) (h : β -> γ) (s : Finset α) : Functor.map h < 
> traverse g s = traverse (Functor.map h ∘ g) s
参数：g : α -> G β；h : β -> γ；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.map_comp_coe_apply`：map_comp_coe_apply (h : α -> β) (s : Multiset
 α) : s.toFinset.image h = (h <$> s).toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_traverse (g : α → G β) (h : β → γ) (s : Finset α) :
    Functor.map h <$> traverse g s = traverse (Functor.map h ∘ g) s := by
  unfold traverse
  simp only [Functor.map_map, fmap_def, map_comp_coe_apply, Multiset.fmap_def, ←
    Multiset.map_traverse]

end Traversable

end Finset

