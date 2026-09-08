/-
Copyright (c) 2016 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Batteries.Control.AlternativeMonad
public import Mathlib.Control.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Notation

/-!
# Functoriality of `Set`

This file defines the functor structure of `Set`.
-/

@[expose] public section

universe u

open Function Set.Notation

namespace Set

variable {α β : Type u} {s : Set α} {f : α → Set β}

/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Alternative Set where
  pure a := {a}
  seq s t := s.seq (t ())
  seqLeft s t := {a | a ∈ s ∧ (t ()).Nonempty}
  seqRight s t := {b | s.Nonempty ∧ b ∈ t ()}
  map := Set.image
  orElse s t := s ∪ t ()
  failure := ∅

@[simp]
/-
**Set.fmap_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：fmap_eq_image (f : α -> β) : f < > s = f '' s
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fmap_eq_image (f : α → β) : f <$> s = f '' s :=
  rfl

@[simp]
/-
**Set.seq_eq_set_seq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：seq_eq_set_seq (s : Set (α -> β)) (t : Set α) : s <*> t = s.seq t
参数：s : Set (α -> β)；t : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem seq_eq_set_seq (s : Set (α → β)) (t : Set α) : s <*> t = s.seq t :=
  rfl

@[simp]
/-
**Set.seqLeft_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：seqLeft_def (s : Set α) (t : Set β) : s <* t = {a | a in s ∧ t.Nonempty}
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem seqLeft_def (s : Set α) (t : Set β) : s <* t = {a | a ∈ s ∧ t.Nonempty} :=
  rfl

@[simp]
/-
**Set.seqRight_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：seqRight_def (s : Set α) (t : Set β) : s *> t = {a | s.Nonempty ∧ a in t}
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem seqRight_def (s : Set α) (t : Set β) : s *> t = {a | s.Nonempty ∧ a ∈ t} :=
  rfl

@[simp]
/-
**Set.pure_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pure_def (a : α) : (pure a : Set α) = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pure_def (a : α) : (pure a : Set α) = {a} :=
  rfl

@[simp]
/-
**Set.failure_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：failure_def : (failure : Set α) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem failure_def : (failure : Set α) = ∅ :=
  rfl

@[simp]
/-
**Set.orElse_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：orElse_def (s : Set α) (t : Set α) : (s <|> t) = s union t
参数：s : Set α；t : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orElse_def (s : Set α) (t : Set α) : (s <|> t) = s ∪ t :=
  rfl

/-- `Set.image2` in terms of monadic operations. Note that this can't be taken as the definition
because of the lack of universe polymorphism. -/
/-
**Set.image2_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_def {α β γ : Type u} (f : α -> β -> γ) (s : Set α) (t : Set β) : im
age2 f s t = f < > s <*> t
参数：f : α -> β -> γ；s : Set α；t : Set β。
该定理/引理给出了一组等式。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`Set.image2` in terms of monadic operations. Note that this can't be taken as th
e definition
because of the lack of universe polymorphism.
-/
theorem image2_def {α β γ : Type u} (f : α → β → γ) (s : Set α) (t : Set β) :
    image2 f s t = f <$> s <*> t := by
  ext
  simp
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulAlternative Set where
  pure_seq _ _ := Set.singleton_seq
  seqLeft_eq _ _ := by simp [Set.seq, Set.image2, Set.nonempty_def]
  seqRight_eq s t := by simp [Set.seq, Set.image2, Set.nonempty_def]
  map_pure _ _ := Set.image_singleton
  seq_pure _ _ := Set.seq_singleton
  seq_assoc _ _ _ := Set.seq_seq
  map_failure _ := Set.image_empty _
  failure_seq _ := Set.image2_empty_left
  orElse_failure _ := Set.union_empty _
  failure_orElse _ := Set.empty_union _
  orElse_assoc _ _ _ := Set.union_assoc _ _ _ |>.symm
  map_orElse _ _ _ := Set.image_union _ _ _
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommApplicative Set where
  commutative_prod := prod_image_seq_comm

/-- The `Set` functor is a monad.

This is not a global instance because it does not have computational content,
so it does not make much sense using `do` notation in general.

Moreover, this would cause monad-related coercions and monad lifting logic to become activated.
Either use `attribute [local instance] Set.monad` to make it be a local instance
or use `SetM.run do ...` when `do` notation is wanted. -/
@[instance_reducible]
/-
**Set.monad** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：AlternativeMonad Set
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Set` functor is a monad.

This is not a global instance because it does not have computational content,
so it does not make much sense using `do` notation in general.

Moreover, this would cause monad-related coercions and monad lifting logic to be
come activated.
Either use `attribute [local instance] Set.monad` to make it be a local instance
or use `SetM.run do ...` when `do` notation is wanted.
-/
protected def monad : AlternativeMonad.{u} Set where
  __ : Alternative Set := inferInstance
  bind s f := ⋃ i ∈ s, f i

section with_instance
attribute [local instance] Set.monad

@[simp]
/-
**Set.bind_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bind_def : s >>= f = ⋃ i in s, f i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_def : s >>= f = ⋃ i ∈ s, f i :=
  rfl
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMonad Set where
  bind_pure_comp _ _ := (image_eq_iUnion _ _).symm
  bind_map _ _ := seq_def.symm
  pure_bind := biUnion_singleton
  bind_assoc _ _ _ := by simp only [bind_def, biUnion_iUnion]

/-! ### Monadic coercion lemmas -/

variable {β : Set α} {γ : Set β}

/-
**Set.mem_coe_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_coe_of_mem {a : α} (ha : a in β) (ha' : ⟨a, ha⟩ in γ) : a in (γ : Set 
α)
参数：ha : a in β；ha' : ⟨a, ha⟩ in γ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_coe_of_mem {a : α} (ha : a ∈ β) (ha' : ⟨a, ha⟩ ∈ γ) : a ∈ (γ : Set α) :=
  ⟨_, ⟨⟨_, rfl⟩, _, ⟨ha', rfl⟩, rfl⟩⟩
/-
**Set.coe_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：coe_subset : (γ : Set α) subseteq β
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coe_subset : (γ : Set α) ⊆ β := by
  intro _ ⟨_, ⟨⟨⟨_, ha⟩, rfl⟩, _, ⟨_, rfl⟩, _⟩⟩; convert! ha
/-
**Set.mem_of_mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_of_mem_coe {a : α} (ha : a in (γ : Set α)) : ⟨a, coe_subset ha⟩ in γ
参数：ha : a in (γ : Set α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.coe_subset`：coe_subset : (γ : Set α) subseteq β
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mem_of_mem_coe {a : α} (ha : a ∈ (γ : Set α)) : ⟨a, coe_subset ha⟩ ∈ γ := by
  rcases ha with ⟨_, ⟨_, rfl⟩, _, ⟨ha, rfl⟩, _⟩; convert! ha
/-
**Set.eq_univ_of_coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_univ_of_coe_eq (hγ : (γ : Set α) = β) : γ = univ
参数：hγ : (γ : Set α) = β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Set.mem_of_mem_coe`：mem_of_mem_coe {a : α} (ha : a in (γ : Set α)) : ⟨a,
 coe_subset ha⟩ in γ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_univ_of_coe_eq (hγ : (γ : Set α) = β) : γ = univ :=
  eq_univ_of_forall fun ⟨_, ha⟩ => mem_of_mem_coe <| hγ.symm ▸ ha
/-
**Set.image_coe_eq_domRestrict_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_coe_eq_domRestrict_image {δ : Type*} {f : α -> δ} : f '' γ = β.domRe
strict f '' γ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.coe_subset`：coe_subset : (γ : Set α) subseteq β
· 使用定理 `Set.mem_of_mem_coe`：mem_of_mem_coe {a : α} (ha : a in (γ : Set α)) : ⟨a,
 coe_subset ha⟩ in γ
· 使用定理 `Set.mem_coe_of_mem`：mem_coe_of_mem {a : α} (ha : a in β) (ha' : ⟨a, ha⟩ 
in γ) : a in (γ : Set α)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem image_coe_eq_domRestrict_image {δ : Type*} {f : α → δ} : f '' γ = β.domRestrict f '' γ :=
  ext fun _ =>
    ⟨fun ⟨_, h, ha⟩ => ⟨_, mem_of_mem_coe h, ha⟩, fun ⟨_, h, ha⟩ => ⟨_, mem_coe_of_mem _ h, ha⟩⟩

@[deprecated (since := "2026-07-19")]
alias image_coe_eq_restrict_image := image_coe_eq_domRestrict_image

end with_instance

/-! ### Coercion applying functoriality for `Subtype.val`
The `Monad` instance gives a coercion using the internal function `Lean.Internal.coeM`.
In practice this is only used for applying the `Set` functor to `Subtype.val`,
as was defined in `Data.Set.Notation`. -/

attribute [local instance] Set.monad in
/-- The coercion from `Set.monad` as an instance is equal to the coercion in `Data.Set.Notation`. -/
/-
**Set.coe_eq_image_val** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：coe_eq_image_val (t : Set s) : @Lean.Internal.coeM Set s α _ _ t = Subtype
.val '' t
参数：t : Set s。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The coercion from `Set.monad` as an instance is equal to the coercion in `Data.S
et.Notation`.
-/
theorem coe_eq_image_val (t : Set s) :
    @Lean.Internal.coeM Set s α _ _ t = Subtype.val '' t := by
  change ⋃ (x ∈ t), {x.1} = _
  ext
  simp

variable {β : Set α} {γ : Set β} {a : α}
/-
**Set.mem_image_val_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_image_val_of_mem (ha : a in β) (ha' : ⟨a, ha⟩ in γ) : a in (γ : Set α)
参数：ha : a in β；ha' : ⟨a, ha⟩ in γ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_image_val_of_mem (ha : a ∈ β) (ha' : ⟨a, ha⟩ ∈ γ) : a ∈ (γ : Set α) :=
  ⟨_, ha', rfl⟩
/-
**Set.image_val_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_val_subset : (γ : Set α) subseteq β
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_image_subset`：coe_image_subset (s : Set α) (t : Set s) : ((↑
) : s -> α) '' t subseteq s
-/
theorem image_val_subset : (γ : Set α) ⊆ β := Subtype.coe_image_subset _ _
/-
**Set.mem_of_mem_image_val** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_of_mem_image_val (ha : a in (γ : Set α)) : ⟨a, image_val_subset ha⟩ in
 γ
参数：ha : a in (γ : Set α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_val_subset`：image_val_subset : (γ : Set α) subseteq β
-/
theorem mem_of_mem_image_val (ha : a ∈ (γ : Set α)) : ⟨a, image_val_subset ha⟩ ∈ γ := by
  rcases ha with ⟨_, ha, rfl⟩; exact ha
/-
**Set.eq_univ_of_image_val_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_univ_of_image_val_eq (hγ : (γ : Set α) = β) : γ = univ
参数：hγ : (γ : Set α) = β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Set.mem_of_mem_image_val`：mem_of_mem_image_val (ha : a in (γ : Set α)) :
 ⟨a, image_val_subset ha⟩ in γ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_univ_of_image_val_eq (hγ : (γ : Set α) = β) : γ = univ :=
  eq_univ_of_forall fun ⟨_, ha⟩ => mem_of_mem_image_val <| hγ.symm ▸ ha
/-
**Set.image_image_val_eq_domRestrict_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_image_val_eq_domRestrict_image {δ : Type*} {f : α -> δ} : f '' γ = β
.domRestrict f '' γ
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
theorem image_image_val_eq_domRestrict_image {δ : Type*} {f : α → δ} :
    f '' γ = β.domRestrict f '' γ := by
  ext; simp

@[deprecated (since := "2026-07-19")]
alias image_image_val_eq_restrict_image := image_image_val_eq_domRestrict_image

end Set

/-! ### Wrapper to enable the `Set` monad -/

/-- This is `Set` but with a `Monad` instance. -/
/-
**SetM** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SetM (α : Type u)
参数：α : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is `Set` but with a `Monad` instance.
-/
def SetM (α : Type u) := Set α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AlternativeMonad SetM := fast_instance% Set.monad
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMonad SetM := Set.instLawfulMonad
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulAlternative SetM := Set.instLawfulAlternative

/-- Evaluates the `SetM` monad, yielding a `Set`.
Implementation note: this is the identity function. -/
/-
**SetM.run** 是 Mathlib 中的一个定义，位于命名空间 `SetM`。
形式化陈述：{α : Type u_1} → SetM α → Set α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the `SetM` monad, yielding a `Set`.
Implementation note: this is the identity function.
-/
protected def SetM.run {α : Type*} (s : SetM α) : Set α := s
