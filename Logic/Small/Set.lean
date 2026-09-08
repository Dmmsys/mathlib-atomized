/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Timothy Carlin-Burns
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Logic.Small.Basic

/-!
# Results about `Small` on coerced sets
-/

public section

universe u u1 u2 u3 u4

variable {α : Type u1} {β : Type u2} {γ : Type u3} {ι : Type u4}

/-
**small_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u} s] : Small.{u} 
t
参数：hts : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
-/
theorem small_subset {s t : Set α} (hts : t ⊆ s) [Small.{u} s] : Small.{u} t :=
  small_of_injective (Set.inclusion_injective hts)
/-
**small_powerset** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_powerset (s : Set α) [Small.{u} s] : Small.{u} (𝒫 s)
参数：s : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_map`：small_map {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃
 β) : Small.{w} α
-/
instance small_powerset (s : Set α) [Small.{u} s] : Small.{u} (𝒫 s) :=
  small_map (Equiv.Set.powerset s)
/-
**small_setProd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_setProd (s : Set α) (t : Set β) [Small.{u} s] [Small.{u} t] : Small.
{u} (s ×ˢ t : Set (α × β))
参数：s : Set α；t : Set β。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
instance small_setProd (s : Set α) (t : Set β) [Small.{u} s] [Small.{u} t] :
    Small.{u} (s ×ˢ t : Set (α × β)) :=
  small_of_injective (Equiv.Set.prod s t).injective
/-
**small_setPi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_setPi {β : α -> Type u2} (s : (a : α) -> Set (β a)) [Small.{u} α] [f
orall a, Small.{u} (s a)] : Small.{u} (Set.pi Set.univ s)
参数：s : (a : α) -> Set (β a)；s a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
instance small_setPi {β : α → Type u2} (s : (a : α) → Set (β a))
    [Small.{u} α] [∀ a, Small.{u} (s a)] : Small.{u} (Set.pi Set.univ s) :=
  small_of_injective (Equiv.Set.univPi s).injective
/-
**small_range** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_range (f : α -> β) [Small.{u} α] : Small.{u} (Set.range f)
参数：f : α -> β。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)
-/
instance small_range (f : α → β) [Small.{u} α] :
    Small.{u} (Set.range f) :=
  small_of_surjective Set.rangeFactorization_surjective
/-
**small_image** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_image (f : α -> β) (s : Set α) [Small.{u} s] : Small.{u} (f '' s)
参数：f : α -> β；s : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用定理 `Set.imageFactorization_surjective`：imageFactorization_surjective {f : α 
-> β} {s : Set α} : Surjective (imageFactorization f s)
-/
instance small_image (f : α → β) (s : Set α) [Small.{u} s] :
    Small.{u} (f '' s) :=
  small_of_surjective Set.imageFactorization_surjective
/-
**small_image2** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_image2 (f : α -> β -> γ) (s : Set α) (t : Set β) [Small.{u} s] [Smal
l.{u} t] : Small.{u} (Set.image2 f s t)
参数：f : α -> β -> γ；s : Set α；t : Set β。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_uncurry_prod`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} (
f : α → β → γ) (s : Set α) (t : Set β),   Function.uncurry f '' s ×ˢ t = Set.ima
ge2 f s t
-/
instance small_image2 (f : α → β → γ) (s : Set α) (t : Set β) [Small.{u} s] [Small.{u} t] :
    Small.{u} (Set.image2 f s t) := by
  rw [← Set.image_uncurry_prod]
  infer_instance
/-
**small_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：small_univ_iff : Small.{u} (@Set.univ α) ↔ Small.{u} α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_congr`：small_congr {α : Type*} {β : Type*} (e : α ≃ β) : Small.{w}
 α ↔ Small.{w} β
-/
theorem small_univ_iff : Small.{u} (@Set.univ α) ↔ Small.{u} α :=
  small_congr <| Equiv.Set.univ α
/-
**small_univ** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_univ [h : Small.{u} α] : Small.{u} (@Set.univ α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `small_univ_iff`：small_univ_iff : Small.{u} (@Set.univ α) ↔ Small.{u} α
-/
instance small_univ [h : Small.{u} α] : Small.{u} (@Set.univ α) :=
  small_univ_iff.2 h
/-
**small_union** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_union (s t : Set α) [Small.{u} s] [Small.{u} t] : Small.{u} (s union
 t : Set α)
参数：s t : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
· 使用定理 `Set.Sum.elim_range`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : 
α → γ) (g : β → γ),   Set.range (Sum.elim f g) = Set.range f ∪ Set.range g
-/
instance small_union (s t : Set α) [Small.{u} s] [Small.{u} t] :
    Small.{u} (s ∪ t : Set α) := by
  rw [← Subtype.range_val (s := s), ← Subtype.range_val (s := t), ← Set.Sum.elim_range]
  infer_instance
/-
**small_iUnion** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_iUnion [Small.{u} ι] (s : ι -> Set α) [forall i, Small.{u} (s i)] : 
Small.{u} (⋃ i, s i)
参数：s : ι -> Set α；s i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用定理 `Set.sigmaToiUnion_surjective`：sigmaToiUnion_surjective : Surjective (sig
maToiUnion t) | ⟨b, hb⟩ => have : exists a, b in t a
-/
instance small_iUnion [Small.{u} ι] (s : ι → Set α)
    [∀ i, Small.{u} (s i)] : Small.{u} (⋃ i, s i) :=
  small_of_surjective <| Set.sigmaToiUnion_surjective _
/-
**small_sUnion** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_sUnion (s : Set (Set α)) [Small.{u} s] [forall t : s, Small.{u} t] :
 Small.{u} (⋃₀ s)
参数：s : Set (Set α)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
-/
instance small_sUnion (s : Set (Set α)) [Small.{u} s] [∀ t : s, Small.{u} t] :
    Small.{u} (⋃₀ s) :=
  Set.sUnion_eq_iUnion ▸ small_iUnion _
/-
**small_biUnion** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_biUnion (s : Set ι) [Small.{u} s] (f : (i : ι) -> i in s -> Set α) [
forall i hi, Small.{u} (f i hi)] : Small.{u} (⋃ i, ⋃ hi, f i hi)
参数：s : Set ι；f : (i : ι) -> i in s -> Set α；f i hi。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
-/
instance small_biUnion (s : Set ι) [Small.{u} s]
    (f : (i : ι) → i ∈ s → Set α) [∀ i hi, Small.{u} (f i hi)] : Small.{u} (⋃ i, ⋃ hi, f i hi) :=
  Set.biUnion_eq_iUnion s f ▸ small_iUnion _
/-
**small_insert** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_insert (x : α) (s : Set α) [Small.{u} s] : Small.{u} (insert x s : S
et α)
参数：x : α；s : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subsingleton`：∀ (α : Type v) [Subsingleton α], Small.{w, v} α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
-/
instance small_insert (x : α) (s : Set α) [Small.{u} s] :
    Small.{u} (insert x s : Set α) :=
  Set.insert_eq x s ▸ small_union.{u} {x} s
/-
**small_diff** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_diff (s t : Set α) [Small.{u} s] : Small.{u} (s \ t : Set α)
参数：s t : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
instance small_diff (s t : Set α) [Small.{u} s] : Small.{u} (s \ t : Set α) :=
  small_subset (Set.sdiff_subset)
/-
**small_sep** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_sep (s : Set α) (P : α -> Prop) [Small.{u} s] : Small.{u} { x | x in
 s ∧ P x}
参数：s : Set α；P : α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Set.sep_subset`：sep_subset (s : Set α) (p : α -> Prop) : { x in s | p x 
} subseteq s
-/
instance small_sep (s : Set α) (P : α → Prop) [Small.{u} s] :
    Small.{u} { x | x ∈ s ∧ P x} :=
  small_subset (Set.sep_subset s P)
/-
**small_inter_of_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_inter_of_left (s t : Set α) [Small.{u} s] : Small.{u} (s inter t : S
et α)
参数：s t : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
instance small_inter_of_left (s t : Set α) [Small.{u} s] :
    Small.{u} (s ∩ t : Set α) :=
  small_subset Set.inter_subset_left
/-
**small_inter_of_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_inter_of_right (s t : Set α) [Small.{u} t] : Small.{u} (s inter t : 
Set α)
参数：s t : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
instance small_inter_of_right (s t : Set α) [Small.{u} t] :
    Small.{u} (s ∩ t : Set α) :=
  small_subset Set.inter_subset_right
/-
**small_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：small_iInter (s : ι -> Set α) (i : ι) [Small.{u} (s i)] : Small.{u} (⋂ i, 
s i)
参数：s : ι -> Set α；i : ι；s i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
-/
theorem small_iInter (s : ι → Set α) (i : ι)
    [Small.{u} (s i)] : Small.{u} (⋂ i, s i) :=
  small_subset (Set.iInter_subset s i)
/-
**small_iInter'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_iInter' [Nonempty ι] (s : ι -> Set α) [forall i, Small.{u} (s i)] : 
Small.{u} (⋂ i, s i)
参数：s : ι -> Set α；s i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_iInter`：small_iInter (s : ι -> Set α) (i : ι) [Small.{u} (s i)] : 
Small.{u} (⋂ i, s i)
-/
instance small_iInter' [Nonempty ι] (s : ι → Set α)
    [∀ i, Small.{u} (s i)] : Small.{u} (⋂ i, s i) :=
  let ⟨i⟩ : Nonempty ι := inferInstance
  small_iInter s i
/-
**small_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：small_sInter {s : Set (Set α)} {t : Set α} (ht : t in s) [Small.{u} t] : S
mall.{u} (⋂₀ s)
参数：Set α；ht : t in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_iInter`：small_iInter (s : ι -> Set α) (i : ι) [Small.{u} (s i)] : 
Small.{u} (⋂ i, s i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_eq_iInter`：sInter_eq_iInter {s : Set (Set α)} : ⋂₀ s = ⋂ i : 
s, i
-/
theorem small_sInter {s : Set (Set α)} {t : Set α} (ht : t ∈ s)
    [Small.{u} t] : Small.{u} (⋂₀ s) :=
  Set.sInter_eq_iInter ▸ small_iInter _ ⟨t, ht⟩
/-
**small_sInter'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_sInter' {s : Set (Set α)} [Nonempty s] [forall t : s, Small.{u} t] :
 Small.{u} (⋂₀ s)
参数：Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_sInter`：small_sInter {s : Set (Set α)} {t : Set α} (ht : t in s) [
Small.{u} t] : Small.{u} (⋂₀ s)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
instance small_sInter' {s : Set (Set α)} [Nonempty s]
    [∀ t : s, Small.{u} t] : Small.{u} (⋂₀ s) :=
  let ⟨t⟩ : Nonempty s := inferInstance
  small_sInter t.prop
/-
**small_biInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：small_biInter {s : Set ι} {i : ι} (hi : i in s) (f : (i : ι) -> i in s -> 
Set α) [Small.{u} (f i hi)] : Small.{u} (⋂ i, ⋂ hi, f i hi)
参数：hi : i in s；f : (i : ι) -> i in s -> Set α；f i hi。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `small_iInter`：small_iInter (s : ι -> Set α) (i : ι) [Small.{u} (s i)] : 
Small.{u} (⋂ i, s i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biInter_eq_iInter`：biInter_eq_iInter (s : Set α) (t : forall x in s,
 Set β) : ⋂ x in s, t x ‹_› = ⋂ x : s, t x x.2
-/
theorem small_biInter {s : Set ι} {i : ι} (hi : i ∈ s)
    (f : (i : ι) → i ∈ s → Set α) [Small.{u} (f i hi)] : Small.{u} (⋂ i, ⋂ hi, f i hi) :=
  Set.biInter_eq_iInter s f ▸ small_iInter _ ⟨i, hi⟩
/-
**small_biInter'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_biInter' (s : Set ι) [Nonempty s] (f : (i : ι) -> i in s -> Set α) [
forall i hi, Small.{u} (f i hi)] : Small.{u} (⋂ i, ⋂ hi, f i hi)
参数：s : Set ι；f : (i : ι) -> i in s -> Set α；f i hi。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_biInter`：small_biInter {s : Set ι} {i : ι} (hi : i in s) (f : (i :
 ι) -> i in s -> Set α) [Small.{u} (f i hi)] : Small.{u} (⋂ i, ⋂ hi, f i hi)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
instance small_biInter' (s : Set ι) [Nonempty s]
    (f : (i : ι) → i ∈ s → Set α) [∀ i hi, Small.{u} (f i hi)] : Small.{u} (⋂ i, ⋂ hi, f i hi) :=
  let ⟨t⟩ : Nonempty s := inferInstance
  small_biInter t.prop f
/-
**small_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：small_empty : Small.{u} (∅ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subsingleton`：∀ (α : Type v) [Subsingleton α], Small.{w, v} α
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
-/
theorem small_empty : Small.{u} (∅ : Set α) :=
  inferInstance
/-
**small_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：small_single (x : α) : Small.{u} ({x} : Set α)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subsingleton`：∀ (α : Type v) [Subsingleton α], Small.{w, v} α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem small_single (x : α) : Small.{u} ({x} : Set α) :=
  inferInstance
/-
**small_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：small_pair (x y : α) : Small.{u} ({x, y} : Set α)
参数：x y : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subsingleton`：∀ (α : Type v) [Subsingleton α], Small.{w, v} α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem small_pair (x y : α) : Small.{u} ({x, y} : Set α) :=
  inferInstance
