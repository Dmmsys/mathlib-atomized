/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Adjoining Elements to Fields

In this file we introduce the notion of adjoining elements to fields.
This isn't quite the same as adjoining elements to rings.
For example, `K[x]` might not include `x⁻¹`.

## Notation

- `F⟮α⟯`: adjoin a single element `α` to `F` (in scope `IntermediateField`).
-/

@[expose] public section

open Module Polynomial

namespace IntermediateField

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E)

/-- `adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`. -/
@[stacks 09FZ "first part"]
/-
**IntermediateField.adjoin** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：adjoin : IntermediateField F E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`.
-/
def adjoin : IntermediateField F E :=
  { Subfield.closure (Set.range (algebraMap F E) ∪ S) with
    algebraMap_mem' := fun x => Subfield.subset_closure (Or.inl (Set.mem_range_self x)) }

@[simp]
/-
**IntermediateField.adjoin_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：adjoin_toSubfield : (adjoin F S).toSubfield = Subfield.closure (Set.range 
(algebraMap F E) union S)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjoin_toSubfield :
    (adjoin F S).toSubfield = Subfield.closure (Set.range (algebraMap F E) ∪ S) := rfl

variable {F S} in
/-
**IntermediateField.mem_adjoin_iff_div** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：mem_adjoin_iff_div {x : E} : x in adjoin F S ↔ exists r in Algebra.adjoin 
F S, exists s in Algebra.adjoin F S, x = r / s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_adjoin_iff_div {x : E} : x ∈ adjoin F S ↔
    ∃ r ∈ Algebra.adjoin F S, ∃ s ∈ Algebra.adjoin F S, x = r / s := by
  simp_rw [adjoin, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring,
    Subfield.mem_closure_iff, ← Algebra.adjoin_eq_ring_closure, Subalgebra.mem_toSubring, eq_comm]

end AdjoinDef

section Lattice

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

@[simp]
/-
**IntermediateField.adjoin_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_le_iff {S : Set E} {T : IntermediateField F E} : adjoin F S <= T ↔ 
S subseteq T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Subfield.subset_closure`：subset_closure {s : Set K} : s subseteq closure
 s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subfield.closure_le`：closure_le {s : Set K} {t : Subfield K} : closure s
 <= t ↔ s subseteq t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `IntermediateField.set_range_subset`：set_range_subset : Set.range (algebr
aMap K L) subseteq S
-/
theorem adjoin_le_iff {S : Set E} {T : IntermediateField F E} : adjoin F S ≤ T ↔ S ⊆ T :=
  ⟨fun H => le_trans (le_trans Set.subset_union_right Subfield.subset_closure) H, fun H =>
    (@Subfield.closure_le E _ (Set.range (algebraMap F E) ∪ S) T.toSubfield).mpr
      (Set.union_subset (IntermediateField.set_range_subset T) H)⟩
/-
**IntermediateField.gc** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：gc : GaloisConnection (adjoin F : Set E -> IntermediateField F E) (fun (x 
: IntermediateField F E) => (x : Set E))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
-/
theorem gc : GaloisConnection (adjoin F : Set E → IntermediateField F E)
    (fun (x : IntermediateField F E) => (x : Set E)) := fun _ _ =>
  adjoin_le_iff

/-- Galois insertion between `adjoin` and `coe`. -/
/-
**IntermediateField.gi** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：gi : GaloisInsertion (adjoin F : Set E -> IntermediateField F E) (fun (x :
 IntermediateField F E) => (x : Set E)) where choice s hs
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.gc`：gc : GaloisConnection (adjoin F : Set E -> Interme
diateField F E) (fun (x : IntermediateField F E) => (x : Set E))

--- 原说明 ---
Galois insertion between `adjoin` and `coe`.
-/
def gi : GaloisInsertion (adjoin F : Set E → IntermediateField F E)
    (fun (x : IntermediateField F E) => (x : Set E)) where
  choice s hs := (adjoin F s).copy s <| le_antisymm (gc.le_u_l s) hs
  gc := IntermediateField.gc
  le_l_u S := (IntermediateField.gc (S : Set E) (adjoin F S)).1 <| le_rfl
  choice_eq _ _ := copy_eq _ _ _
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (IntermediateField F E) where
  __ := GaloisInsertion.liftCompleteLattice IntermediateField.gi
  bot :=
    { toSubalgebra := ⊥
      inv_mem' := by rintro x ⟨r, rfl⟩; exact ⟨r⁻¹, map_inv₀ _ _⟩ }
  bot_le x := (bot_le : ⊥ ≤ x.toSubalgebra)
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K₁ K₂ : IntermediateField F E) : Algebra ↥(K₁ ⊓ K₂) K₁ :=
  inferInstanceAs <| Algebra ↑(K₁.toSubalgebra ⊓ K₂.toSubalgebra) K₁.toSubalgebra
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K₁ K₂ : IntermediateField F E) : Algebra ↥(K₁ ⊓ K₂) K₂ :=
  inferInstanceAs <| Algebra ↑(K₁.toSubalgebra ⊓ K₂.toSubalgebra) K₂.toSubalgebra
/-
**IntermediateField.sup_def** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：sup_def (S T : IntermediateField F E) : S ⊔ T = adjoin F (S union T : Set 
E)
参数：S T : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_def (S T : IntermediateField F E) : S ⊔ T = adjoin F (S ∪ T : Set E) := rfl
/-
**IntermediateField.sSup_def** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：sSup_def (S : Set (IntermediateField F E)) : sSup S = adjoin F (⋃₀ (SetLik
e.coe '' S))
参数：S : Set (IntermediateField F E)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sSup_def (S : Set (IntermediateField F E)) :
    sSup S = adjoin F (⋃₀ (SetLike.coe '' S)) := rfl
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (IntermediateField F E) :=
  ⟨⊤⟩
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (IntermediateField F F) :=
  { (inferInstance : Inhabited (IntermediateField F F)) with
    uniq := fun _ ↦ toSubalgebra_injective <| Subsingleton.elim _ _ }
/-
**IntermediateField.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：coe_bot : ↑(⊥ : IntermediateField F E) = Set.range (algebraMap F E)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ↑(⊥ : IntermediateField F E) = Set.range (algebraMap F E) := rfl
/-
**IntermediateField.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：mem_bot {x : E} : x in (⊥ : IntermediateField F E) ↔ x in Set.range (algeb
raMap F E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_bot {x : E} : x ∈ (⊥ : IntermediateField F E) ↔ x ∈ Set.range (algebraMap F E) :=
  Iff.rfl

@[simp]
/-
**IntermediateField.bot_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：bot_toSubalgebra : (⊥ : IntermediateField F E).toSubalgebra = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_toSubalgebra : (⊥ : IntermediateField F E).toSubalgebra = ⊥ := rfl
/-
**IntermediateField.bot_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：bot_toSubfield : (⊥ : IntermediateField F E).toSubfield = (algebraMap F E)
.fieldRange
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_toSubfield : (⊥ : IntermediateField F E).toSubfield = (algebraMap F E).fieldRange :=
  rfl

@[simp]
/-
**IntermediateField.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：coe_top : ↑(⊤ : IntermediateField F E) = (Set.univ : Set E)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ↑(⊤ : IntermediateField F E) = (Set.univ : Set E) :=
  rfl

@[simp]
/-
**IntermediateField.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：mem_top {x : E} : x in (⊤ : IntermediateField F E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem mem_top {x : E} : x ∈ (⊤ : IntermediateField F E) :=
  trivial

@[simp]
/-
**IntermediateField.top_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：top_toSubalgebra : (⊤ : IntermediateField F E).toSubalgebra = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_toSubalgebra : (⊤ : IntermediateField F E).toSubalgebra = ⊤ :=
  rfl

@[simp]
/-
**IntermediateField.top_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：top_toSubfield : (⊤ : IntermediateField F E).toSubfield = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_toSubfield : (⊤ : IntermediateField F E).toSubfield = ⊤ :=
  rfl

@[simp, norm_cast]
/-
**IntermediateField.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：coe_inf (S T : IntermediateField F E) : (↑(S ⊓ T) : Set E) = (S : Set E) i
nter T
参数：S T : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (S T : IntermediateField F E) : (↑(S ⊓ T) : Set E) = (S : Set E) ∩ T :=
  rfl

@[simp]
/-
**IntermediateField.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：mem_inf {S T : IntermediateField F E} {x : E} : x in S ⊓ T ↔ x in S ∧ x in
 T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf {S T : IntermediateField F E} {x : E} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

@[simp]
/-
**IntermediateField.inf_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：inf_toSubalgebra (S T : IntermediateField F E) : (S ⊓ T).toSubalgebra = S.
toSubalgebra ⊓ T.toSubalgebra
参数：S T : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_toSubalgebra (S T : IntermediateField F E) :
    (S ⊓ T).toSubalgebra = S.toSubalgebra ⊓ T.toSubalgebra :=
  rfl

@[simp]
/-
**IntermediateField.inf_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：inf_toSubfield (S T : IntermediateField F E) : (S ⊓ T).toSubfield = S.toSu
bfield ⊓ T.toSubfield
参数：S T : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_toSubfield (S T : IntermediateField F E) :
    (S ⊓ T).toSubfield = S.toSubfield ⊓ T.toSubfield :=
  rfl

@[simp]
/-
**IntermediateField.sup_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：sup_toSubfield (S T : IntermediateField F E) : (S ⊔ T).toSubfield = S.toSu
bfield ⊔ T.toSubfield
参数：S T : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subfield.closure_eq`：closure_eq (s : Subfield K) : closure (s : Set K) =
 s
· 使用定理 `Subfield.closure_union`：closure_union (s t : Set K) : closure (s union t
) = closure s ⊔ closure t
· 使用定理 `Set.union_eq_right`：union_eq_right {s t : Set α} : s union t = t ↔ s sub
seteq t
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `IntermediateField.algebraMap_mem`：algebraMap_mem (x : K) : algebraMap K 
L x in S
-/
theorem sup_toSubfield (S T : IntermediateField F E) :
    (S ⊔ T).toSubfield = S.toSubfield ⊔ T.toSubfield := by
  rw [← S.toSubfield.closure_eq, ← T.toSubfield.closure_eq, ← Subfield.closure_union]
  simp_rw [sup_def, adjoin_toSubfield, coe_toSubfield]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  exact Set.mem_union_left _ (algebraMap_mem S x)

@[simp, norm_cast]
/-
**IntermediateField.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：coe_sInf (S : Set (IntermediateField F E)) : (↑(sInf S) : Set E) = ⋂ s in 
S, ↑s
参数：S : Set (IntermediateField F E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_sInf (S : Set (IntermediateField F E)) : (↑(sInf S) : Set E) = ⋂ s ∈ S, ↑s :=
  show sInf ((fun (x : IntermediateField F E) => (x : Set E)) '' S) = ⋂ s ∈ S, ↑s by simp

@[simp, grind =]
/-
**IntermediateField.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：mem_sInf {S : Set (IntermediateField F E)} {x : E} : x in sInf S ↔ forall 
p in S, x in p
参数：IntermediateField F E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `IntermediateField.coe_sInf`：coe_sInf (S : Set (IntermediateField F E)) :
 (↑(sInf S) : Set E) = ⋂ s in S, ↑s
-/
theorem mem_sInf {S : Set (IntermediateField F E)} {x : E} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simpa only [Set.mem_iInter] using! Set.ext_iff.1 (coe_sInf S) x

@[simp]
/-
**IntermediateField.sInf_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：sInf_toSubalgebra (S : Set (IntermediateField F E)) : (sInf S).toSubalgebr
a = sInf (toSubalgebra '' S)
参数：S : Set (IntermediateField F E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.coe_sInf`：coe_sInf (S : Set (IntermediateField F E)) :
 (↑(sInf S) : Set E) = ⋂ s in S, ↑s
· 使用定理 `Algebra.coe_sInf`：coe_sInf (S : Set (Subalgebra R A)) : (↑(sInf S) : Set
 A) = ⋂ s in S, ↑s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biInter_and'`：biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iInter_iInter_eq_right`：iInter_iInter_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋂ (x) (h : b = x), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInf_toSubalgebra (S : Set (IntermediateField F E)) :
    (sInf S).toSubalgebra = sInf (toSubalgebra '' S) :=
  SetLike.coe_injective <| by simp

@[simp]
/-
**IntermediateField.sInf_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField
`。
形式化陈述：sInf_toSubfield (S : Set (IntermediateField F E)) : (sInf S).toSubfield = 
sInf (toSubfield '' S)
参数：S : Set (IntermediateField F E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.neg_mem`：∀ {K : Type u_1} {L : Type u_2} [inst : Field
 K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K L)   {x :
 L}, x ∈ S → -x…
· 使用定理 `IntermediateField.sInf_toSubalgebra`：sInf_toSubalgebra (S : Set (Interme
diateField F E)) : (sInf S).toSubalgebra = sInf (toSubalgebra '' S)
· 使用定理 `Algebra.sInf_toSubsemiring`：sInf_toSubsemiring (S : Set (Subalgebra R A)
) : (sInf S).toSubsemiring = sInf (Subalgebra.toSubsemiring '' S)
· 使用定理 `Subring.mk.congr_simp`：∀ {R : Type u} [inst : NonAssocRing R] (toSubsemi
ring toSubsemiring_1 : Subsemiring R)   (e_toSubsemiring : toSubsemiring = toSub
semiring_1)…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biInter_and'`：biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iInter_iInter_eq_right`：iInter_iInter_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋂ (x) (h : b = x), s x h = s b rfl
· 使用定理 `Subfield.coe_sInf`：coe_sInf (S : Set (Subfield K)) : ((sInf S : Subfield
 K) : Set K) = ⋂ s in S, ↑s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInf_toSubfield (S : Set (IntermediateField F E)) :
    (sInf S).toSubfield = sInf (toSubfield '' S) :=
  SetLike.coe_injective <| by simp

@[simp]
/-
**IntermediateField.sSup_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField
`。
形式化陈述：sSup_toSubfield (S : Set (IntermediateField F E)) (hS : S.Nonempty) : (sSu
p S).toSubfield = sSup (toSubfield '' S)
参数：S : Set (IntermediateField F E)；hS : S.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subfield.closure_eq`：closure_eq (s : Subfield K) : closure (s : Set K) =
 s
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `Subfield.closure_sUnion`：closure_sUnion (s : Set (Set K)) : closure (⋃₀ 
s) = ⨆ t in s, closure t
· 使用定理 `IntermediateField.sSup_def`：sSup_def (S : Set (IntermediateField F E)) :
 sSup S = adjoin F (⋃₀ (SetLike.coe '' S))
· 使用定理 `IntermediateField.adjoin_toSubfield`：adjoin_toSubfield : (adjoin F S).to
Subfield = Subfield.closure (Set.range (algebraMap F E) union S)
· 使用定理 `Set.union_eq_right`：union_eq_right {s t : Set α} : s union t = t ↔ s sub
seteq t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IntermediateField.algebraMap_mem`：algebraMap_mem (x : K) : algebraMap K 
L x in S
-/
theorem sSup_toSubfield (S : Set (IntermediateField F E)) (hS : S.Nonempty) :
    (sSup S).toSubfield = sSup (toSubfield '' S) := by
  have h : toSubfield '' S = Subfield.closure '' SetLike.coe '' S := by
    rw [Set.image_image]
    congr! with x
    exact x.toSubfield.closure_eq.symm
  rw [h, sSup_image, ← Subfield.closure_sUnion, sSup_def, adjoin_toSubfield]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hS
  simp only [Set.mem_sUnion, Set.mem_image, exists_exists_and_eq_and, SetLike.mem_coe]
  exact ⟨y, hy, algebraMap_mem y x⟩

@[simp, norm_cast]
/-
**IntermediateField.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：coe_iInf {ι : Sort*} (S : ι -> IntermediateField F E) : (↑(iInf S) : Set E
) = ⋂ i, S i
参数：S : ι -> IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.coe_sInf`：coe_sInf (S : Set (IntermediateField F E)) :
 (↑(sInf S) : Set E) = ⋂ s in S, ↑s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf {ι : Sort*} (S : ι → IntermediateField F E) : (↑(iInf S) : Set E) = ⋂ i, S i := by
  simp [iInf]

@[simp]
/-
**IntermediateField.iInf_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：iInf_toSubalgebra {ι : Sort*} (S : ι -> IntermediateField F E) : (iInf S).
toSubalgebra = ⨅ i, (S i).toSubalgebra
参数：S : ι -> IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.sInf_toSubalgebra`：sInf_toSubalgebra (S : Set (Interme
diateField F E)) : (sInf S).toSubalgebra = sInf (toSubalgebra '' S)
· 使用定理 `Algebra.coe_sInf`：coe_sInf (S : Set (Subalgebra R A)) : (↑(sInf S) : Set
 A) = ⋂ s in S, ↑s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iInf_toSubalgebra {ι : Sort*} (S : ι → IntermediateField F E) :
    (iInf S).toSubalgebra = ⨅ i, (S i).toSubalgebra :=
  SetLike.coe_injective <| by simp [iInf]

@[simp]
/-
**IntermediateField.iInf_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField
`。
形式化陈述：iInf_toSubfield {ι : Sort*} (S : ι -> IntermediateField F E) : (iInf S).to
Subfield = ⨅ i, (S i).toSubfield
参数：S : ι -> IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.sInf_toSubfield`：sInf_toSubfield (S : Set (Intermediat
eField F E)) : (sInf S).toSubfield = sInf (toSubfield '' S)
· 使用定理 `Subfield.coe_sInf`：coe_sInf (S : Set (Subfield K)) : ((sInf S : Subfield
 K) : Set K) = ⋂ s in S, ↑s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iInf_toSubfield {ι : Sort*} (S : ι → IntermediateField F E) :
    (iInf S).toSubfield = ⨅ i, (S i).toSubfield :=
  SetLike.coe_injective <| by simp [iInf]

@[simp]
/-
**IntermediateField.iSup_toSubfield** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField
`。
形式化陈述：iSup_toSubfield {ι : Sort*} [Nonempty ι] (S : ι -> IntermediateField F E) 
: (iSup S).toSubfield = ⨆ i, (S i).toSubfield
参数：S : ι -> IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.sSup_toSubfield`：sSup_toSubfield (S : Set (Intermediat
eField F E)) (hS : S.Nonempty) : (sSup S).toSubfield = sSup (toSubfield '' S)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_toSubfield {ι : Sort*} [Nonempty ι] (S : ι → IntermediateField F E) :
    (iSup S).toSubfield = ⨆ i, (S i).toSubfield := by
  simp only [iSup, Set.range_nonempty, sSup_toSubfield, ← Set.range_comp, Function.comp_def]

variable (F E)

/-- The bottom `IntermediateField` is isomorphic to the field. -/
/-
**IntermediateField.botEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：botEquiv : (⊥ : IntermediateField F E) ≃ₐ[F] F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.bot_toSubalgebra`：bot_toSubalgebra : (⊥ : Intermediate
Field F E).toSubalgebra = ⊥

--- 原说明 ---
The bottom `IntermediateField` is isomorphic to the field.
-/
noncomputable def botEquiv : (⊥ : IntermediateField F E) ≃ₐ[F] F :=
  (Subalgebra.equivOfEq _ _ bot_toSubalgebra).trans (Algebra.botEquiv F E)

variable {F E}
/-
**IntermediateField.botEquiv_def** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：botEquiv_def (x : F) : botEquiv F E (algebraMap F (⊥ : IntermediateField F
 E) x) = x
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem botEquiv_def (x : F) : botEquiv F E (algebraMap F (⊥ : IntermediateField F E) x) = x := by
  simp

@[simp]
/-
**IntermediateField.botEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：botEquiv_symm (x : F) : (botEquiv F E).symm x = algebraMap F _ x
参数：x : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem botEquiv_symm (x : F) : (botEquiv F E).symm x = algebraMap F _ x :=
  rfl
/-
**IntermediateField.algebraOverBot** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`
。
形式化陈述：algebraOverBot : Algebra (⊥ : IntermediateField F E) F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance algebraOverBot : Algebra (⊥ : IntermediateField F E) F :=
  (IntermediateField.botEquiv F E).toAlgHom.toRingHom.toAlgebra
/-
**IntermediateField.coe_algebraMap_over_bot** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField`。
形式化陈述：coe_algebraMap_over_bot : (algebraMap (⊥ : IntermediateField F E) F : (⊥ :
 IntermediateField F E) -> F) = IntermediateField.botEquiv F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
theorem coe_algebraMap_over_bot :
    (algebraMap (⊥ : IntermediateField F E) F : (⊥ : IntermediateField F E) → F) =
      IntermediateField.botEquiv F E :=
  rfl
/-
**IntermediateField.isScalarTower_over_bot** 是 Mathlib 中的一个实例，位于命名空间 `Intermedia
teField`。
形式化陈述：isScalarTower_over_bot : IsScalarTower (⊥ : IntermediateField F E) F E
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.coe_algebraMap_over_bot`：coe_algebraMap_over_bot : (al
gebraMap (⊥ : IntermediateField F E) F : (⊥ : IntermediateField F E) -> F) = Int
ermediateField.botEquiv F E
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `IntermediateField.botEquiv_symm`：botEquiv_symm (x : F) : (botEquiv F E).
symm x = algebraMap F _ x
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
-/
instance isScalarTower_over_bot : IsScalarTower (⊥ : IntermediateField F E) F E :=
  IsScalarTower.of_algebraMap_eq
    (by
      intro x
      obtain ⟨y, rfl⟩ := (botEquiv F E).symm.surjective x
      rw [coe_algebraMap_over_bot, (botEquiv F E).apply_symm_apply, botEquiv_symm,
        IsScalarTower.algebraMap_apply F (⊥ : IntermediateField F E) E])

/-- The top `IntermediateField` is isomorphic to the field.

This is the intermediate field version of `Subalgebra.topEquiv`. -/
@[simps!]
/-
**IntermediateField.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The top `IntermediateField` is isomorphic to the field.

This is the intermediate field version of `Subalgebra.topEquiv`.
-/
def topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E :=
  Subalgebra.topEquiv

section RestrictScalars

@[simp]
/-
**IntermediateField.restrictScalars_bot_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Inter
mediateField`。
形式化陈述：restrictScalars_bot_eq_self (K : IntermediateField F E) : (⊥ : Intermediat
eField K E).restrictScalars _ = K
参数：K : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem restrictScalars_bot_eq_self (K : IntermediateField F E) :
    (⊥ : IntermediateField K E).restrictScalars _ = K :=
  SetLike.coe_injective Subtype.range_coe

variable {K : Type*} [Field K] [Algebra K E] [Algebra K F] [IsScalarTower K F E]

@[simp]
/-
**IntermediateField.restrictScalars_top** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：restrictScalars_top : (⊤ : IntermediateField F E).restrictScalars K = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars_top : (⊤ : IntermediateField F E).restrictScalars K = ⊤ :=
  rfl

@[simp]
/-
**IntermediateField.restrictScalars_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField`。
形式化陈述：restrictScalars_eq_top_iff {L : IntermediateField F E} : L.restrictScalars
 K = ⊤ ↔ L = ⊤
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
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem restrictScalars_eq_top_iff {L : IntermediateField F E} :
    L.restrictScalars K = ⊤ ↔ L = ⊤ := by
  simp [SetLike.ext_iff]

variable (K)
variable (L L' : IntermediateField F E)
/-
**IntermediateField.restrictScalars_sup** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：restrictScalars_sup : L.restrictScalars K ⊔ L'.restrictScalars K = (L ⊔ L'
).restrictScalars K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.toSubfield_injective`：toSubfield_injective : Function.
Injective (toSubfield : IntermediateField K L -> _)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.sup_toSubfield`：sup_toSubfield (S T : IntermediateFiel
d F E) : (S ⊔ T).toSubfield = S.toSubfield ⊔ T.toSubfield
· 使用定理 `IntermediateField.restrictScalars_toSubfield`：restrictScalars_toSubfield
 {E : IntermediateField L' L} : (E.restrictScalars K).toSubfield = E.toSubfield
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrictScalars_sup :
    L.restrictScalars K ⊔ L'.restrictScalars K = (L ⊔ L').restrictScalars K :=
  toSubfield_injective (by simp)
/-
**IntermediateField.restrictScalars_inf** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：restrictScalars_inf : L.restrictScalars K ⊓ L'.restrictScalars K = (L ⊓ L'
).restrictScalars K
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars_inf :
    L.restrictScalars K ⊓ L'.restrictScalars K = (L ⊓ L').restrictScalars K := rfl

end RestrictScalars

variable {K : Type*} [Field K] [Algebra F K]

@[simp]
/-
**IntermediateField.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：map_bot (f : E ->ₐ[F] K) : IntermediateField.map f ⊥ = ⊥
参数：f : E ->ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.toSubalgebra_injective`：toSubalgebra_injective : Funct
ion.Injective (toSubalgebra : IntermediateField K L -> _)
· 使用定理 `Algebra.map_bot`：map_bot (f : A ->ₐ[R] B) : (⊥ : Subalgebra R A).map f =
 ⊥
-/
theorem map_bot (f : E →ₐ[F] K) :
    IntermediateField.map f ⊥ = ⊥ :=
  toSubalgebra_injective <| Algebra.map_bot _
/-
**IntermediateField.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：map_sup (s t : IntermediateField F E) (f : E ->ₐ[F] K) : (s ⊔ t).map f = s
.map f ⊔ t.map f
参数：s t : IntermediateField F E；f : E ->ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `IntermediateField.gc_map_comap`：gc_map_comap (f : L ->ₐ[K] L') : GaloisC
onnection (map f) (comap f)
-/
theorem map_sup (s t : IntermediateField F E) (f : E →ₐ[F] K) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup
/-
**IntermediateField.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：map_iSup {ι : Sort*} (f : E ->ₐ[F] K) (s : ι -> IntermediateField F E) : (
iSup s).map f = ⨆ i, (s i).map f
参数：f : E ->ₐ[F] K；s : ι -> IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `IntermediateField.gc_map_comap`：gc_map_comap (f : L ->ₐ[K] L') : GaloisC
onnection (map f) (comap f)
-/
theorem map_iSup {ι : Sort*} (f : E →ₐ[F] K) (s : ι → IntermediateField F E) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup
/-
**IntermediateField.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：map_inf (s t : IntermediateField F E) (f : E ->ₐ[F] K) : (s ⊓ t).map f = s
.map f ⊓ t.map f
参数：s t : IntermediateField F E；f : E ->ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem map_inf (s t : IntermediateField F E) (f : E →ₐ[F] K) :
    (s ⊓ t).map f = s.map f ⊓ t.map f := SetLike.coe_injective (Set.image_inter f.injective)
/-
**IntermediateField.map_iInf** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：map_iInf {ι : Sort*} [Nonempty ι] (f : E ->ₐ[F] K) (s : ι -> IntermediateF
ield F E) : (iInf s).map f = ⨅ i, (s i).map f
参数：f : E ->ₐ[F] K；s : ι -> IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.coe_iInf`：coe_iInf {ι : Sort*} (S : ι -> IntermediateF
ield F E) : (↑(iInf S) : Set E) = ⋂ i, S i
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : E →ₐ[F] K) (s : ι → IntermediateField F E) :
    (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective f.injective).image_iInter_eq (s := SetLike.coe ∘ s)
/-
**IntermediateField._root_.AlgHom.fieldRange_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `I
ntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgHom.fieldRange_eq_map (f : E →ₐ[F] K) :
    f.fieldRange = IntermediateField.map f ⊤ :=
  SetLike.ext' Set.image_univ.symm
/-
**IntermediateField._root_.AlgHom.map_fieldRange** 是 Mathlib 中的一个定理，位于命名空间 `Inte
rmediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgHom.map_fieldRange {L : Type*} [Field L] [Algebra F L]
    (f : E →ₐ[F] K) (g : K →ₐ[F] L) : f.fieldRange.map g = (g.comp f).fieldRange :=
  SetLike.ext' (Set.range_comp g f).symm
/-
**IntermediateField._root_.AlgHom.fieldRange_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `I
ntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgHom.fieldRange_eq_top {f : E →ₐ[F] K} :
    f.fieldRange = ⊤ ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans Set.range_eq_univ

@[simp]
/-
**IntermediateField._root_.AlgEquiv.fieldRange_eq_top** 是 Mathlib 中的一个定理，位于命名空间 
`IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgEquiv.fieldRange_eq_top (f : E ≃ₐ[F] K) :
    (f : E →ₐ[F] K).fieldRange = ⊤ :=
  AlgHom.fieldRange_eq_top.mpr f.surjective

end Lattice

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E)

/-
**IntermediateField.adjoin_eq_range_algebraMap_adjoin** 是 Mathlib 中的一个定理，位于命名空间 
`IntermediateField`。
形式化陈述：adjoin_eq_range_algebraMap_adjoin : (adjoin F S : Set E) = Set.range (alge
braMap (adjoin F S) E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem adjoin_eq_range_algebraMap_adjoin :
    (adjoin F S : Set E) = Set.range (algebraMap (adjoin F S) E) :=
  Subtype.range_coe.symm
/-
**IntermediateField.adjoin.algebraMap_mem** 是 Mathlib 中的一个定理，位于命名空间 `Intermediat
eField.adjoin`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E] (S : Set E) (x : F),   (algebraMap F E) x ∈ IntermediateField.a
djoin F S
参数：F : Type u_1；S : Set E；x : F；algebraMap F E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.algebraMap_mem`：algebraMap_mem (x : K) : algebraMap K 
L x in S
-/
theorem adjoin.algebraMap_mem (x : F) : algebraMap F E x ∈ adjoin F S :=
  IntermediateField.algebraMap_mem (adjoin F S) x
/-
**IntermediateField.adjoin.range_algebraMap_subset** 是 Mathlib 中的一个定理，位于命名空间 `In
termediateField.adjoin`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E] (S : Set E),   Set.range ⇑(algebraMap F E) ⊆ ↑(IntermediateFiel
d.adjoin F S)
参数：F : Type u_1；S : Set E；algebraMap F E；IntermediateField.adjoin F S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.set_range_subset`：set_range_subset : Set.range (algebr
aMap K L) subseteq S
-/
theorem adjoin.range_algebraMap_subset : Set.range (algebraMap F E) ⊆ adjoin F S :=
  set_range_subset (adjoin F S)
/-
**IntermediateField.adjoin.fieldCoe** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField
.adjoin`。
形式化陈述：(F : Type u_1) →   [inst : Field F] →     {E : Type u_2} → [inst_1 : Field
 E] → [inst_2 : Algebra F E] → (S : Set E) → CoeTC F ↥(IntermediateField.adjoin 
F S)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin.algebraMap_mem`：∀ (F : Type u_1) [inst : Field 
F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (S : Set E) (x : F),
   (algebraMap F E) x ∈ Inter…
-/
instance adjoin.fieldCoe : CoeTC F (adjoin F S) where
  coe x := ⟨algebraMap F E x, adjoin.algebraMap_mem F S x⟩

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/-
**IntermediateField.subset_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：subset_adjoin : S subseteq adjoin F S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.subset_closure`：subset_closure {s : Set K} : s subseteq closure
 s
-/
theorem subset_adjoin : S ⊆ adjoin F S := fun _ hx => Subfield.subset_closure (Or.inr hx)

@[aesop 80% (rule_sets := [SetLike])]
/-
**IntermediateField.mem_adjoin_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：mem_adjoin_of_mem {S : Set E} {s : E} (hs : s in S) : s in adjoin F S
参数：hs : s in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
-/
theorem mem_adjoin_of_mem {S : Set E} {s : E} (hs : s ∈ S) : s ∈ adjoin F S := subset_adjoin F S hs
/-
**IntermediateField.notMem_of_notMem_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField`。
形式化陈述：notMem_of_notMem_adjoin {S : Set E} {s : E} (hs : s ∉ adjoin F S) : s ∉ S
参数：hs : s ∉ adjoin F S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.mem_adjoin_of_mem`：mem_adjoin_of_mem {S : Set E} {s : 
E} (hs : s in S) : s in adjoin F S
-/
theorem notMem_of_notMem_adjoin {S : Set E} {s : E} (hs : s ∉ adjoin F S) : s ∉ S := fun h =>
  hs <| mem_adjoin_of_mem F h
/-
**IntermediateField.adjoin.setCoe** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField.a
djoin`。
形式化陈述：(F : Type u_1) →   [inst : Field F] →     {E : Type u_2} →       [inst_1 :
 Field E] → [inst_2 : Algebra F E] → (S : Set E) → CoeTC ↑S ↥(IntermediateField.
adjoin F S)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance adjoin.setCoe : CoeTC S (adjoin F S) where coe x := ⟨x, subset_adjoin F S (Subtype.mem x)⟩

@[mono, gcongr]
/-
**IntermediateField.adjoin.mono** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.adj
oin`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E] (S T : Set E),   S ⊆ T → IntermediateField.adjoin F S ≤ Interme
diateField.adjoin F T
参数：F : Type u_1；S T : Set E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `IntermediateField.gc`：gc : GaloisConnection (adjoin F : Set E -> Interme
diateField F E) (fun (x : IntermediateField F E) => (x : Set E))
-/
theorem adjoin.mono (T : Set E) (h : S ⊆ T) : adjoin F S ≤ adjoin F T :=
  GaloisConnection.monotone_l gc h
/-
**IntermediateField.adjoin_contains_field_as_subfield** 是 Mathlib 中的一个定理，位于命名空间 
`IntermediateField`。
形式化陈述：adjoin_contains_field_as_subfield (F : Subfield E) : (F : Set E) subseteq 
adjoin F S
参数：F : Subfield E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin.algebraMap_mem`：∀ (F : Type u_1) [inst : Field 
F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (S : Set E) (x : F),
   (algebraMap F E) x ∈ Inter…
-/
theorem adjoin_contains_field_as_subfield (F : Subfield E) : (F : Set E) ⊆ adjoin F S := fun x hx =>
  adjoin.algebraMap_mem F S ⟨x, hx⟩
/-
**IntermediateField.subset_adjoin_of_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Inte
rmediateField`。
形式化陈述：subset_adjoin_of_subset_left {F : Subfield E} {T : Set E} (HT : T subseteq
 F) : T subseteq adjoin F S
参数：HT : T subseteq F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.algebraMap_mem`：algebraMap_mem (x : K) : algebraMap K 
L x in S
-/
theorem subset_adjoin_of_subset_left {F : Subfield E} {T : Set E} (HT : T ⊆ F) : T ⊆ adjoin F S :=
  fun x hx => (adjoin F S).algebraMap_mem ⟨x, HT hx⟩
/-
**IntermediateField.subset_adjoin_of_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Int
ermediateField`。
形式化陈述：subset_adjoin_of_subset_right {T : Set E} (H : T subseteq S) : T subseteq 
adjoin F S
参数：H : T subseteq S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
-/
theorem subset_adjoin_of_subset_right {T : Set E} (H : T ⊆ S) : T ⊆ adjoin F S := fun _ hx =>
  subset_adjoin F S (H hx)

@[simp]
/-
**IntermediateField.adjoin_empty** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_empty (F E : Type*) [Field F] [Field E] [Algebra F E] : adjoin F (∅
 : Set E) = ⊥
参数：F E : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
theorem adjoin_empty (F E : Type*) [Field F] [Field E] [Algebra F E] : adjoin F (∅ : Set E) = ⊥ :=
  eq_bot_iff.mpr (adjoin_le_iff.mpr (Set.empty_subset _))

@[simp]
/-
**IntermediateField.adjoin_univ** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_univ (F E : Type*) [Field F] [Field E] [Algebra F E] : adjoin F (Se
t.univ : Set E) = ⊤
参数：F E : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
-/
theorem adjoin_univ (F E : Type*) [Field F] [Field E] [Algebra F E] :
    adjoin F (Set.univ : Set E) = ⊤ :=
  eq_top_iff.mpr <| subset_adjoin _ _
/-
**IntermediateField.adjoin_union** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_union {S T : Set E} : adjoin F (S union T) = adjoin F S ⊔ adjoin F 
T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `IntermediateField.gc`：gc : GaloisConnection (adjoin F : Set E -> Interme
diateField F E) (fun (x : IntermediateField F E) => (x : Set E))
-/
theorem adjoin_union {S T : Set E} : adjoin F (S ∪ T) = adjoin F S ⊔ adjoin F T :=
  gc.l_sup

/-- If `K` is a field with `F ⊆ K` and `S ⊆ K` then `adjoin F S ≤ K`. -/
/-
**IntermediateField.adjoin_le_subfield** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：adjoin_le_subfield {K : Subfield E} (HF : Set.range (algebraMap F E) subse
teq K) (HS : S subseteq K) : (adjoin F S).toSubfield <= K
参数：HF : Set.range (algebraMap F E) subseteq K；HS : S subseteq K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
If `K` is a field with `F ⊆ K` and `S ⊆ K` then `adjoin F S ≤ K`.
-/
theorem adjoin_le_subfield {K : Subfield E} (HF : Set.range (algebraMap F E) ⊆ K) (HS : S ⊆ K) :
    (adjoin F S).toSubfield ≤ K := by
  simpa using ⟨HF, HS⟩
/-
**IntermediateField.adjoin_subset_adjoin_iff** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField`。
形式化陈述：adjoin_subset_adjoin_iff {F' : Type*} [Field F'] [Algebra F' E] {S S' : Se
t E} : (adjoin F S : Set E) subseteq adjoin F' S' ↔ Set.range (algebraMap F E) s
ubseteq adjoin F' S' ∧ S subseteq adjoin F' S'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IntermediateField.adjoin.range_algebraMap_subset`：∀ (F : Type u_1) [inst
 : Field F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (S : Set E)
,   Set.range ⇑(algebraMap F E) ⊆ ↑(In…
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subfield.closure_le`：closure_le {s : Set K} {t : Subfield K} : closure s
 <= t ↔ s subseteq t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
-/
theorem adjoin_subset_adjoin_iff {F' : Type*} [Field F'] [Algebra F' E] {S S' : Set E} :
    (adjoin F S : Set E) ⊆ adjoin F' S' ↔
      Set.range (algebraMap F E) ⊆ adjoin F' S' ∧ S ⊆ adjoin F' S' :=
  ⟨fun h => ⟨(adjoin.range_algebraMap_subset _ _).trans h,
    (subset_adjoin _ _).trans h⟩, fun ⟨hF, hS⟩ =>
      (Subfield.closure_le (t := (adjoin F' S').toSubfield)).mpr (Set.union_subset hF hS)⟩

/-- Adjoining S and then T is the same as adjoining `S ∪ T`. -/
/-
**IntermediateField.adjoin_adjoin_left** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：adjoin_adjoin_left (T : Set E) : (adjoin (adjoin F S) T).restrictScalars _
 = adjoin F (S union T)
参数：T : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `IntermediateField.adjoin_subset_adjoin_iff`：adjoin_subset_adjoin_iff {F'
 : Type*} [Field F'] [Algebra F' E] {S S' : Set E} : (adjoin F S : Set E) subset
eq adjoin F' S' ↔ Set.range (alg…
· 使用定理 `IntermediateField.adjoin.mono`：∀ (F : Type u_1) [inst : Field F] {E : Ty
pe u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (S T : Set E),   S ⊆ T → Inter
mediateField.adjoin…
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `IntermediateField.subset_adjoin_of_subset_right`：subset_adjoin_of_subset
_right {T : Set E} (H : T subseteq S) : T subseteq adjoin F S
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Subfield.subset_closure`：subset_closure {s : Set K} : s subseteq closure
 s
· 使用定理 `IntermediateField.adjoin.algebraMap_mem`：∀ (F : Type u_1) [inst : Field 
F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (S : Set E) (x : F),
   (algebraMap F E) x ∈ Inter…
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r

--- 原说明 ---
Adjoining S and then T is the same as adjoining `S ∪ T`.
-/
theorem adjoin_adjoin_left (T : Set E) :
    (adjoin (adjoin F S) T).restrictScalars _ = adjoin F (S ∪ T) := by
  rw [SetLike.ext'_iff]
  change (adjoin (adjoin F S) T : Set E) = _
  apply subset_antisymm <;> rw [adjoin_subset_adjoin_iff] <;> constructor
  · rintro _ ⟨⟨x, hx⟩, rfl⟩; exact adjoin.mono _ _ _ Set.subset_union_left hx
  · exact subset_adjoin_of_subset_right _ _ Set.subset_union_right
  · exact Set.range_subset_iff.mpr fun f ↦ Subfield.subset_closure (.inl ⟨f, rfl⟩)
  · exact Set.union_subset
      (fun x hx ↦ Subfield.subset_closure <| .inl ⟨⟨x, Subfield.subset_closure (.inr hx)⟩, rfl⟩)
      (fun x hx ↦ Subfield.subset_closure <| .inr hx)

/-- Adjoining is idempotent: adjoining an adjoin is the same as a single adjoin. -/
@[simp]
/-
**IntermediateField.adjoin_adjoin_right** 是 Mathlib 中的一个引理，位于命名空间 `IntermediateF
ield`。
形式化陈述：adjoin_adjoin_right {K : Type*} [Field K] [Algebra K F] [Algebra K E] [IsS
calarTower K F E] : adjoin F (adjoin K S) = adjoin F S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.coe_restrictScalars`：coe_restrictScalars {E : Intermed
iateField L' L} : (restrictScalars K E : Set L) = (E : Set L)
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IntermediateField.adjoin.mono`：∀ (F : Type u_1) [inst : Field F] {E : Ty
pe u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (S T : Set E),   S ⊆ T → Inter
mediateField.adjoin…
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S

--- 原说明 ---
Adjoining is idempotent: adjoining an adjoin is the same as a single adjoin.
-/
lemma adjoin_adjoin_right {K : Type*} [Field K] [Algebra K F] [Algebra K E] [IsScalarTower K F E] :
    adjoin F (adjoin K S) = adjoin F S := by
  refine le_antisymm ?_ (adjoin.mono F S (adjoin K S) (subset_adjoin K S))
  rw [adjoin_le_iff, ← (adjoin F S).coe_restrictScalars K, SetLike.coe_subset_coe]
  simp

@[simp]
/-
**IntermediateField.adjoin_insert_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：adjoin_insert_adjoin (x : E) : adjoin F (insert x (adjoin F S : Set E)) = 
adjoin F (insert x S)
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.adjoin_union`：adjoin_union {S T : Set E} : adjoin F (S
 union T) = adjoin F S ⊔ adjoin F T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `IntermediateField.adjoin_adjoin_right`：adjoin_adjoin_right {K : Type*} [
Field K] [Algebra K F] [Algebra K E] [IsScalarTower K F E] : adjoin F (adjoin K 
S) = adjoin F S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjoin_insert_adjoin (x : E) :
    adjoin F (insert x (adjoin F S : Set E)) = adjoin F (insert x S) := by
  simp_rw [← Set.singleton_union, adjoin_union, adjoin_adjoin_right]

/-- `F[S][T] = F[T][S]` -/
/-
**IntermediateField.adjoin_adjoin_comm** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：adjoin_adjoin_comm (T : Set E) : (adjoin (adjoin F S) T).restrictScalars F
 = (adjoin (adjoin F T) S).restrictScalars F
参数：T : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.adjoin_adjoin_left`：adjoin_adjoin_left (T : Set E) : (
adjoin (adjoin F S) T).restrictScalars _ = adjoin F (S union T)
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a

--- 原说明 ---
`F[S][T] = F[T][S]`
-/
theorem adjoin_adjoin_comm (T : Set E) :
    (adjoin (adjoin F S) T).restrictScalars F = (adjoin (adjoin F T) S).restrictScalars F := by
  rw [adjoin_adjoin_left, adjoin_adjoin_left, Set.union_comm]
/-
**IntermediateField.adjoin_map** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_map {E' : Type*} [Field E'] [Algebra F E'] (f : E ->ₐ[F] E') : (adj
oin F S).map f = adjoin F (f '' S)
参数：f : E ->ₐ[F] E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.map_le_iff_le_comap`：map_le_iff_le_comap {f : L ->ₐ[K]
 L'} {s : IntermediateField K L} {t : IntermediateField K L'} : s.map f <= t ↔ s
 <= t.comap f
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用引理 `Set.monotone_image`：monotone_image : Monotone (image f)
-/
theorem adjoin_map {E' : Type*} [Field E'] [Algebra F E'] (f : E →ₐ[F] E') :
    (adjoin F S).map f = adjoin F (f '' S) :=
  le_antisymm
    (map_le_iff_le_comap.mpr <| adjoin_le_iff.mpr fun x hx ↦ subset_adjoin _ _ ⟨x, hx, rfl⟩)
    (adjoin_le_iff.mpr <| Set.monotone_image <| subset_adjoin _ _)

@[simp]
/-
**IntermediateField.lift_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：lift_adjoin (K : IntermediateField F E) (S : Set K) : lift (adjoin F S) = 
adjoin F (Subtype.val '' S)
参数：K : IntermediateField F E；S : Set K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_map`：adjoin_map {E' : Type*} [Field E'] [Algebr
a F E'] (f : E ->ₐ[F] E') : (adjoin F S).map f = adjoin F (f '' S)
-/
theorem lift_adjoin (K : IntermediateField F E) (S : Set K) :
    lift (adjoin F S) = adjoin F (Subtype.val '' S) :=
  adjoin_map _ _ _
/-
**IntermediateField.lift_adjoin_simple** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：lift_adjoin_simple (K : IntermediateField F E) (α : K) : lift (adjoin F {α
}) = adjoin F {α.1}
参数：K : IntermediateField F E；α : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.lift_adjoin`：lift_adjoin (K : IntermediateField F E) (
S : Set K) : lift (adjoin F S) = adjoin F (Subtype.val '' S)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_adjoin_simple (K : IntermediateField F E) (α : K) :
    lift (adjoin F {α}) = adjoin F {α.1} := by
  simp only [lift_adjoin, Set.image_singleton]

@[simp]
/-
**IntermediateField.lift_bot** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：lift_bot (K : IntermediateField F E) : lift (F
参数：K : IntermediateField F E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.map_bot`：map_bot (f : E ->ₐ[F] K) : IntermediateField.
map f ⊥ = ⊥
-/
theorem lift_bot (K : IntermediateField F E) :
    lift (F := K) ⊥ = ⊥ := map_bot _

@[simp]
/-
**IntermediateField.lift_top** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：lift_top (K : IntermediateField F E) : lift (F
参数：K : IntermediateField F E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.lift.eq_1`：∀ {K : Type u_1} {L : Type u_2} [inst : Fie
ld K] [inst_1 : Field L] [inst_2 : Algebra K L] {F : IntermediateField K L}   (E
 : IntermediateFi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.fieldRange_eq_map`：∀ {F : Type u_1} [inst : Field F] {E : Type u_
2} [inst_1 : Field E] [inst_2 : Algebra F E] {K : Type u_3}   [inst_3 : Field K]
 [inst_4 : Alg…
· 使用定理 `IntermediateField.fieldRange_val`：fieldRange_val : S.val.fieldRange = S
-/
theorem lift_top (K : IntermediateField F E) :
    lift (F := K) ⊤ = K := by rw [lift, ← AlgHom.fieldRange_eq_map, fieldRange_val]
/-
**IntermediateField.lift_sup** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：lift_sup (K : IntermediateField F E) (L L' : IntermediateField F K) : lift
 (L ⊔ L') = lift L ⊔ lift L'
参数：K : IntermediateField F E；L L' : IntermediateField F K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.map_sup`：map_sup (s t : IntermediateField F E) (f : E 
->ₐ[F] K) : (s ⊔ t).map f = s.map f ⊔ t.map f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_sup (K : IntermediateField F E) (L L' : IntermediateField F K) :
    lift (L ⊔ L') = lift L ⊔ lift L' := by
  simp [lift, map_sup]
/-
**IntermediateField.lift_inf** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：lift_inf (K : IntermediateField F E) (L L' : IntermediateField F K) : lift
 (L ⊓ L') = lift L ⊓ lift L'
参数：K : IntermediateField F E；L L' : IntermediateField F K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.map_inf`：map_inf (s t : IntermediateField F E) (f : E 
->ₐ[F] K) : (s ⊓ t).map f = s.map f ⊓ t.map f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_inf (K : IntermediateField F E) (L L' : IntermediateField F K) :
    lift (L ⊓ L') = lift L ⊓ lift L' := by
  simp [lift, map_inf]

@[simp]
/-
**IntermediateField.adjoin_self** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_self (K : IntermediateField F E) : adjoin F K = K
参数：K : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
-/
theorem adjoin_self (K : IntermediateField F E) :
    adjoin F K = K := le_antisymm (adjoin_le_iff.2 fun _ ↦ id) (subset_adjoin F _)
/-
**IntermediateField.restrictScalars_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Intermedia
teField`。
形式化陈述：restrictScalars_adjoin (K : IntermediateField F E) (S : Set E) : restrictS
calars F (adjoin K S) = adjoin F (K union S)
参数：K : IntermediateField F E；S : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin_self`：adjoin_self (K : IntermediateField F E) :
 adjoin F K = K
· 使用定理 `IntermediateField.adjoin_adjoin_left`：adjoin_adjoin_left (T : Set E) : (
adjoin (adjoin F S) T).restrictScalars _ = adjoin F (S union T)
-/
theorem restrictScalars_adjoin (K : IntermediateField F E) (S : Set E) :
    restrictScalars F (adjoin K S) = adjoin F (K ∪ S) := by
  rw [← adjoin_self _ K, adjoin_adjoin_left, adjoin_self _ K]

variable {F} in
/-
**IntermediateField.extendScalars_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：extendScalars_adjoin {K : IntermediateField F E} {S : Set E} (h : K <= adj
oin F S) : extendScalars h = adjoin K S
参数：h : K <= adjoin F S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.restrictScalars_injective`：restrictScalars_injective :
 Function.Injective (restrictScalars K : IntermediateField L' L -> IntermediateF
ield K L)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.extendScalars_restrictScalars`：extendScalars_restrictS
calars : (extendScalars h).restrictScalars K = E
· 使用定理 `IntermediateField.restrictScalars_adjoin`：restrictScalars_adjoin (K : In
termediateField F E) (S : Set E) : restrictScalars F (adjoin K S) = adjoin F (K 
union S)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IntermediateField.adjoin.mono`：∀ (F : Type u_1) [inst : Field F] {E : Ty
pe u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (S T : Set E),   S ⊆ T → Inter
mediateField.adjoin…
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
-/
theorem extendScalars_adjoin {K : IntermediateField F E} {S : Set E} (h : K ≤ adjoin F S) :
    extendScalars h = adjoin K S := restrictScalars_injective F <| by
  rw [extendScalars_restrictScalars, restrictScalars_adjoin]
  exact le_antisymm (adjoin.mono F S _ Set.subset_union_right) <| adjoin_le_iff.2 <|
    Set.union_subset h (subset_adjoin F S)
/-
**IntermediateField.restrictScalars_adjoin_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `Int
ermediateField`。
形式化陈述：restrictScalars_adjoin_eq_sup (K : IntermediateField F E) (S : Set E) : re
strictScalars F (adjoin K S) = K ⊔ adjoin F S
参数：K : IntermediateField F E；S : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.restrictScalars_adjoin`：restrictScalars_adjoin (K : In
termediateField F E) (S : Set E) : restrictScalars F (adjoin K S) = adjoin F (K 
union S)
· 使用定理 `IntermediateField.adjoin_union`：adjoin_union {S T : Set E} : adjoin F (S
 union T) = adjoin F S ⊔ adjoin F T
· 使用定理 `IntermediateField.adjoin_self`：adjoin_self (K : IntermediateField F E) :
 adjoin F K = K
-/
theorem restrictScalars_adjoin_eq_sup (K : IntermediateField F E) (S : Set E) :
    restrictScalars F (adjoin K S) = K ⊔ adjoin F S := by
  rw [restrictScalars_adjoin, adjoin_union, adjoin_self]
/-
**IntermediateField.adjoin_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_iUnion {ι} (f : ι -> Set E) : adjoin F (⋃ i, f i) = ⨆ i, adjoin F (
f i)
参数：f : ι -> Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `IntermediateField.gc`：gc : GaloisConnection (adjoin F : Set E -> Interme
diateField F E) (fun (x : IntermediateField F E) => (x : Set E))
-/
theorem adjoin_iUnion {ι} (f : ι → Set E) : adjoin F (⋃ i, f i) = ⨆ i, adjoin F (f i) :=
  gc.l_iSup
/-
**IntermediateField.iSup_eq_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：iSup_eq_adjoin {ι} (f : ι -> IntermediateField F E) : ⨆ i, f i = adjoin F 
(⋃ i, f i : Set E)
参数：f : ι -> IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.adjoin_iUnion`：adjoin_iUnion {ι} (f : ι -> Set E) : ad
join F (⋃ i, f i) = ⨆ i, adjoin F (f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IntermediateField.adjoin_self`：adjoin_self (K : IntermediateField F E) :
 adjoin F K = K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_eq_adjoin {ι} (f : ι → IntermediateField F E) :
    ⨆ i, f i = adjoin F (⋃ i, f i : Set E) := by
  simp_rw [adjoin_iUnion, adjoin_self]

variable {F} in
/-- If `E / L / F` and `E / L' / F` are two field extension towers, `L ≃ₐ[F] L'` is an isomorphism
compatible with `E / L` and `E / L'`, then for any subset `S` of `E`, `L(S)` and `L'(S)` are
equal as intermediate fields of `E / F`. -/
/-
**IntermediateField.restrictScalars_adjoin_of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间
 `IntermediateField`。
形式化陈述：restrictScalars_adjoin_of_algEquiv {L L' : Type*} [Field L] [Field L'] [Al
gebra F L] [Algebra L E] [Algebra F L'] [Algebra L' E] [IsScalarTower F L E] [Is
ScalarTower F L' E] (i : L ≃ₐ[F] L') (hi : algebraMap L E = (algebraMap L' E) ∘ 
i) (S : Set E) : (adjoin L S).restrictScalars F = (adjoin L' S).restrictScalars 
F
参数：i : L ≃ₐ[F] L'；hi : algebraMap L E = (algebraMap L' E) ∘ i；S : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IntermediateField.restrictScalars_toSubfield`：restrictScalars_toSubfield
 {E : IntermediateField L' L} : (E.restrictScalars K).toSubfield = E.toSubfield
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EquivLike.range_comp`：∀ {ι : Sort u_1} {ι' : Sort u_2} {E : Type u_3} [i
nst : EquivLike E ι ι'] {α : Type u_4} (f : ι' → α) (e : E),   Set.range (f ∘ ⇑e
) = Set.ra…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `E / L / F` and `E / L' / F` are two field extension towers, `L ≃ₐ[F] L'` is 
an isomorphism
compatible with `E / L` and `E / L'`, then for any subset `S` of `E`, `L(S)` and
 `L'(S)` are
equal as intermediate fields of `E / F`.
-/
theorem restrictScalars_adjoin_of_algEquiv
    {L L' : Type*} [Field L] [Field L']
    [Algebra F L] [Algebra L E] [Algebra F L'] [Algebra L' E]
    [IsScalarTower F L E] [IsScalarTower F L' E] (i : L ≃ₐ[F] L')
    (hi : algebraMap L E = (algebraMap L' E) ∘ i) (S : Set E) :
    (adjoin L S).restrictScalars F = (adjoin L' S).restrictScalars F := by
  apply_fun toSubfield using (fun K K' h ↦ by
    ext x; change x ∈ K.toSubfield ↔ x ∈ K'.toSubfield; rw [h])
  simp [hi]

@[elab_as_elim]
/-
**IntermediateField.adjoin_induction** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：adjoin_induction {s : Set E} {p : forall x in adjoin F s, Prop} (mem : for
all x hx, p x (subset_adjoin _ _ hx)) (algebraMap : forall x, p (algebraMap F E 
x) (algebraMap_mem _ _)) (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) 
(add_mem hx hy)) (inv : forall x hx, p x hx -> p x⁻¹ (inv_mem hx)) (mul : forall
 x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)) {x} (h : x in adjoin 
F s) : p x h
参数：mem : forall x hx, p x (subset_adjoin _ _ hx)；algebraMap : forall x, p (algeb
raMap F E x) (algebraMap_mem _ _)；add : forall x y hx hy, p x hx -> p y hy -> p 
(x + y) (add_mem hx hy)；inv : forall x hx, p x hx -> p x⁻¹ (inv_mem hx)；mul : fo
rall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)；h : x in adjoin F 
s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `IntermediateField.algebraMap_mem`：algebraMap_mem (x : K) : algebraMap K 
L x in S
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubfieldClass.toInvMemClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Div
isionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   InvMemClass S 
K
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subfield.closure_induction`：closure_induction {s : Set K} {p : forall x 
in closure s, Prop} (mem : forall x hx, p x (subset_closure hx)) (one : p 1 (one
_mem _)) (add : …
· 使用定理 `Subfield.subset_closure`：subset_closure {s : Set K} : s subseteq closure
 s
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
theorem adjoin_induction {s : Set E} {p : ∀ x ∈ adjoin F s, Prop}
    (mem : ∀ x hx, p x (subset_adjoin _ _ hx))
    (algebraMap : ∀ x, p (algebraMap F E x) (algebraMap_mem _ _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (inv : ∀ x hx, p x hx → p x⁻¹ (inv_mem hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (h : x ∈ adjoin F s) : p x h :=
  Subfield.closure_induction
    (fun x hx ↦ Or.casesOn hx (fun ⟨x, hx⟩ ↦ hx ▸ algebraMap x) (mem x))
    (by simp_rw [← (Algebra.algebraMap F E).map_one]; exact algebraMap 1) add
    (fun x _ h ↦ by
      simp_rw [← neg_one_smul F x, Algebra.smul_def]; exact mul _ _ _ _ (algebraMap _) h) inv mul h

section

variable {K : Type*} [Semiring K] [Algebra F K]

/-
**IntermediateField.adjoin_algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：adjoin_algHom_ext {s : Set E} ⦃φ₁ φ₂ : adjoin F s ->ₐ[F] K⦄ (h : forall x 
hx, φ₁ ⟨x, subset_adjoin _ _ hx⟩ = φ₂ ⟨x, subset_adjoin _ _ hx⟩) : φ₁ = φ₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IntermediateField.adjoin_induction`：adjoin_induction {s : Set E} {p : fo
rall x in adjoin F s, Prop} (mem : forall x hx, p x (subset_adjoin _ _ hx)) (alg
ebraMap : forall x, p (a…
· 使用定理 `IntermediateField.algebraMap_mem`：algebraMap_mem (x : K) : algebraMap K 
L x in S
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `eq_on_inv₀`：eq_on_inv₀ [MonoidWithZeroHomClass F' G₀ M₀'] (f g : F') (h 
: f a = g a) : f a⁻¹ = g a⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
-/
theorem adjoin_algHom_ext {s : Set E} ⦃φ₁ φ₂ : adjoin F s →ₐ[F] K⦄
    (h : ∀ x hx, φ₁ ⟨x, subset_adjoin _ _ hx⟩ = φ₂ ⟨x, subset_adjoin _ _ hx⟩) :
    φ₁ = φ₂ :=
  AlgHom.ext fun ⟨x, hx⟩ ↦ adjoin_induction _ h (fun _ ↦ φ₂.commutes _ ▸ φ₁.commutes _)
    (fun _ _ _ _ h₁ h₂ ↦ by convert! congr_arg₂ (· + ·) h₁ h₂ <;> rw [← map_add] <;> rfl)
    (fun _ _ ↦ eq_on_inv₀ _ _)
    (fun _ _ _ _ h₁ h₂ ↦ by convert! congr_arg₂ (· * ·) h₁ h₂ <;> rw [← map_mul] <;> rfl)
    hx
/-
**IntermediateField.algHom_ext_of_eq_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField`。
形式化陈述：algHom_ext_of_eq_adjoin {S : IntermediateField F E} {s : Set E} (hS : S = 
adjoin F s) ⦃φ₁ φ₂ : S ->ₐ[F] K⦄ (h : forall x hx, φ₁ ⟨x, hS.ge (subset_adjoin _
 _ hx)⟩ = φ₂ ⟨x, hS.ge (subset_adjoin _ _ hx)⟩) : φ₁ = φ₂
参数：hS : S = adjoin F s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin_algHom_ext`：adjoin_algHom_ext {s : Set E} ⦃φ₁ φ
₂ : adjoin F s ->ₐ[F] K⦄ (h : forall x hx, φ₁ ⟨x, subset_adjoin _ _ hx⟩ = φ₂ ⟨x,
 subset_adjoin _ _ hx⟩) :…
-/
theorem algHom_ext_of_eq_adjoin {S : IntermediateField F E} {s : Set E} (hS : S = adjoin F s)
    ⦃φ₁ φ₂ : S →ₐ[F] K⦄
    (h : ∀ x hx, φ₁ ⟨x, hS.ge (subset_adjoin _ _ hx)⟩ = φ₂ ⟨x, hS.ge (subset_adjoin _ _ hx)⟩) :
    φ₁ = φ₂ := by
  subst hS; exact adjoin_algHom_ext F h

end

open Lean in
/-- Supporting function for the `F⟮x₁,x₂,...,xₙ⟯` adjunction notation. -/
private meta def mkInsertTerm {m : Type → Type} [Monad m] [MonadQuotation m]
    (xs : TSyntaxArray `term) : m Term := run 0 where
  run (i : Nat) : m Term := do
    if h : i + 1 = xs.size then
      ``(singleton $(xs[i]))
    else if h : i < xs.size then
      ``(insert $(xs[i]) $(← run (i + 1)))
    else
      ``(EmptyCollection.emptyCollection)

/-- If `x₁ x₂ ... xₙ : E` then `F⟮x₁,x₂,...,xₙ⟯` is the `IntermediateField F E`
generated by these elements. -/
scoped macro:max K:term "⟮" xs:term,* "⟯" : term => do ``(adjoin $K $(← mkInsertTerm xs.getElems))

open Lean PrettyPrinter.Delaborator SubExpr in
@[app_delab IntermediateField.adjoin]
meta partial def delabAdjoinNotation : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.isAppOfArity ``adjoin 6
  let F ← withNaryArg 0 delab
  let xs ← withNaryArg 5 delabInsertArray
  `($F⟮$(xs.toArray),*⟯)
where
  delabInsertArray : DelabM (List Term) := do
    let e ← getExpr
    if e.isAppOfArity ``EmptyCollection.emptyCollection 2 then
      return []
    else if e.isAppOfArity ``singleton 4 then
      let x ← withNaryArg 3 delab
      return [x]
    else if e.isAppOfArity ``insert 5 then
      let x ← withNaryArg 3 delab
      let xs ← withNaryArg 4 delabInsertArray
      return x :: xs
    else failure

section AdjoinSimple

variable (α : E)

/-
**IntermediateField.mem_adjoin_simple_self** 是 Mathlib 中的一个定理，位于命名空间 `Intermedia
teField`。
形式化陈述：mem_adjoin_simple_self : α in F⟮α⟯
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem mem_adjoin_simple_self : α ∈ F⟮α⟯ :=
  subset_adjoin F {α} (Set.mem_singleton α)

/-- generator of `F⟮α⟯` -/
/-
**IntermediateField.AdjoinSimple.gen** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateFiel
d.AdjoinSimple`。
形式化陈述：(F : Type u_1) → [inst : Field F] → {E : Type u_2} → [inst_1 : Field E] → 
[inst_2 : Algebra F E] → (α : E) → ↥F⟮α⟯
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯

--- 原说明 ---
generator of `F⟮α⟯`
-/
def AdjoinSimple.gen : F⟮α⟯ :=
  ⟨α, mem_adjoin_simple_self F α⟩

@[simp]
/-
**IntermediateField.AdjoinSimple.coe_gen** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field.AdjoinSimple`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E] (α : E),   ↑(IntermediateField.AdjoinSimple.gen F α) = α
参数：F : Type u_1；α : E；IntermediateField.AdjoinSimple.gen F α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AdjoinSimple.coe_gen : (AdjoinSimple.gen F α : E) = α :=
  rfl
/-
**IntermediateField.AdjoinSimple.algebraMap_gen** 是 Mathlib 中的一个定理，位于命名空间 `Inter
mediateField.AdjoinSimple`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E] (α : E),   (algebraMap (↥F⟮α⟯) E) (IntermediateField.AdjoinSimp
le.gen F α) = α
参数：F : Type u_1；α : E；algebraMap (↥F⟮α⟯) E；IntermediateField.AdjoinSimple.gen F 
α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
theorem AdjoinSimple.algebraMap_gen : algebraMap F⟮α⟯ E (AdjoinSimple.gen F α) = α :=
  rfl

-- Note: After unfolding `AdjoinSimple.gen`, the simp lemma `coe_aeval_mk_apply`
-- does not fire, so we have to add this.
@[simp]
/-
**IntermediateField.AdjoinSimple.coe_aeval_gen_apply** 是 Mathlib 中的一个定理，位于命名空间 `
IntermediateField.AdjoinSimple`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E] (α : E) (f : Polynomial F),   ↑((Polynomial.aeval (Intermediate
Field.AdjoinSimple.gen F α)) f) = (Polynomial.aeval α) f
参数：F : Type u_1；α : E；f : Polynomial F；(Polynomial.aeval (IntermediateField.Adjo
inSimple.gen F α)) f；Polynomial.aeval α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.coe_aeval_mk_apply`：coe_aeval_mk_apply {S : Subalgebra R A} (
h : x in S) : (aeval (⟨x, h⟩ : S) p : A) = aeval x p
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯
-/
theorem AdjoinSimple.coe_aeval_gen_apply (f : F[X]) :
    aeval (AdjoinSimple.gen F α) f = aeval α f :=
  Polynomial.coe_aeval_mk_apply ..
/-
**IntermediateField.adjoin_simple_adjoin_simple** 是 Mathlib 中的一个定理，位于命名空间 `Inter
mediateField`。
形式化陈述：adjoin_simple_adjoin_simple (β : E) : F⟮α⟯⟮β⟯.restrictScalars F = F⟮α, β⟯
参数：β : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_adjoin_left`：adjoin_adjoin_left (T : Set E) : (
adjoin (adjoin F S) T).restrictScalars _ = adjoin F (S union T)
-/
theorem adjoin_simple_adjoin_simple (β : E) : F⟮α⟯⟮β⟯.restrictScalars F = F⟮α, β⟯ :=
  adjoin_adjoin_left _ _ _
/-
**IntermediateField.adjoin_simple_comm** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：adjoin_simple_comm (β : E) : F⟮α⟯⟮β⟯.restrictScalars F = F⟮β⟯⟮α⟯.restrictS
calars F
参数：β : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_adjoin_comm`：adjoin_adjoin_comm (T : Set E) : (
adjoin (adjoin F S) T).restrictScalars F = (adjoin (adjoin F T) S).restrictScala
rs F
-/
theorem adjoin_simple_comm (β : E) : F⟮α⟯⟮β⟯.restrictScalars F = F⟮β⟯⟮α⟯.restrictScalars F :=
  adjoin_adjoin_comm _ _ _

variable {F} {α}
/-
**IntermediateField.adjoin_simple_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：adjoin_simple_le_iff {K : IntermediateField F E} : F⟮α⟯ <= K ↔ α in K
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
theorem adjoin_simple_le_iff {K : IntermediateField F E} : F⟮α⟯ ≤ K ↔ α ∈ K := by simp
/-
**IntermediateField.biSup_adjoin_simple** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：biSup_adjoin_simple : ⨆ x in S, F⟮x⟯ = adjoin F S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `IntermediateField.gc`：gc : GaloisConnection (adjoin F : Set E -> Interme
diateField F E) (fun (x : IntermediateField F E) => (x : Set E))
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
-/
theorem biSup_adjoin_simple : ⨆ x ∈ S, F⟮x⟯ = adjoin F S := by
  rw [← iSup_subtype'', ← gc.l_iSup, iSup_subtype'']; congr; exact S.biUnion_of_singleton

variable {A B C : Type*} [Field A] [Field B] [Field C] [Algebra A B] [Algebra B C] [Algebra A C]
  [IsScalarTower A B C] (b : B)

/-- Ring homomorphism between `A⟮b⟯` and `A⟮↑b⟯`. -/
/-
**IntermediateField.RingHom.adjoinAlgebraMap** 是 Mathlib 中的一个定义，位于命名空间 `Intermed
iateField.RingHom`。
形式化陈述：{A : Type u_3} →   {B : Type u_4} →     {C : Type u_5} →       [inst : Fie
ld A] →         [inst_1 : Field B] →           [inst_2 : Field C] →             
[inst_3 : Algebra A B] →               [inst_4 : Algebra B C] →                 
[inst_5 : Algebra A C] → [IsScalarTower A B C] → (b : B) → ↥A⟮b⟯ →+* ↥A⟮(algebra
Map B C) b⟯
参数：b : B；algebraMap B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring homomorphism between `A⟮b⟯` and `A⟮↑b⟯`.
-/
def RingHom.adjoinAlgebraMap : A⟮b⟯ →+* A⟮((algebraMap B C) b)⟯ :=
  RingHom.codRestrict (((Algebra.ofId B C).restrictScalars A).comp (IntermediateField.val A⟮b⟯)) _
    (fun x ↦ by
      rw [show (algebraMap B C) b = (Algebra.ofId B C).restrictScalars A b by rfl,
        ← Set.image_singleton, ← IntermediateField.adjoin_map A {b}]
      use x
      simp)
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra A⟮b⟯ A⟮(algebraMap B C) b⟯ :=
  RingHom.toAlgebra (RingHom.adjoinAlgebraMap _)
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower A⟮b⟯ A⟮(algebraMap B C) b⟯ C :=
  IsScalarTower.of_algebraMap_eq' rfl

end AdjoinSimple

end AdjoinDef

section AdjoinIntermediateFieldLattice

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] {α : E} {S : Set E}

@[simp]
/-
**IntermediateField.adjoin_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：adjoin_eq_bot_iff : adjoin F S = ⊥ ↔ S subseteq (⊥ : IntermediateField F E
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem adjoin_eq_bot_iff : adjoin F S = ⊥ ↔ S ⊆ (⊥ : IntermediateField F E) := by
  rw [eq_bot_iff, adjoin_le_iff]
/-
**IntermediateField.adjoin_simple_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField`。
形式化陈述：adjoin_simple_eq_bot_iff : F⟮α⟯ = ⊥ ↔ α in (⊥ : IntermediateField F E)
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
theorem adjoin_simple_eq_bot_iff : F⟮α⟯ = ⊥ ↔ α ∈ (⊥ : IntermediateField F E) := by
  simp

@[simp]
/-
**IntermediateField.adjoin_zero** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_zero : F⟮(0 : E)⟯ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.adjoin_simple_eq_bot_iff`：adjoin_simple_eq_bot_iff : F
⟮α⟯ = ⊥ ↔ α in (⊥ : IntermediateField F E)
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
theorem adjoin_zero : F⟮(0 : E)⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (zero_mem ⊥)

@[simp]
/-
**IntermediateField.adjoin_one** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_one : F⟮(1 : E)⟯ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.adjoin_simple_eq_bot_iff`：adjoin_simple_eq_bot_iff : F
⟮α⟯ = ⊥ ↔ α in (⊥ : IntermediateField F E)
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
theorem adjoin_one : F⟮(1 : E)⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (one_mem ⊥)

@[simp]
/-
**IntermediateField.adjoin_intCast** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：adjoin_intCast (n : Int) : F⟮(n : E)⟯ = ⊥
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.adjoin_simple_eq_bot_iff`：adjoin_simple_eq_bot_iff : F
⟮α⟯ = ⊥ ↔ α in (⊥ : IntermediateField F E)
· 使用定理 `intCast_mem`：intCast_mem (n : Int) : (n : R) in s
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
-/
theorem adjoin_intCast (n : ℤ) : F⟮(n : E)⟯ = ⊥ := by
  exact adjoin_simple_eq_bot_iff.mpr (intCast_mem ⊥ n)

@[simp]
/-
**IntermediateField.adjoin_natCast** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：adjoin_natCast (n : Nat) : F⟮(n : E)⟯ = ⊥
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.adjoin_simple_eq_bot_iff`：adjoin_simple_eq_bot_iff : F
⟮α⟯ = ⊥ ↔ α in (⊥ : IntermediateField F E)
· 使用定理 `IntermediateField.natCast_mem`：natCast_mem (n : Nat) : (n : L) in S
-/
theorem adjoin_natCast (n : ℕ) : F⟮(n : E)⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (natCast_mem ⊥ n)

end AdjoinIntermediateFieldLattice

section Induction

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

/-- An intermediate field `S` is finitely generated if there exists `t : Finset E` such that
`IntermediateField.adjoin F t = S`.

We use the class `Algebra.EssFiniteType F E` instead of `(⊤ : IntermediateField F E).FG` to say that
`E` is finitely generated as an `F` extension.
See `IntermediateField.fg_top_iff`. -/
@[stacks 09FZ "second part"]
/-
**IntermediateField.FG** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：FG (S : IntermediateField F E) : Prop
参数：S : IntermediateField F E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An intermediate field `S` is finitely generated if there exists `t : Finset E` s
uch that
`IntermediateField.adjoin F t = S`.

We use the class `Algebra.EssFiniteType F E` instead of `(⊤ : IntermediateField 
F E).FG` to say that
`E` is finitely generated as an `F` extension.
See `IntermediateField.fg_top_iff`.
-/
def FG (S : IntermediateField F E) : Prop :=
  ∃ t : Finset E, adjoin F ↑t = S
/-
**IntermediateField.fg_adjoin_finset** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：fg_adjoin_finset (t : Finset E) : (adjoin F (↑t : Set E)).FG
参数：t : Finset E。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fg_adjoin_finset (t : Finset E) : (adjoin F (↑t : Set E)).FG :=
  ⟨t, rfl⟩
/-
**IntermediateField.fg_def** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：fg_def {S : IntermediateField F E} : S.FG ↔ exists t : Set E, Set.Finite t
 ∧ adjoin F t = S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.exists_finite_iff_finset`：exists_finite_iff_finset {p : Set α -> Pro
p} : (exists s : Set α, s.Finite ∧ p s) ↔ exists s : Finset α, p ↑s
-/
theorem fg_def {S : IntermediateField F E} : S.FG ↔ ∃ t : Set E, Set.Finite t ∧ adjoin F t = S :=
  Iff.symm Set.exists_finite_iff_finset
/-
**IntermediateField.fg_adjoin_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：fg_adjoin_of_finite {t : Set E} (h : Set.Finite t) : (adjoin F t).FG
参数：h : Set.Finite t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.fg_def`：fg_def {S : IntermediateField F E} : S.FG ↔ ex
ists t : Set E, Set.Finite t ∧ adjoin F t = S
-/
theorem fg_adjoin_of_finite {t : Set E} (h : Set.Finite t) : (adjoin F t).FG :=
  fg_def.mpr ⟨t, h, rfl⟩
/-
**IntermediateField.fg_bot** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：fg_bot : (⊥ : IntermediateField F E).FG
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `IntermediateField.adjoin_empty`：adjoin_empty (F E : Type*) [Field F] [Fi
eld E] [Algebra F E] : adjoin F (∅ : Set E) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fg_bot : (⊥ : IntermediateField F E).FG :=
  ⟨∅, by simp only [Finset.coe_empty, adjoin_empty]⟩
/-
**IntermediateField.fg_sup** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：fg_sup {S T : IntermediateField F E} (hS : S.FG) (hT : T.FG) : (S ⊔ T).FG
参数：hS : S.FG；hT : T.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin_union`：adjoin_union {S T : Set E} : adjoin F (S
 union T) = adjoin F S ⊔ adjoin F T
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `IntermediateField.fg_adjoin_finset`：fg_adjoin_finset (t : Finset E) : (a
djoin F (↑t : Set E)).FG
-/
theorem fg_sup {S T : IntermediateField F E} (hS : S.FG) (hT : T.FG) : (S ⊔ T).FG := by
  obtain ⟨s, rfl⟩ := hS; obtain ⟨t, rfl⟩ := hT
  classical rw [← adjoin_union, ← Finset.coe_union]
  exact fg_adjoin_finset _
/-
**IntermediateField.fg_iSup** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：fg_iSup {ι : Sort*} [Finite ι] {S : ι -> IntermediateField F E} (h : foral
l i, (S i).FG) : (⨆ i, S i).FG
参数：h : forall i, (S i).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.fg_adjoin_of_finite`：fg_adjoin_of_finite {t : Set E} (
h : Set.Finite t) : (adjoin F t).FG
· 使用定理 `Set.finite_iUnion`：finite_iUnion [Finite ι] {f : ι -> Set α} (H : forall
 i, (f i).Finite) : (⋃ i, f i).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem fg_iSup {ι : Sort*} [Finite ι] {S : ι → IntermediateField F E} (h : ∀ i, (S i).FG) :
    (⨆ i, S i).FG := by
  choose s hs using h
  simp_rw [← hs, ← adjoin_iUnion]
  exact fg_adjoin_of_finite (Set.finite_iUnion fun _ ↦ Finset.finite_toSet _)

/-- A field is finitely generated if and only if it is finitely generated over its prime
subfield. -/
/-
**IntermediateField._root_.Field.fg_iff_fg_top_bot** 是 Mathlib 中的一个定理，位于命名空间 `In
termediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A field is finitely generated if and only if it is finitely generated over its p
rime
subfield.
-/
theorem _root_.Field.fg_iff_fg_top_bot :
    Field.FG F ↔ (⊤ : IntermediateField (⊥ : Subfield F) F).FG := by
  simp [Field.fg_iff, fg_def, Set.exists_finite_iff_finset,
    ← toSubfield_inj, Subfield.algebraMap_ofSubfield, Subfield.closure_union]
/-
**IntermediateField.induction_on_adjoin_finset** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField`。
形式化陈述：induction_on_adjoin_finset (S : Finset E) (P : IntermediateField F E -> Pr
op) (base : P ⊥) (ih : forall (K : IntermediateField F E), forall x in S, P K ->
 P (K⟮x⟯.restrictScalars F)) : P (adjoin F S)
参数：S : Finset E；P : IntermediateField F E -> Prop；base : P ⊥；ih : forall (K : In
termediateField F E), forall x in S, P K -> P (K⟮x⟯.restrictScalars F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on'`：induction_on' {α : Type*} {motive : Finset α -> Pr
op} [DecidableEq α] (S : Finset α) (empty : motive ∅) (insert : forall (a s), a 
in S -> s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `IntermediateField.adjoin_empty`：adjoin_empty (F E : Type*) [Field F] [Fi
eld E] [Algebra F E] : adjoin F (∅ : Set E) = ⊥
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin_adjoin_left`：adjoin_adjoin_left (T : Set E) : (
adjoin (adjoin F S) T).restrictScalars _ = adjoin F (S union T)
-/
theorem induction_on_adjoin_finset (S : Finset E) (P : IntermediateField F E → Prop) (base : P ⊥)
    (ih : ∀ (K : IntermediateField F E), ∀ x ∈ S, P K → P (K⟮x⟯.restrictScalars F)) :
    P (adjoin F S) := by
  classical
  refine Finset.induction_on' S ?_ (fun _ _ ha _ _ h => ?_)
  · simp [base]
  · rw [Finset.coe_insert, Set.insert_eq, Set.union_comm, ← adjoin_adjoin_left]
    exact ih (adjoin F _) _ ha h
/-
**IntermediateField.induction_on_adjoin_fg** 是 Mathlib 中的一个定理，位于命名空间 `Intermedia
teField`。
形式化陈述：induction_on_adjoin_fg (P : IntermediateField F E -> Prop) (base : P ⊥) (i
h : forall (K : IntermediateField F E) (x : E), P K -> P (K⟮x⟯.restrictScalars F
)) (K : IntermediateField F E) (hK : K.FG) : P K
参数：P : IntermediateField F E -> Prop；base : P ⊥；ih : forall (K : IntermediateFie
ld F E) (x : E), P K -> P (K⟮x⟯.restrictScalars F)；K : IntermediateField F E；hK 
: K.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.induction_on_adjoin_finset`：induction_on_adjoin_finset
 (S : Finset E) (P : IntermediateField F E -> Prop) (base : P ⊥) (ih : forall (K
 : IntermediateField F E), forall …
-/
theorem induction_on_adjoin_fg (P : IntermediateField F E → Prop) (base : P ⊥)
    (ih : ∀ (K : IntermediateField F E) (x : E), P K → P (K⟮x⟯.restrictScalars F))
    (K : IntermediateField F E) (hK : K.FG) : P K := by
  obtain ⟨S, rfl⟩ := hK
  exact induction_on_adjoin_finset S P base fun K x _ hK => ih K x hK

end Induction

end IntermediateField

namespace IntermediateField

variable {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

/-
**IntermediateField.map_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：map_comap_eq (f : L ->ₐ[K] L') (S : IntermediateField K L') : (S.comap f).
map f = S ⊓ f.fieldRange
参数：f : L ->ₐ[K] L'；S : IntermediateField K L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
-/
theorem map_comap_eq (f : L →ₐ[K] L') (S : IntermediateField K L') :
    (S.comap f).map f = S ⊓ f.fieldRange :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range
/-
**IntermediateField.map_comap_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：map_comap_eq_self {f : L ->ₐ[K] L'} {S : IntermediateField K L'} (h : S <=
 f.fieldRange) : (S.comap f).map f = S
参数：h : S <= f.fieldRange。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `IntermediateField.map_comap_eq`：map_comap_eq (f : L ->ₐ[K] L') (S : Inte
rmediateField K L') : (S.comap f).map f = S ⊓ f.fieldRange
-/
theorem map_comap_eq_self {f : L →ₐ[K] L'} {S : IntermediateField K L'} (h : S ≤ f.fieldRange) :
    (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using map_comap_eq f S
/-
**IntermediateField.map_comap_eq_self_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `I
ntermediateField`。
形式化陈述：map_comap_eq_self_of_surjective {f : L ->ₐ[K] L'} (hf : Function.Surjectiv
e f) (S : IntermediateField K L') : (S.comap f).map f = S
参数：hf : Function.Surjective f；S : IntermediateField K L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
-/
theorem map_comap_eq_self_of_surjective {f : L →ₐ[K] L'} (hf : Function.Surjective f)
    (S : IntermediateField K L') : (S.comap f).map f = S :=
  SetLike.coe_injective (Set.image_preimage_eq _ hf)
/-
**IntermediateField.comap_map** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：comap_map (f : L ->ₐ[K] L') (S : IntermediateField K L) : (S.map f).comap 
f = S
参数：f : L ->ₐ[K] L'；S : IntermediateField K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem comap_map (f : L →ₐ[K] L') (S : IntermediateField K L) : (S.map f).comap f = S :=
  SetLike.coe_injective (Set.preimage_image_eq _ f.injective)

end IntermediateField

section ExtendScalars

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]

namespace Subfield

variable (F : Subfield L)

@[simp]
/-
**Subfield.extendScalars_self** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：extendScalars_self : extendScalars (le_refl F) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.mem_extendScalars`：mem_extendScalars : x in extendScalars h ↔ x
 in E
· 使用定理 `IntermediateField.mem_bot`：mem_bot {x : E} : x in (⊥ : IntermediateField
 F E) ↔ x in Set.range (algebraMap F E)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem extendScalars_self : extendScalars (le_refl F) = ⊥ := by
  ext x
  rw [mem_extendScalars, IntermediateField.mem_bot]
  refine ⟨fun h ↦ ⟨⟨x, h⟩, rfl⟩, ?_⟩
  rintro ⟨y, rfl⟩
  exact y.2

@[simp]
/-
**Subfield.extendScalars_top** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：extendScalars_top : extendScalars (le_top : F <= ⊤) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.toSubfield_injective`：toSubfield_injective : Function.
Injective (toSubfield : IntermediateField K L -> _)
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.extendScalars_toSubfield`：extendScalars_toSubfield : (extendSca
lars h).toSubfield = E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extendScalars_top : extendScalars (le_top : F ≤ ⊤) = ⊤ :=
  IntermediateField.toSubfield_injective (by simp)

variable {F}
variable {E E' : Subfield L} (h : F ≤ E) (h' : F ≤ E')
/-
**Subfield.extendScalars_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：extendScalars_sup : extendScalars h ⊔ extendScalars h' = extendScalars (le
_sup_of_le_left h : F <= E ⊔ E')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
theorem extendScalars_sup :
    extendScalars h ⊔ extendScalars h' = extendScalars (le_sup_of_le_left h : F ≤ E ⊔ E') :=
  ((extendScalars.orderIso F).map_sup ⟨_, h⟩ ⟨_, h'⟩).symm
/-
**Subfield.extendScalars_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：extendScalars_inf : extendScalars h ⊓ extendScalars h' = extendScalars (le
_inf h h')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.map_inf`：OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β]
 (f : α ≃o β) (x y : α) : f (x ⊓ y) = f x ⊓ f y
-/
theorem extendScalars_inf : extendScalars h ⊓ extendScalars h' = extendScalars (le_inf h h') :=
  ((extendScalars.orderIso F).map_inf ⟨_, h⟩ ⟨_, h'⟩).symm

end Subfield

namespace IntermediateField

variable (F : IntermediateField K L)

@[simp]
/-
**IntermediateField.extendScalars_self** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：extendScalars_self : extendScalars (le_refl F) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.restrictScalars_injective`：restrictScalars_injective :
 Function.Injective (restrictScalars K : IntermediateField L' L -> IntermediateF
ield K L)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.restrictScalars_bot_eq_self`：restrictScalars_bot_eq_se
lf (K : IntermediateField F E) : (⊥ : IntermediateField K E).restrictScalars _ =
 K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extendScalars_self : extendScalars (le_refl F) = ⊥ :=
  restrictScalars_injective K (by simp)

@[simp]
/-
**IntermediateField.extendScalars_top** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：extendScalars_top : extendScalars (le_top : F <= ⊤) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.restrictScalars_injective`：restrictScalars_injective :
 Function.Injective (restrictScalars K : IntermediateField L' L -> IntermediateF
ield K L)
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extendScalars_top : extendScalars (le_top : F ≤ ⊤) = ⊤ :=
  restrictScalars_injective K (by simp)

variable {F}
variable {E E' : IntermediateField K L} (h : F ≤ E) (h' : F ≤ E')
/-
**IntermediateField.extendScalars_sup** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：extendScalars_sup : extendScalars h ⊔ extendScalars h' = extendScalars (le
_sup_of_le_left h : F <= E ⊔ E')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
theorem extendScalars_sup :
    extendScalars h ⊔ extendScalars h' = extendScalars (le_sup_of_le_left h : F ≤ E ⊔ E') :=
  ((extendScalars.orderIso F).map_sup ⟨_, h⟩ ⟨_, h'⟩).symm
/-
**IntermediateField.extendScalars_inf** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：extendScalars_inf : extendScalars h ⊓ extendScalars h' = extendScalars (le
_inf h h')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.map_inf`：OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β]
 (f : α ≃o β) (x y : α) : f (x ⊓ y) = f x ⊓ f y
-/
theorem extendScalars_inf : extendScalars h ⊓ extendScalars h' = extendScalars (le_inf h h') :=
  ((extendScalars.orderIso F).map_inf ⟨_, h⟩ ⟨_, h'⟩).symm

end IntermediateField

end ExtendScalars

