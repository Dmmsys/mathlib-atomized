/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Junyan Xu
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Extension of field embeddings

`IntermediateField.exists_algHom_of_adjoin_splits'` is the main result: if E/L/F is a tower of
field extensions, K is another extension of F, and `f` is an embedding of L/F into K/F, such
that the minimal polynomials of a set of generators of E/L splits in K (via `f`), then `f`
extends to an embedding of E/F into K/F.

## Reference

[Isaacs1980] *Roots of Polynomials in Algebraic Extensions of Fields*,
The American Mathematical Monthly

-/

@[expose] public section

open Polynomial

namespace IntermediateField

variable (F E K : Type*) [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] {S : Set E}

/-- Lifts `L → K` of `F → K` -/
/-
**IntermediateField.Lifts** 是 Mathlib 中的一个归纳类型，位于命名空间 `IntermediateField`。
形式化陈述：(F : Type u_1) →   (E : Type u_2) →     (K : Type u_3) →       [inst : Fie
ld F] → [inst_1 : Field E] → [inst_2 : Field K] → [Algebra F E] → [Algebra F K] 
→ Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifts `L → K` of `F → K`
-/
structure Lifts where
  /-- The domain of a lift. -/
  carrier : IntermediateField F E
  /-- The lifted RingHom, expressed as an AlgHom. -/
  emb : carrier →ₐ[F] K

variable {F E K}

namespace Lifts

/-
**IntermediateField.Lifts.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField.Lifts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Lifts F E K) where
  le L₁ L₂ := ∃ h : L₁.carrier ≤ L₂.carrier, ∀ x, L₂.emb (inclusion h x) = L₁.emb x
  le_refl L := ⟨le_rfl, by simp⟩
  le_trans L₁ L₂ L₃ := by
    rintro ⟨h₁₂, h₁₂'⟩ ⟨h₂₃, h₂₃'⟩
    refine ⟨h₁₂.trans h₂₃, fun _ ↦ ?_⟩
    rw [← inclusion_inclusion h₁₂ h₂₃, h₂₃', h₁₂']
  le_antisymm := by
    rintro ⟨L₁, e₁⟩ ⟨L₂, e₂⟩ ⟨h₁₂, h₁₂'⟩ ⟨h₂₁, h₂₁'⟩
    obtain rfl : L₁ = L₂ := h₁₂.antisymm h₂₁
    congr
    exact AlgHom.ext h₂₁'
/-
**IntermediateField.Lifts.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField.Lifts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : OrderBot (Lifts F E K) where
  bot := ⟨⊥, (Algebra.ofId F K).comp (botEquiv F E)⟩
  bot_le L := ⟨bot_le, fun x ↦ by
    obtain ⟨x, rfl⟩ := (botEquiv F E).symm.surjective x
    simp_rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    exact L.emb.commutes x⟩
/-
**IntermediateField.Lifts.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField.Lifts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Inhabited (Lifts F E K) :=
  ⟨⊥⟩

variable {L₁ L₂ : Lifts F E K}
/-
**IntermediateField.Lifts.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.Li
fts`。
形式化陈述：le_iff : L₁ <= L₂ ↔ exists h : L₁.carrier <= L₂.carrier, L₂.emb.comp (incl
usion h) = L₁.emb
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_iff : L₁ ≤ L₂ ↔
    ∃ h : L₁.carrier ≤ L₂.carrier, L₂.emb.comp (inclusion h) = L₁.emb := by
  simp_rw [AlgHom.ext_iff]; rfl
/-
**IntermediateField.Lifts.eq_iff_le_carrier_eq** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField.Lifts`。
形式化陈述：eq_iff_le_carrier_eq : L₁ = L₂ ↔ L₁ <= L₂ ∧ L₁.carrier = L₂.carrier
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_iff_le_carrier_eq : L₁ = L₂ ↔ L₁ ≤ L₂ ∧ L₁.carrier = L₂.carrier :=
  ⟨fun eq ↦ ⟨eq.le, congr_arg _ eq⟩, fun ⟨le, eq⟩ ↦ le.antisymm ⟨eq.ge, fun x ↦ (le.2 ⟨x, _⟩).symm⟩⟩
/-
**IntermediateField.Lifts.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.Li
fts`。
形式化陈述：eq_iff : L₁ = L₂ ↔ exists h : L₁.carrier = L₂.carrier, L₂.emb.comp (inclus
ion h.le) = L₁.emb
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.Lifts.eq_iff_le_carrier_eq`：eq_iff_le_carrier_eq : L₁ 
= L₂ ↔ L₁ <= L₂ ∧ L₁.carrier = L₂.carrier
· 使用定理 `IntermediateField.Lifts.le_iff`：le_iff : L₁ <= L₂ ↔ exists h : L₁.carrie
r <= L₂.carrier, L₂.emb.comp (inclusion h) = L₁.emb
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem eq_iff : L₁ = L₂ ↔
    ∃ h : L₁.carrier = L₂.carrier, L₂.emb.comp (inclusion h.le) = L₁.emb := by
  rw [eq_iff_le_carrier_eq, le_iff]
  exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨h.1.le, h.2⟩, h.1⟩⟩
/-
**IntermediateField.Lifts.lt_iff_le_carrier_ne** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField.Lifts`。
形式化陈述：lt_iff_le_carrier_ne : L₁ < L₂ ↔ L₁ <= L₂ ∧ L₁.carrier != L₂.carrier
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_iff_le_carrier_ne : L₁ < L₂ ↔ L₁ ≤ L₂ ∧ L₁.carrier ≠ L₂.carrier := by
  rw [lt_iff_le_and_ne, and_congr_right]; intro h; simp_rw [Ne, eq_iff_le_carrier_eq, h, true_and]
/-
**IntermediateField.Lifts.lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.Li
fts`。
形式化陈述：lt_iff : L₁ < L₂ ↔ exists h : L₁.carrier < L₂.carrier, L₂.emb.comp (inclus
ion h.le) = L₁.emb
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.Lifts.lt_iff_le_carrier_ne`：lt_iff_le_carrier_ne : L₁ 
< L₂ ↔ L₁ <= L₂ ∧ L₁.carrier != L₂.carrier
· 使用定理 `IntermediateField.Lifts.le_iff`：le_iff : L₁ <= L₂ ↔ exists h : L₁.carrie
r <= L₂.carrier, L₂.emb.comp (inclusion h) = L₁.emb
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem lt_iff : L₁ < L₂ ↔
    ∃ h : L₁.carrier < L₂.carrier, L₂.emb.comp (inclusion h.le) = L₁.emb := by
  rw [lt_iff_le_carrier_ne, le_iff]
  exact ⟨fun h ↦ ⟨h.1.1.lt_of_ne h.2, h.1.2⟩, fun h ↦ ⟨⟨h.1.le, h.2⟩, h.1.ne⟩⟩
/-
**IntermediateField.Lifts.le_of_carrier_le_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Inter
mediateField.Lifts`。
形式化陈述：le_of_carrier_le_iSup {ι} {ρ : ι -> Lifts F E K} {σ τ : Lifts F E K} (hσ :
 forall i, ρ i <= σ) (hτ : forall i, ρ i <= τ) (carrier_le : σ.carrier <= ⨆ i, (
ρ i).carrier) : σ <= τ
参数：hσ : forall i, ρ i <= σ；hτ : forall i, ρ i <= τ；carrier_le : σ.carrier <= ⨆ i
, (ρ i).carrier。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.Lifts.le_iff`：le_iff : L₁ <= L₂ ↔ exists h : L₁.carrie
r <= L₂.carrier, L₂.emb.comp (inclusion h) = L₁.emb
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `IntermediateField.algHom_ext_of_eq_adjoin`：algHom_ext_of_eq_adjoin {S : 
IntermediateField F E} {s : Set E} (hS : S = adjoin F s) ⦃φ₁ φ₂ : S ->ₐ[F] K⦄ (h
 : forall x hx, φ₁ ⟨x, hS.ge (s…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `IntermediateField.iSup_eq_adjoin`：iSup_eq_adjoin {ι} (f : ι -> Intermedi
ateField F E) : ⨆ i, f i = adjoin F (⋃ i, f i : Set E)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_of_carrier_le_iSup {ι} {ρ : ι → Lifts F E K} {σ τ : Lifts F E K}
    (hσ : ∀ i, ρ i ≤ σ) (hτ : ∀ i, ρ i ≤ τ) (carrier_le : σ.carrier ≤ ⨆ i, (ρ i).carrier) :
    σ ≤ τ :=
  le_iff.mpr ⟨carrier_le.trans (iSup_le fun i ↦ (hτ i).1), algHom_ext_of_eq_adjoin _
      (carrier_le.antisymm (iSup_le fun i ↦ (hσ i).1)|>.trans <| iSup_eq_adjoin _ _) fun x hx ↦
    have ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    ((hτ i).2 ⟨x, hx⟩).trans ((hσ i).2 ⟨x, hx⟩).symm⟩

/-- `σ : L →ₐ[F] K` is an extendible lift ("extendible pair" in [Isaacs1980]) if for every
intermediate field `M` that is finite-dimensional over `L`, `σ` extends to some `M →ₐ[F] K`.
In our definition we only require `M` to be finitely generated over `L`, which is equivalent
if the ambient field `E` is algebraic over `F` (which is the case in our main application).
We also allow the domain of the extension to be an intermediate field that properly contains `M`,
since one can always restrict the domain to `M`. -/
/-
**IntermediateField.Lifts.IsExtendible** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateFi
eld.Lifts`。
形式化陈述：IsExtendible (σ : Lifts F E K) : Prop
参数：σ : Lifts F E K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`σ : L →ₐ[F] K` is an extendible lift ("extendible pair" in [Isaacs1980]) if for
 every
intermediate field `M` that is finite-dimensional over `L`, `σ` extends to some 
`M →ₐ[F] K`.
In our definition we only require `M` to be finitely generated over `L`, which i
s equivalent
if the ambient field `E` is algebraic over `F` (which is the case in our main ap
plication).
We also allow the domain of the extension to be an intermediate field that prope
rly contains `M`,
since one can always restrict the domain to `M`.
-/
def IsExtendible (σ : Lifts F E K) : Prop :=
  ∀ S : Finset E, ∃ τ ≥ σ, (S : Set E) ⊆ τ.carrier

section Chain
variable (c : Set (Lifts F E K)) (hc : IsChain (· ≤ ·) c)

/-- The union of a chain of lifts. -/
/-
**IntermediateField.Lifts.union** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField.Lif
ts`。
形式化陈述：union : Lifts F E K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The union of a chain of lifts.
-/
noncomputable def union : Lifts F E K :=
  let t (i : ↑(insert ⊥ c)) := i.val.carrier
  have hc := hc.insert fun _ _ _ ↦ .inl bot_le
  have dir : Directed (· ≤ ·) t := hc.directedOn.directed_val.mono_comp _ fun _ _ h ↦ h.1
  ⟨iSup t, (Subalgebra.iSupLift (toSubalgebra <| t ·) dir (·.val.emb) (fun i j h ↦
    AlgHom.ext fun x ↦ (hc.total i.2 j.2).elim (fun hij ↦ (hij.snd x).symm) fun hji ↦ by
      rw [AlgHom.comp_apply, ← inclusion]
      dsimp only [coe_type_toSubalgebra]
      rw [← hji.snd (inclusion h x), inclusion_inclusion, inclusion_self, AlgHom.id_apply x])
    _ le_rfl).comp
      (Subalgebra.equivOfEq _ _ <| toSubalgebra_iSup_of_directed dir)⟩

set_option backward.isDefEq.respectTransparency false in
/-
**IntermediateField.Lifts.le_union** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.
Lifts`。
形式化陈述：le_union ⦃σ : Lifts F E K⦄ (hσ : σ in c) : σ <= union c hc
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Subalgebra.iSupLift_inclusion`：iSupLift_inclusion {dir : Directed (· <= 
·) K} {f : forall i, K i ->ₐ[R] B} {hf : forall (i j : ι) (h : K i <= K j), f i 
= (f j).comp (inclu…
· 使用定理 `Set.instNonemptyElemInsert`：∀ {α : Type u_1} (a : α) (s : Set α), Nonemp
ty ↑(insert a s)
-/
theorem le_union ⦃σ : Lifts F E K⦄ (hσ : σ ∈ c) : σ ≤ union c hc :=
  have hσ := Set.mem_insert_of_mem ⊥ hσ
  let t (i : ↑(insert ⊥ c)) := i.val.carrier
  ⟨le_iSup t ⟨σ, hσ⟩, fun x ↦ by
    dsimp only [union, AlgHom.comp_apply]
    exact Subalgebra.iSupLift_inclusion (K := (toSubalgebra <| t ·))
      (i := ⟨σ, hσ⟩) x (le_iSup (toSubalgebra <| t ·) ⟨σ, hσ⟩)⟩
/-
**IntermediateField.Lifts.carrier_union** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield.Lifts`。
形式化陈述：carrier_union : (union c hc).carrier = ⨆ i : c, i.1.carrier
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem carrier_union : (union c hc).carrier = ⨆ i : c, i.1.carrier :=
  le_antisymm (iSup_le <| by rintro ⟨i, rfl | hi⟩; exacts [bot_le, le_iSup_of_le ⟨i, hi⟩ le_rfl]) <|
    iSup_le fun i ↦ le_iSup_of_le ⟨i, .inr i.2⟩ le_rfl

/-- A chain of lifts has an upper bound. -/
/-
**IntermediateField.Lifts.exists_upper_bound** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField.Lifts`。
形式化陈述：exists_upper_bound (c : Set (Lifts F E K)) (hc : IsChain (· <= ·) c) : exi
sts ub, forall a in c, a <= ub
参数：c : Set (Lifts F E K)；hc : IsChain (· <= ·) c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.Lifts.le_union`：le_union ⦃σ : Lifts F E K⦄ (hσ : σ in 
c) : σ <= union c hc

--- 原说明 ---
A chain of lifts has an upper bound.
-/
theorem exists_upper_bound (c : Set (Lifts F E K)) (hc : IsChain (· ≤ ·) c) :
    ∃ ub, ∀ a ∈ c, a ≤ ub := ⟨_, le_union c hc⟩
/-
**IntermediateField.Lifts.union_isExtendible** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField.Lifts`。
形式化陈述：union_isExtendible [alg : Algebra.IsAlgebraic F E] [Nonempty c] (hext : fo
rall σ in c, σ.IsExtendible) : (union c hc).IsExtendible
参数：hext : forall σ in c, σ.IsExtendible。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IntermediateField.finiteDimensional_adjoin`：finiteDimensional_adjoin {S 
: Set L} [Finite S] (hS : forall x in S, IsIntegral K x) : FiniteDimensional K (
adjoin K S)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用引理 `Directed.finite_le`：Directed.finite_le {ι κ : Sort*} [Nonempty ι] [Finit
e κ] {f : ι -> α} (hf : Directed r f) (g : κ -> ι) : exists z, forall i, r (f (g
 i)) (f …
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `IsChain.directed`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} [St
d.Refl r] {f : β → α} {c : Set β},   IsChain (f ⁻¹'o r) c → Directed r fun x => 
f ↑x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.Lifts.le_iff`：le_iff : L₁ <= L₂ ↔ exists h : L₁.carrie
r <= L₂.carrier, L₂.emb.comp (inclusion h) = L₁.emb
· 使用定理 `IntermediateField.restrictScalars_adjoin`：restrictScalars_adjoin (K : In
termediateField F E) (S : Set E) : restrictScalars F (adjoin K S) = adjoin F (K 
union S)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IntermediateField.adjoin.mono`：∀ (F : Type u_1) [inst : Field F] {E : Ty
pe u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (S T : Set E),   S ⊆ T → Inter
mediateField.adjoin…
（共 47 条，此处仅展示前 30 条）
-/
theorem union_isExtendible [alg : Algebra.IsAlgebraic F E]
    [Nonempty c] (hext : ∀ σ ∈ c, σ.IsExtendible) :
    (union c hc).IsExtendible := fun S ↦ by
  let Ω := adjoin F (S : Set E) →ₐ[F] K
  have ⟨ω, hω⟩ : ∃ ω : Ω, ∀ π : c, ∃ θ ≥ π.1, ⟨_, ω⟩ ≤ θ ∧ θ.carrier = π.1.1 ⊔ adjoin F S := by
    by_contra!; choose π hπ using this
    have := finiteDimensional_adjoin (S := (S : Set E)) fun _ _ ↦ (alg.isIntegral).1 _
    have ⟨π₀, hπ₀⟩ := hc.directed.finite_le π
    have ⟨θ, hθπ, hθ⟩ := hext _ π₀.2 S
    rw [← adjoin_le_iff] at hθ
    let θ₀ := θ.emb.comp (inclusion hθ)
    have := (hπ₀ θ₀).trans hθπ
    exact hπ θ₀ ⟨_, θ.emb.comp <| inclusion <| sup_le this.1 hθ⟩
      ⟨le_sup_left, this.2⟩ ⟨le_sup_right, fun _ ↦ rfl⟩ rfl
  choose θ ge hθ eq using hω
  have : IsChain (· ≤ ·) (Set.range θ) := by
    simp_rw [← restrictScalars_adjoin_eq_sup, restrictScalars_adjoin] at eq
    rintro _ ⟨π₁, rfl⟩ _ ⟨π₂, rfl⟩ -
    wlog h : π₁ ≤ π₂ generalizing π₁ π₂
    · exact (this _ _ <| (hc.total π₁.2 π₂.2).resolve_left h).symm
    refine .inl (le_iff.mpr ⟨?_, algHom_ext_of_eq_adjoin _ (eq _) ?_⟩)
    · rw [eq, eq]; exact adjoin.mono _ _ _ (Set.union_subset_union_left _ h.1)
    rintro x (hx | hx)
    · change (θ π₂).emb (inclusion (ge π₂).1 <| inclusion h.1 ⟨x, hx⟩) =
        (θ π₁).emb (inclusion (ge π₁).1 ⟨x, hx⟩)
      rw [(ge π₁).2, (ge π₂).2, h.2]
    · change (θ π₂).emb (inclusion (hθ π₂).1 ⟨x, subset_adjoin _ _ hx⟩) =
        (θ π₁).emb (inclusion (hθ π₁).1 ⟨x, subset_adjoin _ _ hx⟩)
      rw [(hθ π₁).2, (hθ π₂).2]
  refine ⟨union _ this, le_of_carrier_le_iSup (fun π ↦ le_union c hc π.2)
    (fun π ↦ (ge π).trans <| le_union _ _ ⟨_, rfl⟩) (carrier_union _ _).le, ?_⟩
  simp_rw [carrier_union, iSup_range', eq]
  exact (subset_adjoin _ _).trans (SetLike.coe_subset_coe.mpr <|
    le_sup_right.trans <| le_iSup_of_le (Classical.arbitrary _) le_rfl)

end Chain

/-
**IntermediateField.Lifts.nonempty_algHom_of_exist_lifts_finset** 是 Mathlib 中的一个
定理，位于命名空间 `IntermediateField.Lifts`。
形式化陈述：nonempty_algHom_of_exist_lifts_finset [alg : Algebra.IsAlgebraic F E] (h :
 forall S : Finset E, exists σ : Lifts F E K, (S : Set E) subseteq σ.carrier) : 
Nonempty (E ->ₐ[F] K)
参数：h : forall S : Finset E, exists σ : Lifts F E K, (S : Set E) subseteq σ.carri
er。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `zorn_le₀`：zorn_le₀ (s : Set α) (ih : forall c subseteq s, IsChain (· <= 
·) c -> exists ub in s, forall z in c, z <= ub) : exists m, Maximal (· in s) m
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `IntermediateField.Lifts.union_isExtendible`：union_isExtendible [alg : Al
gebra.IsAlgebraic F E] [Nonempty c] (hext : forall σ in c, σ.IsExtendible) : (un
ion c hc).IsExtendible
· 使用定理 `IntermediateField.Lifts.le_union`：le_union ⦃σ : Lifts F E K⦄ (hσ : σ in 
c) : σ <= union c hc
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `SetLike.exists_of_lt`：exists_of_lt : p < q -> exists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.finiteDimensional_adjoin`：finiteDimensional_adjoin {S 
: Set L} [Finite S] (hS : forall x in S, IsIntegral K x) : FiniteDimensional K (
adjoin K S)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `Algebra.IsAlgebraic.tower_top`：Algebra.IsAlgebraic.tower_top [Algebra.Is
Algebraic K A] : Algebra.IsAlgebraic L A
· 使用定理 `IntermediateField.instIsScalarTowerSubtypeMem_1`：∀ {K : Type u_1} {L : T
ype u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] {S : Interme
diateField K L}   {E : Type u_4} [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `IntermediateField.Lifts.lt_iff`：lt_iff : L₁ < L₂ ↔ exists h : L₁.carrier
 < L₂.carrier, L₂.emb.comp (inclusion h.le) = L₁.emb
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.restrictScalars_adjoin_eq_sup`：restrictScalars_adjoin_
eq_sup (K : IntermediateField F E) (S : Set E) : restrictScalars F (adjoin K S) 
= K ⊔ adjoin F S
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 50 条，此处仅展示前 30 条）
-/
theorem nonempty_algHom_of_exist_lifts_finset [alg : Algebra.IsAlgebraic F E]
    (h : ∀ S : Finset E, ∃ σ : Lifts F E K, (S : Set E) ⊆ σ.carrier) :
    Nonempty (E →ₐ[F] K) := by
  have : (⊥ : Lifts F E K).IsExtendible := fun S ↦ have ⟨σ, hσ⟩ := h S; ⟨σ, bot_le, hσ⟩
  have ⟨ϕ, hϕ⟩ := zorn_le₀ {ϕ : Lifts F E K | ϕ.IsExtendible}
    fun c hext hc ↦ (isEmpty_or_nonempty c).elim
      (fun _ ↦ ⟨⊥, this, fun ϕ hϕ ↦ isEmptyElim (⟨ϕ, hϕ⟩ : c)⟩)
      fun _ ↦ ⟨_, union_isExtendible c hc hext, le_union c hc⟩
  suffices ϕ.carrier = ⊤ from ⟨ϕ.emb.comp <| ((equivOfEq this).trans topEquiv).symm⟩
  by_contra!
  obtain ⟨α, -, hα⟩ := SetLike.exists_of_lt this.lt_top
  let _ : Algebra ϕ.carrier K := ϕ.emb.toAlgebra
  let Λ := ϕ.carrier⟮α⟯ →ₐ[ϕ.carrier] K
  have := finiteDimensional_adjoin (S := {α}) fun _ _ ↦ ((alg.tower_top ϕ.carrier).isIntegral).1 _
  let L (σ : Λ) : Lifts F E K := ⟨ϕ.carrier⟮α⟯.restrictScalars F, σ.restrictScalars F⟩
  have hL (σ : Λ) : ϕ < L σ := lt_iff.mpr
    ⟨by simpa only [L, restrictScalars_adjoin_eq_sup, left_lt_sup, adjoin_simple_le_iff],
      AlgHom.coe_ringHom_injective σ.comp_algebraMap⟩
  have ⟨(ϕ_ext : ϕ.IsExtendible), ϕ_max⟩ := maximal_iff_forall_gt.mp hϕ
  simp_rw [Set.mem_ofPred, IsExtendible] at ϕ_max; push Not at ϕ_max
  choose S hS using fun σ : Λ ↦ ϕ_max (hL σ)
  classical
  have ⟨θ, hθϕ, hθ⟩ := ϕ_ext ({α} ∪ Finset.univ.biUnion S)
  simp_rw [Finset.coe_union, Set.union_subset_iff, Finset.coe_singleton, Set.singleton_subset_iff,
    Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.iUnion_subset_iff] at hθ
  have : ϕ.carrier⟮α⟯.restrictScalars F ≤ θ.carrier := by
    rw [restrictScalars_adjoin_eq_sup, sup_le_iff, adjoin_simple_le_iff]; exact ⟨hθϕ.1, hθ.1⟩
  exact hS ⟨(θ.emb.comp <| inclusion this).toRingHom, hθϕ.2⟩ θ ⟨this, fun _ ↦ rfl⟩ (hθ.2 _)

/-- Given a lift `x` and an integral element `s : E` over `x.carrier` whose conjugates over
`x.carrier` are all in `K`, we can extend the lift to a lift whose carrier contains `s`. -/
/-
**IntermediateField.Lifts.exists_lift_of_splits'** 是 Mathlib 中的一个定理，位于命名空间 `Inte
rmediateField.Lifts`。
形式化陈述：exists_lift_of_splits' (x : Lifts F E K) {s : E} (h1 : IsIntegral x.carrie
r s) (h2 : ((minpoly x.carrier s).map x.emb.toRingHom).Splits) : exists y, x <= 
y ∧ s in y.carrier
参数：x : Lifts F E K；h1 : IsIntegral x.carrier s；h2 : ((minpoly x.carrier s).map x
.emb.toRingHom).Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `minpoly.degree_pos`：degree_pos [Nontrivial B] (hx : IsIntegral A x) : 0 
< degree (minpoly A x)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_map`：degree_map (p : R[X]) (f : R ->+* S) : (p.map f).
degree = p.degree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Polynomial.mem_aroots`：mem_aroots [IsDomain T] [CommRing S] [IsDomain S]
 [Algebra T S] [Module.IsTorsionFree T S] {p : T[X]} {a : S} : a in p.aroots S ↔
 p != 0 ∧ a…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `Polynomial.eval_rootOfSplits`：eval_rootOfSplits (hf : f.Splits) (hfd : f
.degree != 0) : f.eval (rootOfSplits hf hfd) = 0
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `IntermediateField.algebraMap_mem`：algebraMap_mem (x : K) : algebraMap K 
L x in S
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯

--- 原说明 ---
Given a lift `x` and an integral element `s : E` over `x.carrier` whose conjugat
es over
`x.carrier` are all in `K`, we can extend the lift to a lift whose carrier conta
ins `s`.
-/
theorem exists_lift_of_splits' (x : Lifts F E K) {s : E} (h1 : IsIntegral x.carrier s)
    (h2 : ((minpoly x.carrier s).map x.emb.toRingHom).Splits) : ∃ y, x ≤ y ∧ s ∈ y.carrier :=
  have I2 := (minpoly.degree_pos h1).ne'
  letI : Algebra x.carrier K := x.emb.toRingHom.toAlgebra
  let carrier := x.carrier⟮s⟯.restrictScalars F
  letI : Algebra x.carrier carrier := x.carrier⟮s⟯.toSubalgebra.algebra
  let φ : carrier →ₐ[x.carrier] K := ((algHomAdjoinIntegralEquiv x.carrier h1).symm
    ⟨rootOfSplits h2 (by rwa [degree_map]), by
      rw [mem_aroots, and_iff_right (minpoly.ne_zero h1)]
      exact (eval_map _ _).symm.trans (eval_rootOfSplits _ _)⟩)
  ⟨⟨carrier, (@algHomEquivSigma F x.carrier carrier K _ _ _ _ _ _ _ _
      (IsScalarTower.of_algebraMap_eq fun _ ↦ rfl)).symm ⟨x.emb, φ⟩⟩,
    ⟨fun z hz ↦ algebraMap_mem x.carrier⟮s⟯ ⟨z, hz⟩, φ.commutes⟩,
    mem_adjoin_simple_self x.carrier s⟩

/-- Given an integral element `s : E` over `F` whose `F`-conjugates are all in `K`,
any lift can be extended to one whose carrier contains `s`. -/
/-
**IntermediateField.Lifts.exists_lift_of_splits** 是 Mathlib 中的一个定理，位于命名空间 `Inter
mediateField.Lifts`。
形式化陈述：exists_lift_of_splits (x : Lifts F E K) {s : E} (h1 : IsIntegral F s) (h2 
: ((minpoly F s).map (algebraMap F K)).Splits) : exists y, x <= y ∧ s in y.carri
er
参数：x : Lifts F E K；h1 : IsIntegral F s；h2 : ((minpoly F s).map (algebraMap F K))
.Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.Lifts.exists_lift_of_splits'`：exists_lift_of_splits' (
x : Lifts F E K) {s : E} (h1 : IsIntegral x.carrier s) (h2 : ((minpoly x.carrier
 s).map x.emb.toRingHom).Splits) : e…
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `IsIntegral.minpoly_splits_tower_top'`：IsIntegral.minpoly_splits_tower_to
p' (int : IsIntegral R x) {f : K ->+* L} (h : Splits ((minpoly R x).map (f.comp 
<| algebraMap R K))) : Spl…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B

--- 原说明 ---
Given an integral element `s : E` over `F` whose `F`-conjugates are all in `K`,
any lift can be extended to one whose carrier contains `s`.
-/
theorem exists_lift_of_splits (x : Lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : ((minpoly F s).map (algebraMap F K)).Splits) : ∃ y, x ≤ y ∧ s ∈ y.carrier :=
  exists_lift_of_splits' x h1.tower_top <| h1.minpoly_splits_tower_top' <| by
    rwa [← x.emb.comp_algebraMap] at h2

end Lifts

section

/-
**IntermediateField.exists_algHom_adjoin_of_splits''** 是 Mathlib 中的一个定理，位于命名空间 `
IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_algHom_adjoin_of_splits'' {L : IntermediateField F E}
    (f : L →ₐ[F] K) (hK : ∀ s ∈ S, IsIntegral L s ∧ ((minpoly L s).map f.toRingHom).Splits) :
    ∃ φ : adjoin L S →ₐ[F] K, φ.domRestrict L = f := by
  obtain ⟨φ, hfφ, hφ⟩ := zorn_le_nonempty_Ici₀ _
    (fun c _ hc _ _ ↦ Lifts.exists_upper_bound c hc) ⟨L, f⟩ le_rfl
  refine ⟨φ.emb.comp (inclusion <| (le_extendScalars_iff hfφ.1 <| adjoin L S).mp <|
    adjoin_le_iff.mpr fun s h ↦ ?_), AlgHom.ext hfφ.2⟩
  let := (inclusion hfφ.1).toAlgebra
  let : SMul L φ.carrier := Algebra.toSMul
  have : IsScalarTower L φ.carrier E := ⟨fun x y ↦ smul_assoc x (y : E)⟩
  have := φ.exists_lift_of_splits' (hK s h).1.tower_top ((hK s h).1.minpoly_splits_tower_top' ?_)
  · obtain ⟨y, h1, h2⟩ := this
    exact (hφ h1).1 h2
  · convert! (hK s h).2; ext; apply hfφ.2

variable {L : Type*} [Field L] [Algebra F L] [Algebra L E] [IsScalarTower F L E]
  (f : L →ₐ[F] K) (hK : ∀ s ∈ S, IsIntegral L s ∧ ((minpoly L s).map f.toRingHom).Splits)

set_option backward.isDefEq.respectTransparency.types false in
include hK in
/-
**IntermediateField.exists_algHom_adjoin_of_splits'** 是 Mathlib 中的一个定理，位于命名空间 `I
ntermediateField`。
形式化陈述：exists_algHom_adjoin_of_splits' : exists φ : adjoin L S ->ₐ[F] K, φ.domRes
trict L = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.instIsScalarTowerSubtypeMem_1`：∀ {K : Type u_1} {L : T
ype u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] {S : Interme
diateField K L}   {E : Type u_4} [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `_private.Mathlib.FieldTheory.Extension.0.IntermediateField.exists_algHom
_adjoin_of_splits''`：∀ {F : Type u_1} {E : Type u_2} {K : Type u_3} [inst : Fiel
d F] [inst_1 : Field E] [inst_2 : Field K]   [inst_3 : Algebra F E] [inst_4 : Al
g…
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsIntegral.minpoly_splits_tower_top'`：IsIntegral.minpoly_splits_tower_to
p' (int : IsIntegral R x) {f : K ->+* L} (h : Splits ((minpoly R x).map (f.comp 
<| algebraMap R K))) : Spl…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `IntermediateField.subset_adjoin_of_subset_left`：subset_adjoin_of_subset_
left {F : Subfield E} {T : Set E} (HT : T subseteq F) : T subseteq adjoin F S
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem exists_algHom_adjoin_of_splits' :
    ∃ φ : adjoin L S →ₐ[F] K, φ.domRestrict L = f := by
  let L' := (IsScalarTower.toAlgHom F L E).fieldRange
  let f' : L' →ₐ[F] K := f.comp (AlgEquiv.ofInjectiveField _).symm.toAlgHom
  have := exists_algHom_adjoin_of_splits'' f' (S := S) fun s hs ↦ ?_
  · obtain ⟨φ, hφ⟩ := this; refine ⟨φ.comp <|
      inclusion (?_ : (adjoin L S).restrictScalars F ≤ (adjoin L' S).restrictScalars F), ?_⟩
    · simp_rw [← SetLike.coe_subset_coe, coe_restrictScalars, adjoin_subset_adjoin_iff]
      exact ⟨subset_adjoin_of_subset_left S (F := L'.toSubfield) le_rfl, subset_adjoin _ _⟩
    · ext x
      let y := (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) x
      refine Eq.trans congr($hφ y) ?_
      simp only [AlgHom.coe_comp, Function.comp_apply, f']
      exact congr_arg f (AlgEquiv.symm_apply_apply _ _)
  let : Algebra L L' := (AlgEquiv.ofInjectiveField _).toRingHom.toAlgebra
  have : IsScalarTower L L' E := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨(hK s hs).1.tower_top, (hK s hs).1.minpoly_splits_tower_top' ?_⟩
  convert! (hK s hs).2
  ext
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
    AlgHom.coe_comp, Function.comp_apply, f']
  exact congr_arg f (AlgEquiv.symm_apply_apply _ _)

include hK in
/-
**IntermediateField.exists_algHom_of_adjoin_splits'** 是 Mathlib 中的一个定理，位于命名空间 `I
ntermediateField`。
形式化陈述：exists_algHom_of_adjoin_splits' (hS : adjoin L S = ⊤) : exists φ : E ->ₐ[F
] K, φ.domRestrict L = f
参数：hS : adjoin L S = ⊤。
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
· 使用定理 `IntermediateField.exists_algHom_adjoin_of_splits'`：exists_algHom_adjoin_
of_splits' : exists φ : adjoin L S ->ₐ[F] K, φ.domRestrict L = f
-/
theorem exists_algHom_of_adjoin_splits' (hS : adjoin L S = ⊤) :
    ∃ φ : E →ₐ[F] K, φ.domRestrict L = f :=
  have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits' f hK
  ⟨φ.comp (((equivOfEq hS).trans topEquiv).symm.toAlgHom.restrictScalars F), hφ⟩
/-
**IntermediateField.exists_algHom_of_splits'** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField`。
形式化陈述：exists_algHom_of_splits' (hK : forall s : E, IsIntegral L s ∧ ((minpoly L 
s).map f.toRingHom).Splits) : exists φ : E ->ₐ[F] K, φ.domRestrict L = f
参数：hK : forall s : E, IsIntegral L s ∧ ((minpoly L s).map f.toRingHom).Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.exists_algHom_of_adjoin_splits'`：exists_algHom_of_adjo
in_splits' (hS : adjoin L S = ⊤) : exists φ : E ->ₐ[F] K, φ.domRestrict L = f
· 使用定理 `IntermediateField.adjoin_univ`：adjoin_univ (F E : Type*) [Field F] [Fiel
d E] [Algebra F E] : adjoin F (Set.univ : Set E) = ⊤
-/
theorem exists_algHom_of_splits'
    (hK : ∀ s : E, IsIntegral L s ∧ ((minpoly L s).map f.toRingHom).Splits) :
    ∃ φ : E →ₐ[F] K, φ.domRestrict L = f :=
  exists_algHom_of_adjoin_splits' f (fun x _ ↦ hK x) (adjoin_univ L E)

end

variable (hK : ∀ s ∈ S, IsIntegral F s ∧ ((minpoly F s).map (algebraMap F K)).Splits)
  (hK' : ∀ s : E, IsIntegral F s ∧ ((minpoly F s).map (algebraMap F K)).Splits)
  {L : IntermediateField F E} (f : L →ₐ[F] K) (hL : L ≤ adjoin F S) {x : E} {y : K}

section
include hK

/-
**IntermediateField.exists_algHom_adjoin_of_splits** 是 Mathlib 中的一个定理，位于命名空间 `In
termediateField`。
形式化陈述：exists_algHom_adjoin_of_splits : exists φ : adjoin F S ->ₐ[F] K, φ.comp (i
nclusion hL) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_le_nonempty_Ici₀`：zorn_le_nonempty_Ici₀ (a : α) (ih : forall c subs
eteq Ici a, IsChain (· <= ·) c -> forall y in c, exists ub, forall z in c, z <= 
ub) (x : α)…
· 使用定理 `IntermediateField.Lifts.exists_upper_bound`：exists_upper_bound (c : Set 
(Lifts F E K)) (hc : IsChain (· <= ·) c) : exists ub, forall a in c, a <= ub
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `IntermediateField.Lifts.exists_lift_of_splits`：exists_lift_of_splits (x 
: Lifts F E K) {s : E} (h1 : IsIntegral F s) (h2 : ((minpoly F s).map (algebraMa
p F K)).Splits) : exists y, x <= y …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
theorem exists_algHom_adjoin_of_splits : ∃ φ : adjoin F S →ₐ[F] K, φ.comp (inclusion hL) = f := by
  obtain ⟨φ, hfφ, hφ⟩ := zorn_le_nonempty_Ici₀ _
    (fun c _ hc _ _ ↦ Lifts.exists_upper_bound c hc) ⟨L, f⟩ le_rfl
  refine ⟨φ.emb.comp (inclusion <| adjoin_le_iff.mpr fun s hs ↦ ?_), ?_⟩
  · rcases φ.exists_lift_of_splits (hK s hs).1 (hK s hs).2 with ⟨y, h1, h2⟩
    exact (hφ h1).1 h2
  · ext; apply hfφ.2
/-
**IntermediateField.nonempty_algHom_adjoin_of_splits** 是 Mathlib 中的一个定理，位于命名空间 `
IntermediateField`。
形式化陈述：nonempty_algHom_adjoin_of_splits : Nonempty (adjoin F S ->ₐ[F] K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `IntermediateField.exists_algHom_adjoin_of_splits`：exists_algHom_adjoin_o
f_splits : exists φ : adjoin F S ->ₐ[F] K, φ.comp (inclusion hL) = f
-/
theorem nonempty_algHom_adjoin_of_splits : Nonempty (adjoin F S →ₐ[F] K) :=
  have ⟨φ, _⟩ := exists_algHom_adjoin_of_splits hK (⊥ : Lifts F E K).emb bot_le; ⟨φ⟩

variable (hS : adjoin F S = ⊤)

include hS in
/-
**IntermediateField.exists_algHom_of_adjoin_splits** 是 Mathlib 中的一个定理，位于命名空间 `In
termediateField`。
形式化陈述：exists_algHom_of_adjoin_splits : exists φ : E ->ₐ[F] K, φ.comp L.val = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.exists_algHom_adjoin_of_splits`：exists_algHom_adjoin_o
f_splits : exists φ : adjoin F S ->ₐ[F] K, φ.comp (inclusion hL) = f
-/
theorem exists_algHom_of_adjoin_splits : ∃ φ : E →ₐ[F] K, φ.comp L.val = f :=
  have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits hK f (hS.symm ▸ le_top)
  ⟨φ.comp ((equivOfEq hS).trans topEquiv).symm.toAlgHom, hφ⟩

include hS in
/-
**IntermediateField.nonempty_algHom_of_adjoin_splits** 是 Mathlib 中的一个定理，位于命名空间 `
IntermediateField`。
形式化陈述：nonempty_algHom_of_adjoin_splits : Nonempty (E ->ₐ[F] K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.exists_algHom_of_adjoin_splits`：exists_algHom_of_adjoi
n_splits : exists φ : E ->ₐ[F] K, φ.comp L.val = f
-/
theorem nonempty_algHom_of_adjoin_splits : Nonempty (E →ₐ[F] K) :=
  have ⟨φ, _⟩ := exists_algHom_of_adjoin_splits hK (⊥ : Lifts F E K).emb hS; ⟨φ⟩

variable (hx : x ∈ adjoin F S) (hy : aeval y (minpoly F x) = 0)
include hy
/-
**IntermediateField.exists_algHom_adjoin_of_splits_of_aeval** 是 Mathlib 中的一个定理，位
于命名空间 `IntermediateField`。
形式化陈述：exists_algHom_adjoin_of_splits_of_aeval : exists φ : adjoin F S ->ₐ[F] K, 
φ ⟨x, hx⟩ = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.isAlgebraic_adjoin`：isAlgebraic_adjoin {S : Set L} (hS
 : forall x in S, IsIntegral K x) : Algebra.IsAlgebraic K (adjoin K S)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.adjoin_simple_le_iff`：adjoin_simple_le_iff {K : Interm
ediateField F E} : F⟮α⟯ <= K ↔ α in K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.isIntegral_iff`：isIntegral_iff {x : S} : IsIntegral K 
x ↔ IsIntegral K (x : L)
· 使用定理 `isAlgebraic_iff_isIntegral`：isAlgebraic_iff_isIntegral {x : A} : IsAlgeb
raic K x ↔ IsIntegral K x
· 使用定理 `Polynomial.mem_aroots`：mem_aroots [IsDomain T] [CommRing S] [IsDomain S]
 [Algebra T S] [Module.IsTorsionFree T S] {p : T[X]} {a : S} : a in p.aroots S ↔
 p != 0 ∧ a…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IntermediateField.exists_algHom_adjoin_of_splits`：exists_algHom_adjoin_o
f_splits : exists φ : adjoin F S ->ₐ[F] K, φ.comp (inclusion hL) = f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用引理 `IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen`：algHomAdjoin
IntegralEquiv_symm_apply_gen (h : IsIntegral F α) (x : { x // x in (minpoly F α)
.aroots K }) : (algHomAdjoinIntegralEquiv F h).s…
-/
theorem exists_algHom_adjoin_of_splits_of_aeval : ∃ φ : adjoin F S →ₐ[F] K, φ ⟨x, hx⟩ = y := by
  have := isAlgebraic_adjoin (fun s hs ↦ (hK s hs).1)
  have ix : IsAlgebraic F _ := Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : adjoin F S)
  rw [isAlgebraic_iff_isIntegral, isIntegral_iff] at ix
  obtain ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits hK ((algHomAdjoinIntegralEquiv F ix).symm
    ⟨y, mem_aroots.mpr ⟨minpoly.ne_zero ix, hy⟩⟩) (adjoin_simple_le_iff.mpr hx)
  exact ⟨φ, (DFunLike.congr_fun hφ <| AdjoinSimple.gen F x).trans <|
    algHomAdjoinIntegralEquiv_symm_apply_gen F ix _⟩

include hS in
/-
**IntermediateField.exists_algHom_of_adjoin_splits_of_aeval** 是 Mathlib 中的一个定理，位
于命名空间 `IntermediateField`。
形式化陈述：exists_algHom_of_adjoin_splits_of_aeval : exists φ : E ->ₐ[F] K, φ x = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.mem_top`：mem_top {x : E} : x in (⊤ : IntermediateField
 F E)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.exists_algHom_adjoin_of_splits_of_aeval`：exists_algHom
_adjoin_of_splits_of_aeval : exists φ : adjoin F S ->ₐ[F] K, φ ⟨x, hx⟩ = y
-/
theorem exists_algHom_of_adjoin_splits_of_aeval : ∃ φ : E →ₐ[F] K, φ x = y :=
  have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits_of_aeval hK (hS ▸ mem_top) hy
  ⟨φ.comp ((equivOfEq hS).trans topEquiv).symm.toAlgHom, hφ⟩


include hK'

end

section
include hK'

/-
**IntermediateField.exists_algHom_of_splits** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField`。
形式化陈述：exists_algHom_of_splits : exists φ : E ->ₐ[F] K, φ.comp L.val = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.exists_algHom_of_adjoin_splits`：exists_algHom_of_adjoi
n_splits : exists φ : E ->ₐ[F] K, φ.comp L.val = f
· 使用定理 `IntermediateField.adjoin_univ`：adjoin_univ (F E : Type*) [Field F] [Fiel
d E] [Algebra F E] : adjoin F (Set.univ : Set E) = ⊤
-/
theorem exists_algHom_of_splits : ∃ φ : E →ₐ[F] K, φ.comp L.val = f :=
  exists_algHom_of_adjoin_splits (fun x _ ↦ hK' x) f (adjoin_univ F E)
/-
**IntermediateField.nonempty_algHom_of_splits** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField`。
形式化陈述：nonempty_algHom_of_splits : Nonempty (E ->ₐ[F] K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.nonempty_algHom_of_adjoin_splits`：nonempty_algHom_of_a
djoin_splits : Nonempty (E ->ₐ[F] K)
· 使用定理 `IntermediateField.adjoin_univ`：adjoin_univ (F E : Type*) [Field F] [Fiel
d E] [Algebra F E] : adjoin F (Set.univ : Set E) = ⊤
-/
theorem nonempty_algHom_of_splits : Nonempty (E →ₐ[F] K) :=
  nonempty_algHom_of_adjoin_splits (fun x _ ↦ hK' x) (adjoin_univ F E)
/-
**IntermediateField.exists_algHom_of_splits_of_aeval** 是 Mathlib 中的一个定理，位于命名空间 `
IntermediateField`。
形式化陈述：exists_algHom_of_splits_of_aeval (hy : aeval y (minpoly F x) = 0) : exists
 φ : E ->ₐ[F] K, φ x = y
参数：hy : aeval y (minpoly F x) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.exists_algHom_of_adjoin_splits_of_aeval`：exists_algHom
_of_adjoin_splits_of_aeval : exists φ : E ->ₐ[F] K, φ x = y
· 使用定理 `IntermediateField.adjoin_univ`：adjoin_univ (F E : Type*) [Field F] [Fiel
d E] [Algebra F E] : adjoin F (Set.univ : Set E) = ⊤
-/
theorem exists_algHom_of_splits_of_aeval (hy : aeval y (minpoly F x) = 0) :
    ∃ φ : E →ₐ[F] K, φ x = y :=
  exists_algHom_of_adjoin_splits_of_aeval (fun x _ ↦ hK' x) (adjoin_univ F E) hy

end

end IntermediateField

section Algebra.IsAlgebraic

/-- Let `K/F` be an algebraic extension of fields and `L` a field in which all the minimal
polynomial over `F` of elements of `K` splits. Then, for `x ∈ K`, the images of `x` by the
`F`-algebra morphisms from `K` to `L` are exactly the roots in `L` of the minimal polynomial
of `x` over `F`. -/
/-
**Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly_of_splits** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly_of_splits {F K : Type*} 
(L : Type*) [Field F] [Field K] [Field L] [Algebra F L] [Algebra F K] (hA : fora
ll x : K, ((minpoly F x).map (algebraMap F L)).Splits) [Algebra.IsAlgebraic F K]
 (x : K) : (Set.range fun (ψ : K ->ₐ[F] L) => ψ x) = (minpoly F x).rootSet L
参数：L : Type*；hA : forall x : K, ((minpoly F x).map (algebraMap F L)).Splits；x : 
K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.mem_rootSet_of_ne`：mem_rootSet_of_ne {p : T[X]} {S : Type*} [
IsDomain T] [CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] (
hp : p != 0) {a : …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IntermediateField.exists_algHom_of_splits_of_aeval`：exists_algHom_of_spl
its_of_aeval (hy : aeval y (minpoly F x) = 0) : exists φ : E ->ₐ[F] K, φ x = y

--- 原说明 ---
Let `K/F` be an algebraic extension of fields and `L` a field in which all the m
inimal
polynomial over `F` of elements of `K` splits. Then, for `x ∈ K`, the images of 
`x` by the
`F`-algebra morphisms from `K` to `L` are exactly the roots in `L` of the minima
l polynomial
of `x` over `F`.
-/
theorem Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly_of_splits {F K : Type*} (L : Type*)
    [Field F] [Field K] [Field L] [Algebra F L] [Algebra F K]
    (hA : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits)
    [Algebra.IsAlgebraic F K] (x : K) :
    (Set.range fun (ψ : K →ₐ[F] L) => ψ x) = (minpoly F x).rootSet L := by
  ext a
  rw [mem_rootSet_of_ne (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x))]
  refine ⟨fun ⟨ψ, hψ⟩ ↦ ?_, fun ha ↦ IntermediateField.exists_algHom_of_splits_of_aeval
    (fun x ↦ ⟨Algebra.IsIntegral.isIntegral x, hA x⟩) ha⟩
  rw [← hψ, Polynomial.aeval_algHom_apply ψ x, minpoly.aeval, map_zero]

end Algebra.IsAlgebraic

