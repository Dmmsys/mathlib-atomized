/-
Copyright (c) 2025 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
module

public import Mathlib.Order.Nucleus
public import Mathlib.Order.SupClosed

/-!
# Sublocale

Locales are the dual concept to frames. Locale theory is a branch of point-free topology, where
intuitively locales are like topological spaces which may or may not have enough points.
Sublocales of a locale generalize the concept of subspaces in topology to the point-free setting.

## TODO

Create separate definitions for `sInf_mem` and `HImpClosed` (also useful for `CompleteSublattice`)

## References

* [J. Picada A. Pultr, *Frames and Locales*][picado2012]
* https://ncatlab.org/nlab/show/sublocale
* https://ncatlab.org/nlab/show/nucleus
-/

@[expose] public section

variable {X : Type*} [Order.Frame X]
open Set

/-- A sublocale of a locale `X` is a set `S` which is closed under all meets and such that
`x ⇨ s ∈ S` for all `x : X` and `s ∈ S`.

Note that locales are the same thing as frames, but with reverse morphisms, which is why we assume
`Frame X`. We only need to define locales categorically. See `Locale`. -/
/-
**Sublocale** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_2) → [Order.Frame X] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sublocale of a locale `X` is a set `S` which is closed under all meets and suc
h that
`x ⇨ s ∈ S` for all `x : X` and `s ∈ S`.

Note that locales are the same thing as frames, but with reverse morphisms, whic
h is why we assume
`Frame X`. We only need to define locales categorically. See `Locale`.
-/
structure Sublocale (X : Type*) [Order.Frame X] where
  /-- The set corresponding to the sublocale. -/
  carrier : Set X
  /-- A sublocale is closed under all meets.

  Do NOT use directly. Use `Sublocale.sInf_mem` instead. -/
  sInf_mem' : ∀ s ⊆ carrier, sInf s ∈ carrier
  /-- A sublocale is closed under heyting implication.

  Do NOT use directly. Use `Sublocale.himp_mem` instead. -/
  himp_mem' : ∀ a b, b ∈ carrier → a ⇨ b ∈ carrier

namespace Sublocale

variable {ι : Sort*} {S T : Sublocale X} {s : Set X} {f : ι → X} {a b : X}

/-
**Sublocale.instSetLike** 是 Mathlib 中的一个实例，位于命名空间 `Sublocale`。
形式化陈述：instSetLike : SetLike (Sublocale X) X where coe x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSetLike : SetLike (Sublocale X) X where
  coe x := x.carrier
  coe_injective s1 s2 h := by cases s1; congr
/-
**Sublocale.** 是 Mathlib 中的一个实例，位于命名空间 `Sublocale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Sublocale X) := .ofSetLike (Sublocale X) X
/-
**Sublocale.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `Sublocale`。
形式化陈述：∀ {X : Type u_1} [inst : Order.Frame X] {S : Sublocale X} {a : X}, a ∈ S.c
arrier ↔ a ∈ S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_carrier : a ∈ S.carrier ↔ a ∈ S := .rfl
/-
**Sublocale.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sublocale`。
形式化陈述：∀ {X : Type u_1} [inst : Order.Frame X] {a : X} (carrier : Set X) (sInf_me
m' : ∀ s ⊆ carrier, sInf s ∈ carrier)   (himp_mem' : ∀ (a b : X), b ∈ carrier → 
a ⇨ b ∈ carrier),   a ∈ { carrier := carrier, sInf_mem' := sInf_mem', himp_mem' 
:= himp_mem' } ↔ a ∈ carrier
参数：carrier : Set X；sInf_mem' : ∀ s ⊆ carrier, sInf s ∈ carrier；himp_mem' : ∀ (a 
b : X), b ∈ carrier → a ⇨ b ∈ carrier。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_mk (carrier : Set X) (sInf_mem' himp_mem') :
    a ∈ mk carrier sInf_mem' himp_mem' ↔ a ∈ carrier := .rfl

@[simp, gcongr]
/-
**Sublocale.mk_le_mk** 是 Mathlib 中的一个引理，位于命名空间 `Sublocale`。
形式化陈述：mk_le_mk (carrier₁ carrier₂ : Set X) (sInf_mem'₁ sInf_mem'₂ himp_mem'₁ him
p_mem'₂) : mk carrier₁ sInf_mem'₁ himp_mem'₁ <= mk carrier₂ sInf_mem'₂ himp_mem'
₂ ↔ carrier₁ subseteq carrier₂
参数：carrier₁ carrier₂ : Set X；sInf_mem'₁ sInf_mem'₂ himp_mem'₁ himp_mem'₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mk_le_mk (carrier₁ carrier₂ : Set X) (sInf_mem'₁ sInf_mem'₂ himp_mem'₁ himp_mem'₂) :
    mk carrier₁ sInf_mem'₁ himp_mem'₁ ≤ mk carrier₂ sInf_mem'₂ himp_mem'₂ ↔ carrier₁ ⊆ carrier₂ :=
  .rfl

initialize_simps_projections Sublocale (carrier → coe, as_prefix coe)
/-
**Sublocale.ext** 是 Mathlib 中的一个定理，位于命名空间 `Sublocale`。
形式化陈述：∀ {X : Type u_1} [inst : Order.Frame X] {S T : Sublocale X}, (∀ (x : X), x
 ∈ S ↔ x ∈ T) → S = T
参数：∀ (x : X), x ∈ S ↔ x ∈ T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
@[ext] lemma ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h
/-
**Sublocale.sInf_mem** 是 Mathlib 中的一个引理，位于命名空间 `Sublocale`。
形式化陈述：sInf_mem (hs : s subseteq S) : sInf s in S
参数：hs : s subseteq S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sublocale.sInf_mem'`：∀ {X : Type u_2} [inst : Order.Frame X] (self : Sub
locale X), ∀ s ⊆ self.carrier, sInf s ∈ self.carrier
-/
lemma sInf_mem (hs : s ⊆ S) : sInf s ∈ S := S.sInf_mem' _ hs
/-
**Sublocale.iInf_mem** 是 Mathlib 中的一个引理，位于命名空间 `Sublocale`。
形式化陈述：iInf_mem (hf : forall i, f i in S) : ⨅ i, f i in S
参数：hf : forall i, f i in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sublocale.sInf_mem`：sInf_mem (hs : s subseteq S) : sInf s in S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma iInf_mem (hf : ∀ i, f i ∈ S) : ⨅ i, f i ∈ S := S.sInf_mem <| by simpa [range_subset_iff]
/-
**Sublocale.infClosed** 是 Mathlib 中的一个引理，位于命名空间 `Sublocale`。
形式化陈述：infClosed : InfClosed (S : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_pair`：∀ {α : Type u_1} [inst : CompleteLattice α] {a b : α}, sInf {
a, b} = a ⊓ b
· 使用引理 `Sublocale.sInf_mem`：sInf_mem (hs : s subseteq S) : sInf s in S
· 使用定理 `Set.pair_subset`：pair_subset (ha : a in s) (hb : b in s) : {a, b} subset
eq s
-/
lemma infClosed : InfClosed (S : Set X) := by
  rintro a ha b hb; rw [← sInf_pair]; exact S.sInf_mem (pair_subset ha hb)
/-
**Sublocale.inf_mem** 是 Mathlib 中的一个引理，位于命名空间 `Sublocale`。
形式化陈述：inf_mem (ha : a in S) (hb : b in S) : a ⊓ b in S
参数：ha : a in S；hb : b in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sublocale.infClosed`：infClosed : InfClosed (S : Set X)
-/
lemma inf_mem (ha : a ∈ S) (hb : b ∈ S) : a ⊓ b ∈ S := S.infClosed ha hb
/-
**Sublocale.top_mem** 是 Mathlib 中的一个引理，位于命名空间 `Sublocale`。
形式化陈述：top_mem : ⊤ in S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_empty`：∀ {α : Type u_1} [inst : CompleteLattice α], sInf ∅ = ⊤
· 使用引理 `Sublocale.sInf_mem`：sInf_mem (hs : s subseteq S) : sInf s in S
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
lemma top_mem : ⊤ ∈ S := by simpa using S.sInf_mem <| empty_subset _
/-
**Sublocale.himp_mem** 是 Mathlib 中的一个引理，位于命名空间 `Sublocale`。
形式化陈述：himp_mem (hb : b in S) : a ⇨ b in S
参数：hb : b in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sublocale.himp_mem'`：∀ {X : Type u_2} [inst : Order.Frame X] (self : Sub
locale X) (a b : X), b ∈ self.carrier → a ⇨ b ∈ self.carrier
-/
lemma himp_mem (hb : b ∈ S) : a ⇨ b ∈ S := S.himp_mem' _ _ hb
/-
**Sublocale.carrier.instSemilatticeInf** 是 Mathlib 中的一个定义，位于命名空间 `Sublocale.carr
ier`。
形式化陈述：{X : Type u_1} → [inst : Order.Frame X] → {S : Sublocale X} → SemilatticeI
nf ↥S
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Sublocale.inf_mem`：inf_mem (ha : a in S) (hb : b in S) : a ⊓ b in S
-/
instance carrier.instSemilatticeInf : SemilatticeInf S := Subtype.semilatticeInf fun _ _ ↦ inf_mem
/-
**Sublocale.carrier.instOrderTop** 是 Mathlib 中的一个定义，位于命名空间 `Sublocale.carrier`。
形式化陈述：{X : Type u_1} → [inst : Order.Frame X] → {S : Sublocale X} → OrderTop ↥S
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Sublocale.top_mem`：top_mem : ⊤ in S
-/
instance carrier.instOrderTop : OrderTop S := Subtype.orderTop top_mem
/-
**Sublocale.carrier.instHImp** 是 Mathlib 中的一个定义，位于命名空间 `Sublocale.carrier`。
形式化陈述：{X : Type u_1} → [inst : Order.Frame X] → {S : Sublocale X} → HImp ↥S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance carrier.instHImp : HImp S where himp a b := ⟨a ⇨ b, S.himp_mem b.2⟩
/-
**Sublocale.carrier.instInfSet** 是 Mathlib 中的一个定义，位于命名空间 `Sublocale.carrier`。
形式化陈述：{X : Type u_1} → [inst : Order.Frame X] → {S : Sublocale X} → InfSet ↥S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance carrier.instInfSet : InfSet S where
  sInf x := ⟨sInf (Subtype.val '' x), S.sInf_mem' _
    (by simp_rw [image_subset_iff, subset_def]; simp)⟩
/-
**Sublocale.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Sublocale`。
形式化陈述：∀ {X : Type u_1} [inst : Order.Frame X] {S : Sublocale X} (a b : ↥S), ↑(a 
⊓ b) = ↑a ⊓ ↑b
参数：a b : ↥S；a ⊓ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inf (a b : S) : (a ⊓ b).val = ↑a ⊓ ↑b := rfl
/-
**Sublocale.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Sublocale`。
形式化陈述：∀ {X : Type u_1} [inst : Order.Frame X] {S : Sublocale X} (s : Set ↥S), ↑(
sInf s) = sInf (Subtype.val '' s)
参数：s : Set ↥S；sInf s；Subtype.val '' s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_sInf (s : Set S) : (sInf s).val = sInf (Subtype.val '' s) := rfl
/-
**Sublocale.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Sublocale`。
形式化陈述：∀ {X : Type u_1} [inst : Order.Frame X] {ι : Sort u_2} {S : Sublocale X} (
f : ι → ↥S), ↑(⨅ i, f i) = ⨅ i, ↑(f i)
参数：f : ι → ↥S；⨅ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, norm_cast] lemma coe_iInf (f : ι → S) : (⨅ i, f i).val = ⨅ i, (f i).val := by
  simp [iInf, ← range_comp, Function.comp_def]
/-
**Sublocale.carrier.instCompleteLattice** 是 Mathlib 中的一个定义，位于命名空间 `Sublocale.car
rier`。
形式化陈述：{X : Type u_1} → [inst : Order.Frame X] → {S : Sublocale X} → CompleteLatt
ice ↥S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance carrier.instCompleteLattice : CompleteLattice S where
  __ := instSemilatticeInf
  __ := instOrderTop
  __ := completeLatticeOfInf S <| by simp [isGLB_iff_le_iff, lowerBounds, ← Subtype.coe_le_coe]
/-
**Sublocale.coe_himp** 是 Mathlib 中的一个定理，位于命名空间 `Sublocale`。
形式化陈述：∀ {X : Type u_1} [inst : Order.Frame X] {S : Sublocale X} (a b : ↥S), ↑(a 
⇨ b) = ↑a ⇨ ↑b
参数：a b : ↥S；a ⇨ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_himp (a b : S) : (a ⇨ b).val = a.val ⇨ b.val := rfl
/-
**Sublocale.carrier.instHeytingAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Sublocale.carr
ier`。
形式化陈述：{X : Type u_1} → [inst : Order.Frame X] → {S : Sublocale X} → HeytingAlgeb
ra ↥S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance carrier.instHeytingAlgebra : HeytingAlgebra S where
  le_himp_iff a b c := by simp [← Subtype.coe_le_coe, ← @Sublocale.coe_inf, himp]
  compl a := a ⇨ ⊥
  himp_bot _ := rfl
/-
**Sublocale.carrier.instFrame** 是 Mathlib 中的一个定义，位于命名空间 `Sublocale.carrier`。
形式化陈述：{X : Type u_1} → [inst : Order.Frame X] → {S : Sublocale X} → Order.Frame 
↥S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance carrier.instFrame : Order.Frame S where
  __ := carrier.instHeytingAlgebra
  __ := carrier.instCompleteLattice

set_option backward.privateInPublic true in
/-- See `Sublocale.restrict` for the public-facing version. -/
/-
**Sublocale.restrictAux** 是 Mathlib 中的一个定义，位于命名空间 `Sublocale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `Sublocale.restrict` for the public-facing version.
-/
private def restrictAux (S : Sublocale X) (a : X) : S := sInf {s : S | a ≤ s}
/-
**Sublocale.le_restrictAux** 是 Mathlib 中的一个引理，位于命名空间 `Sublocale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma le_restrictAux : a ≤ S.restrictAux a := by simp +contextual [restrictAux]

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/-- See `Sublocale.giRestrict` for the public-facing version. -/
/-
**Sublocale.giAux** 是 Mathlib 中的一个定义，位于命名空间 `Sublocale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `Sublocale.giRestrict` for the public-facing version.
-/
private def giAux (S : Sublocale X) : GaloisInsertion S.restrictAux Subtype.val where
  choice x hx := ⟨x, by
    rw [le_antisymm le_restrictAux hx]
    exact S.sInf_mem <| by simp +contextual [Set.subset_def]⟩
  gc a b := by
    constructor <;> intro h
    · exact le_trans (by simp +contextual [restrictAux]) h
    · exact sInf_le (by simp [h])
  le_l_u x := by simp [restrictAux]
  choice_eq a h := by simp [le_antisymm_iff, restrictAux, sInf_le]

/-- The restriction from a locale X into the sublocale S. -/
/-
**Sublocale.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Sublocale`。
形式化陈述：restrict (S : Sublocale X) : FrameHom X S where toFun x
参数：S : Sublocale X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction from a locale X into the sublocale S.
-/
def restrict (S : Sublocale X) : FrameHom X S where
  toFun x := sInf {s : S | x ≤ s}
  map_inf' a b := by
    change Sublocale.restrictAux S (a ⊓ b) = Sublocale.restrictAux S a ⊓ Sublocale.restrictAux S b
    refine eq_of_forall_ge_iff (fun s ↦ Iff.symm ?_)
    calc
      _ ↔ S.restrictAux a ≤ S.restrictAux b ⇨ s := by simp
      _ ↔ S.restrictAux b ≤ a ⇨ s := by rw [S.giAux.gc.le_iff_le, @le_himp_comm, coe_himp]
      _ ↔ b ≤ a ⇨ s := by
        set c : S := ⟨a ⇨ s, S.himp_mem s.coe_prop⟩
        change Sublocale.restrictAux S b ≤ c.val ↔ b ≤ c
        rw [S.giAux.u_le_u_iff, S.giAux.gc.le_iff_le]
      _ ↔ S.restrictAux (a ⊓ b) ≤ s := by simp [inf_comm, S.giAux.gc.le_iff_le]
  map_sSup' s := by
    change Sublocale.restrictAux S (sSup s) = _
    rw [S.giAux.gc.l_sSup, sSup_image]
    rfl
  map_top' := by
    refine le_antisymm le_top ?_
    change _ ≤ restrictAux S ⊤
    rw [← Subtype.coe_le_coe, S.giAux.gc.u_top]
    simp [restrictAux, sInf]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The restriction corresponding to a sublocale forms a Galois insertion with the forgetful map
from the sublocale to the original locale. -/
/-
**Sublocale.giRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Sublocale`。
形式化陈述：giRestrict (S : Sublocale X) : GaloisInsertion S.restrict Subtype.val
参数：S : Sublocale X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction corresponding to a sublocale forms a Galois insertion with the f
orgetful map
from the sublocale to the original locale.
-/
def giRestrict (S : Sublocale X) : GaloisInsertion S.restrict Subtype.val := S.giAux
/-
**Sublocale.restrict_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Sublocale`。
形式化陈述：∀ {X : Type u_1} [inst : Order.Frame X] {S : Sublocale X} {a : X} (ha : a 
∈ S), S.restrict a = ⟨a, ha⟩
参数：ha : a ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b
-/
@[simp] lemma restrict_of_mem (ha : a ∈ S) : S.restrict a = ⟨a, ha⟩ := S.giRestrict.l_u_eq ⟨a, ha⟩

/-- The restriction from the locale X into a sublocale is a nucleus. -/
@[simps]
/-
**Sublocale.toNucleus** 是 Mathlib 中的一个定义，位于命名空间 `Sublocale`。
形式化陈述：toNucleus (S : Sublocale X) : Nucleus X where toFun x
参数：S : Sublocale X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction from the locale X into a sublocale is a nucleus.
-/
def toNucleus (S : Sublocale X) : Nucleus X where
  toFun x := S.restrict x
  map_inf' _ _ := by simp [S.giRestrict.gc.u_inf]
  idempotent' _ := by rw [S.giRestrict.gc.l_u_l_eq_l]
  le_apply' _ := S.giRestrict.gc.le_u_l _
/-
**Sublocale.range_toNucleus** 是 Mathlib 中的一个定理，位于命名空间 `Sublocale`。
形式化陈述：∀ {X : Type u_1} [inst : Order.Frame X] {S : Sublocale X}, Set.range ⇑S.to
Nucleus = ↑S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sublocale.toNucleus_apply`：∀ {X : Type u_1} [inst : Order.Frame X] (S : 
Sublocale X) (x : X), S.toNucleus x = ↑(S.restrict x)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Sublocale.restrict_of_mem`：∀ {X : Type u_1} [inst : Order.Frame X] {S : 
Sublocale X} {a : X} (ha : a ∈ S), S.restrict a = ⟨a, ha⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma range_toNucleus : range S.toNucleus = S := by
  ext x
  constructor
  · simp +contextual [eq_comm]
  · intro hx
    exact ⟨x, by simp_all⟩
/-
**Sublocale.toNucleus_le_toNucleus** 是 Mathlib 中的一个定理，位于命名空间 `Sublocale`。
形式化陈述：∀ {X : Type u_1} [inst : Order.Frame X] {S T : Sublocale X}, S.toNucleus ≤
 T.toNucleus ↔ T ≤ S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Sublocale.range_toNucleus`：∀ {X : Type u_1} [inst : Order.Frame X] {S : 
Sublocale X}, Set.range ⇑S.toNucleus = ↑S
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toNucleus_le_toNucleus : S.toNucleus ≤ T.toNucleus ↔ T ≤ S := by
  simp [← Nucleus.range_subset_range]

end Sublocale

namespace Nucleus

/-- The range of a nucleus is a sublocale. -/
@[simps]
/-
**Nucleus.toSublocale** 是 Mathlib 中的一个定义，位于命名空间 `Nucleus`。
形式化陈述：toSublocale (n : Nucleus X) : Sublocale X where carrier
参数：n : Nucleus X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a nucleus is a sublocale.
-/
def toSublocale (n : Nucleus X) : Sublocale X where
  carrier := range n
  sInf_mem' a h := by
    rw [mem_range]
    refine le_antisymm (le_sInf_iff.mpr (fun b h1 ↦ ?_)) le_apply
    simp_rw [subset_def, mem_range] at h
    rw [← h b h1]
    exact n.monotone (sInf_le h1)
  himp_mem' a b h := by rw [mem_range, ← h, map_himp_apply] at *

@[simp]
/-
**Nucleus.mem_toSublocale** 是 Mathlib 中的一个引理，位于命名空间 `Nucleus`。
形式化陈述：mem_toSublocale {n : Nucleus X} {x : X} : x in n.toSublocale ↔ exists y, n
 y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_toSublocale {n : Nucleus X} {x : X} : x ∈ n.toSublocale ↔ ∃ y, n y = x := .rfl
/-
**Nucleus.toSublocale_le_toSublocale** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : Order.Frame X] {m n : Nucleus X}, m.toSublocale ≤
 n.toSublocale ↔ n ≤ m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nucleus.coe_toSublocale`：∀ {X : Type u_1} [inst : Order.Frame X] (n : Nu
cleus X), ↑n.toSublocale = Set.range ⇑n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp, gcongr] lemma toSublocale_le_toSublocale {m n : Nucleus X} :
    m.toSublocale ≤ n.toSublocale ↔ n ≤ m := by simp [← SetLike.coe_subset_coe]
/-
**Nucleus.restrict_toSublocale** 是 Mathlib 中的一个定理，位于命名空间 `Nucleus`。
形式化陈述：∀ {X : Type u_1} [inst : Order.Frame X] (n : Nucleus X) (x : X), n.toSublo
cale.restrict x = ⟨n x, ⋯⟩
参数：n : Nucleus X；x : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
s : Set β} {f : β → α}, sInf (f '' s) = ⨅ a ∈ s, f a
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…
· 使用引理 `Nucleus.le_apply`：le_apply : x <= n x
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nucleus.idempotent`：∀ {X : Type u_1} [inst : SemilatticeInf X] {n : Nucl
eus X} (x : X), n (n x) = n x
· 使用引理 `Nucleus.monotone`：monotone : Monotone n
-/
@[simp] lemma restrict_toSublocale (n : Nucleus X) (x : X) :
    n.toSublocale.restrict x = ⟨n x, x, rfl⟩ := by
  ext
  simpa [Sublocale.restrict, sInf_image, le_antisymm_iff (a := iInf _)] using
    ⟨iInf₂_le_of_le ⟨n x, x, rfl⟩ n.le_apply le_rfl, fun y hxy ↦ by simpa using n.monotone hxy⟩

end Nucleus

set_option backward.isDefEq.respectTransparency false in
/-- The nuclei on a frame corresponds exactly to the sublocales on this frame.
The sublocales are ordered dually to the nuclei. -/
/-
**nucleusIsoSublocale** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nucleusIsoSublocale : (Nucleus X)ᵒᵈ ≃o Sublocale X where toFun n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nuclei on a frame corresponds exactly to the sublocales on this frame.
The sublocales are ordered dually to the nuclei.
-/
def nucleusIsoSublocale : (Nucleus X)ᵒᵈ ≃o Sublocale X where
  toFun n := n.ofDual.toSublocale
  invFun s := .toDual s.toNucleus
  left_inv := by simp [Function.LeftInverse, Nucleus.ext_iff]
  right_inv S := by ext x; simpa using ⟨by simp +contextual [eq_comm], fun hx ↦ ⟨x, by simp [hx]⟩⟩
  map_rel_iff' := by simp
/-
**nucleusIsoSublocale.eq_toSublocale** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nucleusIsoSublocale.eq_toSublocale : Nucleus.toSublocale = @nucleusIsoSubl
ocale X _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nucleusIsoSublocale.eq_toSublocale : Nucleus.toSublocale = @nucleusIsoSublocale X _ := rfl
/-
**nucleusIsoSublocale.symm_eq_toNucleus** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nucleusIsoSublocale.symm_eq_toNucleus : Sublocale.toNucleus = (@nucleusIso
Sublocale X _).symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nucleusIsoSublocale.symm_eq_toNucleus :
  Sublocale.toNucleus = (@nucleusIsoSublocale X _).symm := rfl
/-
**Sublocale.instCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sublocale.instCompleteLattice : CompleteLattice (Sublocale X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Sublocale.instCompleteLattice : CompleteLattice (Sublocale X) :=
  nucleusIsoSublocale.toGaloisInsertion.liftCompleteLattice

set_option backward.isDefEq.respectTransparency false in
/-
**Sublocale.instCoframe** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sublocale.instCoframe : Order.Coframe (Sublocale X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Sublocale.instCoframe : Order.Coframe (Sublocale X) := .ofMinimalAxioms {
  iInf_sup_le_sup_sInf a s := by simp [← toNucleus_le_toNucleus,
    nucleusIsoSublocale.symm_eq_toNucleus, nucleusIsoSublocale.symm.map_sup,
    nucleusIsoSublocale.symm.map_sInf, sup_iInf_eq, nucleusIsoSublocale.symm.map_iInf] }
