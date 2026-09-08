/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.Topology.Maps.Proper.Basic

/-! # Restriction of a closed compact set in a product space to a set of coordinates

We show that the image of a compact closed set `s` in a product `Π i : ι, α i` by
the restriction to a subset of coordinates `S : Set ι` is a closed set.

The idea of the proof is to use `isClosedMap_snd_of_compactSpace`, which is the fact that if
`X` is a compact topological space, then `Prod.snd : X × Y → Y` is a closed map.

We remark that `s` is included in the set `Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s`, and we build
a homeomorphism
`Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s ≃ₜ Sᶜ.domRestrict '' s × Π i : S, α i`.
`Sᶜ.domRestrict '' s` is a compact space since `s` is compact, and the lemma applies,
with `X = Sᶜ.domRestrict '' s` and `Y = Π i : S, α i`.

-/

@[expose] public section

open Set

variable {ι : Type*} {α : ι → Type*} {s : Set (Π i, α i)} {i : ι} {S : Set ι}

namespace Topology

open scoped Classical in
/-- Given a set in a product space `s : Set (Π j, α j)` and a set of coordinates `S : Set ι`,
`Sᶜ.domRestrict '' s × (Π i : S, α i)` is the set of functions that coincide with an element of `s`
on `Sᶜ` and are arbitrary on `S`.
`reorderRestrictProd` sends a term of that type to `Π j, α j` by looking for the value at `j`
in one part of the product or the other depending on whether `j` is in `S` or not. -/
/-
**Topology.reorderRestrictProd** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
形式化陈述：reorderRestrictProd (S : Set ι) (s : Set (Π j, α j)) (p : Sᶜ.domRestrict '
' s × (Π i : S, α i)) : Π j, α j
参数：S : Set ι；s : Set (Π j, α j)；p : Sᶜ.domRestrict '' s × (Π i : S, α i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a set in a product space `s : Set (Π j, α j)` and a set of coordinates `S 
: Set ι`,
`Sᶜ.domRestrict '' s × (Π i : S, α i)` is the set of functions that coincide wit
h an element of `s`
on `Sᶜ` and are arbitrary on `S`.
`reorderRestrictProd` sends a term of that type to `Π j, α j` by looking for the
 value at `j`
in one part of the product or the other depending on whether `j` is in `S` or no
t.
-/
noncomputable def reorderRestrictProd (S : Set ι) (s : Set (Π j, α j))
    (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) :
    Π j, α j :=
  fun j ↦ if h : j ∈ S
    then (p.2 : Π j : ↑(S : Set ι), α j) ⟨j, h⟩
    else (p.1 : Π j : ↑(Sᶜ : Set ι), α j) ⟨j, h⟩

@[simp]
/-
**Topology.reorderRestrictProd_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：reorderRestrictProd_of_mem (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) (j :
 S) : reorderRestrictProd S s p j = (p.2 : Π j : ↑(S : Set ι), α j) j
参数：p : Sᶜ.domRestrict '' s × (Π i : S, α i)；j : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reorderRestrictProd_of_mem (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) (j : S) :
    reorderRestrictProd S s p j = (p.2 : Π j : ↑(S : Set ι), α j) j := by
  have hj : ↑j ∈ S := j.prop
  simp [reorderRestrictProd, hj]

@[simp]
/-
**Topology.reorderRestrictProd_of_compl** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：reorderRestrictProd_of_compl (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) (j
 : (Sᶜ : Set ι)) : reorderRestrictProd S s p j = (p.1 : Π j : ↑(Sᶜ : Set ι), α j
) j
参数：p : Sᶜ.domRestrict '' s × (Π i : S, α i)；j : (Sᶜ : Set ι)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reorderRestrictProd_of_compl (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) (j : (Sᶜ : Set ι)) :
    reorderRestrictProd S s p j = (p.1 : Π j : ↑(Sᶜ : Set ι), α j) j := by
  have hj : ↑j ∉ S := j.prop
  simp [reorderRestrictProd, hj]

@[simp]
/-
**Topology.restrict_compl_reorderRestrictProd** 是 Mathlib 中的一个引理，位于命名空间 `Topolog
y`。
形式化陈述：restrict_compl_reorderRestrictProd (p : Sᶜ.domRestrict '' s × (Π i : S, α 
i)) : Sᶜ.domRestrict (reorderRestrictProd S s p) = p.1
参数：p : Sᶜ.domRestrict '' s × (Π i : S, α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.reorderRestrictProd_of_compl`：reorderRestrictProd_of_compl (p :
 Sᶜ.domRestrict '' s × (Π i : S, α i)) (j : (Sᶜ : Set ι)) : reorderRestrictProd 
S s p j = (p.1 : Π j : ↑(Sᶜ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_compl_reorderRestrictProd (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) :
    Sᶜ.domRestrict (reorderRestrictProd S s p) = p.1 := by ext; simp
/-
**Topology.continuous_reorderRestrictProd** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：continuous_reorderRestrictProd [forall i, TopologicalSpace (α i)] : Contin
uous (reorderRestrictProd S s)
参数：α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
-/
lemma continuous_reorderRestrictProd [∀ i, TopologicalSpace (α i)] :
    Continuous (reorderRestrictProd S s) := by
  refine continuous_pi fun j ↦ ?_
  simp only [reorderRestrictProd]
  split_ifs with h
  · fun_prop
  · exact ((continuous_apply _).comp continuous_subtype_val).comp continuous_fst
/-
**Topology.reorderRestrictProd_mem_preimage_image_restrict** 是 Mathlib 中的一个引理，位于
命名空间 `Topology`。
形式化陈述：reorderRestrictProd_mem_preimage_image_restrict (p : Sᶜ.domRestrict '' s ×
 (Π i : S, α i)) : reorderRestrictProd S s p in Sᶜ.domRestrict ⁻¹' Sᶜ.domRestric
t '' s
参数：p : Sᶜ.domRestrict '' s × (Π i : S, α i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.restrict_compl_reorderRestrictProd`：restrict_compl_reorderRestr
ictProd (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) : Sᶜ.domRestrict (reorderRest
rictProd S s p) = p.1
-/
lemma reorderRestrictProd_mem_preimage_image_restrict (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) :
    reorderRestrictProd S s p ∈ Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s := by
  obtain ⟨y, hy_mem_s, hy_eq⟩ := p.1.2
  exact ⟨y, hy_mem_s, hy_eq.trans (restrict_compl_reorderRestrictProd p).symm⟩

@[simp]
/-
**Topology.reorderRestrictProd_restrict_compl** 是 Mathlib 中的一个引理，位于命名空间 `Topolog
y`。
形式化陈述：reorderRestrictProd_restrict_compl (x : Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict 
'' s) : reorderRestrictProd S s ⟨⟨Sᶜ.domRestrict x, x.2⟩, fun i => (x : Π j, α j
) i⟩ = (x : Π j, α j)
参数：x : Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reorderRestrictProd_restrict_compl (x : Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s) :
    reorderRestrictProd S s ⟨⟨Sᶜ.domRestrict x, x.2⟩, fun i ↦ (x : Π j, α j) i⟩ =
      (x : Π j, α j) := by
  ext; simp [reorderRestrictProd]

/-- Homeomorphism between the set of functions that coincide with a given set of functions away
from a given set `S`, and dependent functions away from `S` times any value on `S`. -/
noncomputable
/-
**Topology._root_.Homeomorph.preimageImageRestrict** 是 Mathlib 中的一个定义，位于命名空间 `To
pology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.Homeomorph.preimageImageRestrict (α : ι → Type*) [∀ i, TopologicalSpace (α i)]
    (S : Set ι) (s : Set (Π j, α j)) :
    Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s ≃ₜ Sᶜ.domRestrict '' s × (Π i : S, α i) where
  toFun x := ⟨⟨Sᶜ.domRestrict x, x.2⟩, fun i ↦ (x : Π j, α j) i⟩
  invFun p := ⟨reorderRestrictProd S s p, reorderRestrictProd_mem_preimage_image_restrict p⟩
  left_inv x := by ext; simp
  right_inv p := by ext <;> simp
  continuous_toFun := by
    refine (Continuous.subtype_mk (by fun_prop) _).prodMk ?_
    rw [continuous_pi_iff]
    exact fun _ ↦ (continuous_apply _).comp continuous_subtype_val
  continuous_invFun := continuous_reorderRestrictProd.subtype_mk _

set_option backward.isDefEq.respectTransparency false in
/-- The image by `preimageImageRestrict α S s` of `s` seen as a set of
`Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s` is a set of
`Sᶜ.domRestrict '' s × (Π i : S, α i)`, and the image of that set by `Prod.snd` is
`S.domRestrict '' s`.

Used in `IsCompact.isClosed_image_restrict` to prove that the restriction of a compact closed set
in a product space to a set of coordinates is closed. -/
/-
**Topology.image_snd_preimageImageRestrict** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：image_snd_preimageImageRestrict [forall i, TopologicalSpace (α i)] : Prod.
snd '' (Homeomorph.preimageImageRestrict α S s '' ((fun (x : Sᶜ.domRestrict ⁻¹' 
Sᶜ.domRestrict '' s) => (x : Π j, α j)) ⁻¹' s)) = S.domRestrict '' s
参数：α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
The image by `preimageImageRestrict α S s` of `s` seen as a set of
`Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s` is a set of
`Sᶜ.domRestrict '' s × (Π i : S, α i)`, and the image of that set by `Prod.snd` 
is
`S.domRestrict '' s`.

Used in `IsCompact.isClosed_image_restrict` to prove that the restriction of a c
ompact closed set
in a product space to a set of coordinates is closed.
-/
lemma image_snd_preimageImageRestrict [∀ i, TopologicalSpace (α i)] :
    Prod.snd '' (Homeomorph.preimageImageRestrict α S s ''
        ((fun (x : Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s) ↦ (x : Π j, α j)) ⁻¹' s))
      = S.domRestrict '' s := by
  ext x
  simp only [Homeomorph.preimageImageRestrict, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk,
    mem_image, mem_preimage, Subtype.exists, exists_and_left, Prod.exists, Prod.mk.injEq,
    exists_and_right, exists_eq_right, Subtype.mk.injEq, exists_prop]
  constructor
  · rintro ⟨y, _, z, hz_mem, _, hzx⟩
    exact ⟨z, hz_mem, hzx⟩
  · rintro ⟨z, hz_mem, hzx⟩
    exact ⟨Sᶜ.domRestrict z, mem_image_of_mem Sᶜ.domRestrict hz_mem, z, hz_mem,
      ⟨⟨⟨z, hz_mem, rfl⟩, rfl⟩, hzx⟩⟩

end Topology

section IsClosed

variable [∀ i, TopologicalSpace (α i)]

/-- The restriction of a compact closed set in a product space to a set of coordinates is closed. -/
/-
**IsCompact.isClosed_image_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.isClosed_image_restrict (S : Set ι) (hs_compact : IsCompact s) (
hs_closed : IsClosed s) : IsClosed (S.domRestrict '' s)
参数：S : Set ι；hs_compact : IsCompact s；hs_closed : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.image_snd_preimageImageRestrict`：image_snd_preimageImageRestric
t [forall i, TopologicalSpace (α i)] : Prod.snd '' (Homeomorph.preimageImageRest
rict α S s '' ((fun (x : Sᶜ.do…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用引理 `Pi.continuous_domRestrict`：Pi.continuous_domRestrict (S : Set ι) : Conti
nuous (S.domRestrict : (forall i : ι, A i) -> (forall i : S, A i))
· 使用定理 `isClosedMap_snd_of_compactSpace`：isClosedMap_snd_of_compactSpace [Compac
tSpace X] : IsClosedMap (Prod.snd : X × Y -> Y)
· 使用定理 `Homeomorph.isClosed_image`：isClosed_image (h : X ≃ₜ Y) {s : Set X} : IsC
losed (h '' s) ↔ IsClosed s
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)

--- 原说明 ---
The restriction of a compact closed set in a product space to a set of coordinat
es is closed.
-/
theorem IsCompact.isClosed_image_restrict (S : Set ι)
    (hs_compact : IsCompact s) (hs_closed : IsClosed s) :
    IsClosed (S.domRestrict '' s) := by
  rw [← Topology.image_snd_preimageImageRestrict]
  have : CompactSpace (Sᶜ.domRestrict '' s) :=
    isCompact_iff_compactSpace.mp (hs_compact.image (Pi.continuous_domRestrict _))
  refine isClosedMap_snd_of_compactSpace _ ?_
  rw [Homeomorph.isClosed_image]
  exact hs_closed.preimage continuous_subtype_val
/-
**isClosedMap_restrict_of_compactSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosedMap_restrict_of_compactSpace [forall i, CompactSpace (α i)] : IsCl
osedMap (S.domRestrict : (Π i, α i) -> _)
参数：α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `isClosedMap_fst_of_compactSpace`：isClosedMap_fst_of_compactSpace [Compac
tSpace Y] : IsClosedMap (Prod.fst : X × Y -> X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Homeomorph.isClosed_image`：isClosed_image (h : X ≃ₜ Y) {s : Set X} : IsC
losed (h '' s) ↔ IsClosed s
-/
lemma isClosedMap_restrict_of_compactSpace [∀ i, CompactSpace (α i)] :
    IsClosedMap (S.domRestrict : (Π i, α i) → _) := fun s hs ↦ by
  classical
  have : S.domRestrict (π := α) = Prod.fst ∘ (Homeomorph.piEquivPiSubtypeProd (· ∈ S) α) := rfl
  rw [this, image_comp]
  exact isClosedMap_fst_of_compactSpace _ <| (Homeomorph.isClosed_image _).mpr hs
/-
**IsClosed.isClosed_image_eval** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.isClosed_image_eval (i : ι) (hs_compact : IsCompact s) (hs_closed
 : IsClosed s) : IsClosed ((fun x => x i) '' s)
参数：i : ι；hs_compact : IsCompact s；hs_closed : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isClosed_image_restrict`：IsCompact.isClosed_image_restrict (S 
: Set ι) (hs_compact : IsCompact s) (hs_closed : IsClosed s) : IsClosed (S.domRe
strict '' s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Homeomorph.isClosed_image`：isClosed_image (h : X ≃ₜ Y) {s : Set X} : IsC
losed (h '' s) ↔ IsClosed s
-/
lemma IsClosed.isClosed_image_eval (i : ι)
    (hs_compact : IsCompact s) (hs_closed : IsClosed s) :
    IsClosed ((fun x ↦ x i) '' s) := by
  suffices IsClosed (Set.domRestrict {i} '' s) by
    have : Homeomorph.piUnique _ ∘ Set.domRestrict {i} = fun (x : Π j, α j) ↦ x i := rfl
    rwa [← this, image_comp, Homeomorph.isClosed_image (Homeomorph.piUnique _)]
  exact hs_compact.isClosed_image_restrict {i} hs_closed

end IsClosed

